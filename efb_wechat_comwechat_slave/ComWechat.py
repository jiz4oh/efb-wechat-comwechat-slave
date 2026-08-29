import logging, tempfile
import time
import threading
from lxml import etree
from traceback import print_exc
from pydub import AudioSegment
import os
import base64
import contextlib
from pathlib import Path
from xml.sax.saxutils import escape

import re
import json
import secrets
from ehforwarderbot.chat import SystemChat, PrivateChat , SystemChatMember, ChatMember, SelfChatMember
import hashlib
from typing import Tuple, Optional, Collection, BinaryIO, Dict, Any , Union , List
from datetime import datetime
from cachetools import TTLCache

from ehforwarderbot import MsgType, Chat, Message, Status, coordinator
from wechatrobot import WeChatRobot
from wechatrobot import ChatRoomData_pb2 as ChatRoom

from . import __version__ as version

from ehforwarderbot.channel import SlaveChannel
from ehforwarderbot.types import MessageID, ChatID, InstanceID
from ehforwarderbot import utils as efb_utils
from ehforwarderbot.exceptions import EFBException, EFBChatNotFound, EFBMessageError, EFBOperationNotSupported
from ehforwarderbot.message import MessageCommand, MessageCommands
from ehforwarderbot.status import MessageRemoval, ChatUpdates, MemberUpdates

from .ChatMgr import ChatMgr
from .CustomTypes import EFBGroupChat, EFBPrivateChat, EFBGroupMember, EFBSystemUser
from .MsgDeco import qutoed_text
from .MsgProcess import MsgProcess, MsgWrapper
from .Utils import (
    download_file,
    load_config,
    load_temp_file_to_local,
    resolve_hooked_wechat_image_path,
    WC_EMOTICON_CONVERSION,
    dump_message_ids,
    load_message_ids,
)
from .db import DatabaseManager
from .dbkey import DbKeyManager

from rich.console import Console
from rich import print as rprint
from io import BytesIO
from PIL import Image
from typing import Callable

VOICE_DATABASE_NAMES = ("MediaMSG0.db", "MediaMSG1.db", "MediaMSG2.db")
MEDIA_DELETE_TYPES = {"image", "video", "file", "share"}
MEDIA_RETRY_TYPES = {"image", "video", "file", "share"}
MEDIA_RETRY_FIELDS = (
    "type",
    "message",
    "msgid",
    "svrid",
    "sender",
    "self",
    "wxid",
    "extrainfo",
    "thumb_path",
)

class ComWeChatChannel(SlaveChannel):
    channel_name : str = "ComWechatChannel"
    channel_emoji : str = "💻"
    channel_id : str = "honus.comwechat"
    file_lock_key = "__file_op__"

    bot : WeChatRobot = None
    config : Dict = {}
    delete_media_after_send: bool = True
    friends : EFBPrivateChat = []
    groups : EFBGroupChat    = []

    contacts : Dict[str, Dict[str, str]] = {}  # {wxid: {nickname: str, remark: str}}
    group_members : Dict = {}       # {"group_id" : { "wxID" : "displayName"}}

    time_out : int = int(os.getenv("EFB_MEDIA_TIMEOUT", "300"))
    cache =  TTLCache(maxsize=200, ttl= time_out)  # 缓存发送过的消息ID
    file_msg : Dict = {}                           # 存储待修改的文件类消息 {path : msg}
    delete_file : Dict = {}                        # 存储待删除的消息 {path : time}
    forward_pattern = r"ehforwarderbot:\/\/([^/]+)\/forward\/(\d+)"

    __version__ = version.__version__
    logger: logging.Logger = logging.getLogger("comwechat")
    logger.setLevel(logging.DEBUG)

    #MsgType.Voice
    supported_message_types = {MsgType.Text, MsgType.Sticker, MsgType.Image , MsgType.Link , MsgType.File , MsgType.Video , MsgType.Animation, MsgType.Voice}
    self_update_lock = threading.Lock()
    contact_update_lock = threading.Lock()

    def __init__(self, instance_id: InstanceID = None):
        super().__init__(instance_id=instance_id)
        self.logger.info("ComWeChat Slave Channel initialized.")
        self.logger.info("Version: %s" % self.__version__)
        config_path = Path(efb_utils.get_config_path(self.channel_id))
        self.config = load_config(config_path)
        self.direct_transfer = "direct_transfer" in self.config
        self.delete_media_after_send = self.config.get("delete_media_after_send", True) is True
        cache_path = Path(self.config.get("media_retry_cache_path", "media_retry_cache.json"))
        self.media_retry_cache_path = cache_path if cache_path.is_absolute() else config_path.parent / cache_path
        self.media_retry_cache_lock = threading.RLock()
        self.media_retry_cache = TTLCache(maxsize=200, ttl=max(self.time_out, 1))
        self._load_media_retry_cache()
        self.mark_as_read_enabled = self.config.get("auto_mark_as_read", True) is True
        try:
            self.mark_as_read_delay = max(float(self.config.get("mark_as_read_delay", 10)), 0)
        except (TypeError, ValueError):
            self.mark_as_read_delay = 10
        self.mark_as_read_timers: Dict[str, threading.Timer] = {}
        self.mark_as_read_lock = threading.RLock()
        self.db: DatabaseManager = DatabaseManager(self)
        self.bot = WeChatRobot()

        # Mechanism for waiting for send confirmation
        self.sent_msgs: Dict[Any, threading.Event] = {}
        self.sent_msg_results: Dict[Any, MessageID] = {}
        self.pending_lock = threading.Lock()
        self.revoke_message_ids = TTLCache(maxsize=200, ttl=max(self.time_out, 1))
        self._file_locks: Dict[ChatID, threading.Lock] = {}
        self._file_locks_lock = threading.Lock()
        self.send_timeout = self.config.get("send_timeout", 5)

        self.wxid = None
        self.base_path = self.config["base_path"] if "base_path" in self.config else self.bot.get_base_path()
        self.load()
        self.dir = self.config["dir"]
        if not self.dir.endswith(os.path.sep):
            self.dir += os.path.sep
        self.dbkey: DbKeyManager = DbKeyManager(self)
        self._voice_db_names: Optional[List[str]] = None
        ChatMgr.slave_channel = self
        self.user_auth_chat = ChatMgr.build_efb_chat_as_system_user(EFBSystemUser(
            uid = self.channel_name,
            name = self.channel_name,
        ))

        def update_contacts_wrapper(func):
            def wrapper(*args, **kwargs):
                if not self.friends and not self.groups:
                    self.get_me()
                    self.GetContactListBySql()
                return func(*args, **kwargs)
            return wrapper

        @self.bot.on("sent_msg")
        def on_sent_msg(msg: Dict):
            """Callback for messages sent by the bot (potentially from other devices or API)."""
            self.logger.debug(f"on_sent_msg received: {msg}")
            sender: str = msg.get("sender")
            msgid = msg.get("msgid")
            message_content = msg.get("message")
            filepath = msg.get("filepath")

            if not sender or not msgid:
                self.logger.warning("on_sent_msg missing sender or msgid.")
                return

            if msgid in self.cache:
                self.logger.warning("self msg due to bug from upstream.")
                return

            key = None
            with self.pending_lock:
                if message_content:
                    potential_key_text = (sender, message_content)
                    if potential_key_text in self.sent_msgs:
                        key = potential_key_text
                    if key is None:
                        try:
                            quote = etree.fromstring(message_content.encode())
                            potential_key_quote = (
                                sender,
                                quote.findtext(".//appmsg/title"),
                                quote.findtext(".//refermsg/svrid"),
                            )
                            if potential_key_quote in self.sent_msgs:
                                key = potential_key_quote
                        except (TypeError, ValueError, etree.XMLSyntaxError):
                            pass

                if filepath:
                    potential_key_file = (sender, None, self.file_lock_key)
                    if potential_key_file in self.sent_msgs:
                        key = potential_key_file
                        self.logger.debug(f"Found pending file operation for key: {key}")

                if key and key in self.sent_msgs:
                    event = self.sent_msgs[key]
                    self.sent_msg_results[key] = MessageID(str(msgid))
                    event.set()
                    self.logger.debug(f"Matched sent message {key} with msgid {msgid}. Signaled event.")
                else:
                    self.logger.warning(f"No pending message found matching sender {sender}, content/filepath.")

        @self.bot.on("self_msg")
        @update_contacts_wrapper
        def on_self_msg(msg : Dict):
            self.logger.debug(f"self_msg:{msg}")
            sender = msg["sender"]

            name = self.get_name_by_wxid(sender)

            if "@chatroom" in sender:
                chat = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
                    uid = sender,
                    name = name,
                ))
                author = chat.self
                self.extract_alias(msg)
            else:
                chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                    uid = sender,
                    name = name,
                ))
                if sender.startswith('gh_'):
                    chat.vendor_specific = {'is_mp' : True}
                author = chat.self

            self.handle_msg(msg , author , chat)

        @self.bot.on("friend_msg")
        @update_contacts_wrapper
        def on_friend_msg(msg : Dict):
            self.logger.debug(f"friend_msg:{msg}")

            sender = msg['sender']

            if msg["type"] == "eventnotify":
                return

            name = self.get_name_by_wxid(sender)

            chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                    uid= sender,
                    name= name,
            ))
            try:
                self.get_chat(sender)
            except EFBChatNotFound:
                self.friends.append(chat)
                coordinator.send_status(ChatUpdates(channel=self, new_chats=[sender]))

            if sender.startswith('gh_'):
                chat.vendor_specific = {'is_mp' : True}
                self.logger.debug(f'modified_chat:{chat}')
            author = chat.other
            self.handle_msg(msg, author, chat)

        @self.bot.on("group_msg")
        @update_contacts_wrapper
        def on_group_msg(msg : Dict):
            self.logger.debug(f"group_msg:{msg}")
            sender = msg["sender"]
            wxid  =  msg["wxid"]

            chatname = self.get_name_by_wxid(sender)

            chat = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
                uid = sender,
                name = chatname,
            ))

            try:
                self.get_chat(sender)
            except EFBChatNotFound:
                self.groups.append(chat)
                coordinator.send_status(ChatUpdates(channel=self, new_chats=[sender]))

            self.extract_alias(msg)
            member = self.get_group_member(sender, wxid)

            author = ChatMgr.build_efb_chat_as_member(chat, member)
            self.handle_msg(msg, author, chat)

            if msg["type"] == "sysmsg" and msg.get("message", None):
                match = re.search(r'^(.*?) invited (.*?) to the group chat$', msg["message"])
                if match:
                    coordinator.send_status(
                        MemberUpdates(self, sender, new_members=[ChatID(match.group(2))])
                    )
                match = re.search(r'^.*? has deleted this group.$', msg["message"])
                if match:
                    coordinator.send_status(
                        ChatUpdates(self, removed_chats=[sender])
                    )

        @self.bot.on("revoke_msg")
        @update_contacts_wrapper
        def on_revoked_msg(msg : Dict):
            self.logger.debug(f"revoke_msg:{msg}")
            sender = msg["sender"]
            if "@chatroom" in sender:
                wxid  =  msg["wxid"]

            name = self.get_name_by_wxid(sender)

            if "@chatroom" in sender:
                chat = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
                    uid = sender,
                    name = name,
                ))
                xml = etree.fromstring(msg["message"])
                text = xml.xpath('string(/sysmsg/revokemsg/replacemsg)')
                alias = re.search(r'^"(.*?)" (撤回了一条消息|recalled a message)$', text)
                if alias and alias.group(1) != self.get_nickname_by_wxid(wxid):
                    self.merge_group_members(sender, {
                        wxid: alias.group(1)
                    })
            else:
                chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                    uid = sender,
                    name = name,
                ))

            newmsgid = MessageID(re.search("<newmsgid>(.*?)<\/newmsgid>", msg["message"]).group(1))

            if self.revoke_message_ids.get(newmsgid):
                self.logger.debug("Ignoring revoke feedback for server msgid %s", newmsgid)
                return

            efb_msg = Message(chat = chat , uid = newmsgid)
            coordinator.send_status(
                MessageRemoval(source_channel=self, destination_channel=coordinator.master, message=efb_msg)
            )

        @self.bot.on("transfer_msg")
        @update_contacts_wrapper
        def on_transfer_msg(msg : Dict):
            self.logger.debug(f"transfer_msg:{msg}")
            sender = msg["sender"]
            name = self.get_name_by_wxid(sender)

            if msg["isSendMsg"]:
                if msg["isSendByPhone"]:
                    chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                            uid= sender,
                            name= name,
                    ))
                    author = chat.other
                    self.handle_msg(msg, author, chat)
                    return

            content = {}

            money = re.search("收到转账(.*)元", msg["message"]).group(1)
            transcationid = re.search("<transcationid><!\[CDATA\[(.*)\]\]><\/transcationid>", msg["message"]).group(1)
            transferid = re.search("<transferid><!\[CDATA\[(.*)\]\]><\/transferid>", msg["message"]).group(1)
            text = (
                f"收到 {name} 转账:\n"
                f"金额为 {money} 元\n"
            )

            commands = [
                MessageCommand(
                    name=("Accept"),
                    callable_name="process_transfer",
                    kwargs={"transcationid" : transcationid , "transferid" : transferid , "wxid" : sender},
                )
            ]

            content["sender"] = sender
            content["message"] = text
            content["commands"] = commands
            content["name"] = name
            self.system_msg(content)

        @self.bot.on("frdver_msg")
        @update_contacts_wrapper
        def on_frdver_msg(msg : Dict):
            self.logger.debug(f"frdver_msg:{msg}")
            content = {}
            sender = msg["sender"]
            fromnickname = re.search('fromnickname="(.*?)"', msg["message"]).group(1)
            wxid = re.search('fromusername="(.*?)"', msg["message"]).group(1)
            sign = re.search('sign="(.*?)"', msg["message"]).group(1)
            apply_content = re.search('content="(.*?)"', msg["message"]).group(1)
            chatroom = re.search('chatroomusername="(.*?)"', msg["message"]).group(1)
            source = "朋友验证消息"
            if chatroom:
                source = f"来自群聊: {self.get_name_by_wxid(chatroom)}"
            else:
                sharecardnickname = re.search('sharecardnickname="(.*?)"', msg["message"]).group(1)
                if sharecardnickname:
                    source = f"对方通过 \"{sharecardnickname}\" 分享的名片添加"
            url = re.search('bigheadimgurl="(.*?)"', msg["message"]).group(1)
            v3 = re.search('encryptusername="(v3.*?)"', msg["message"]).group(1)
            v4 = re.search('ticket="(v4.*?)"', msg["message"]).group(1)
            text = (
                "好友申请:\n"
                f"名字: {fromnickname}\n"
                f"微信号: {wxid}\n"
                f"个性签名: {sign}\n"
                f"验证内容: {apply_content}\n"
                f"来源: {source}\n"
                f"头像: {url}"
            )

            commands = [
                MessageCommand(
                    name=("Accept"),
                    callable_name="process_friend_request",
                    kwargs={"v3" : v3 , "v4" : v4},
                )
            ]

            content["sender"] = sender
            content["message"] = text
            content["commands"] = commands
            self.system_msg(content)

        @self.bot.on("card_msg")
        @update_contacts_wrapper
        def on_card_msg(msg : Dict):
            self.logger.debug(f"card_msg:{msg}")
            sender = msg["sender"]
            wxid = msg["wxid"]
            content = {}
            name = self.get_name_by_wxid(sender)

            bigheadimgurl = re.search('bigheadimgurl="(.*?)"', msg["message"]).group(1)
            nickname = re.search('nickname="(.*?)"', msg["message"]).group(1)
            province = re.search('province="(.*?)"', msg["message"]).group(1)
            city = re.search('city="(.*?)"', msg["message"]).group(1)
            sex = re.search('sex="(.*?)"', msg["message"]).group(1)
            username = re.search('username="(.*?)"', msg["message"]).group(1)

            text = "名片信息:\n"
            if nickname:
                text += f"昵称: {nickname}\n"
            if city:
                text += f"城市: {city}\n"
            if province:
                text += f"省份: {province}\n"
            if sex:
                if sex == "0":
                    text += "性别: 未知\n"
                elif sex == "1":
                    text += "性别: 男\n"
                elif sex == "2":
                    text += "性别: 女\n"
            if bigheadimgurl:
                text += f"头像: {bigheadimgurl}\n"

            commands = [
                MessageCommand(
                    name=("Add To Friend"),
                    callable_name="add_friend",
                    kwargs={"v3" : username},
                )
            ]

            if "@chatroom" in sender:
                chat = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
                    uid = sender,
                    name = self.get_name_by_wxid(sender)
                ))
                if sender == wxid:
                    author = chat.self
                else:
                    author = ChatMgr.build_efb_chat_as_member(
                        chat,
                        self.get_group_member(sender, wxid),
                    )
            else:
                chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                    uid = sender,
                    name = name,
                ))
                author = chat.self if sender == self.wxid else chat.other
                if sender.startswith('gh_'):
                    chat.vendor_specific = {'is_mp' : True}

            # if "v3" in username:
            #     content["commands"] = commands
            # 暂时屏蔽
            m = Message(
                type=MsgType.Text,
                text=text
            )
            self.send_efb_msgs(MsgWrapper(msg, m), author=author, chat=chat, uid=MessageID(str(msg['msgid'])))

    def is_login(self) -> bool:
        try:
            response = self.bot.IsLoginIn()
            return response.get("is_login", 0) == 1
        except:
            return False

    def get_qrcode(self):
        result = self.bot.GetQrcodeImage()
        
        # 检查是否返回了 JSON 数据（已登录）
        try:
            json_result = json.loads(result)
            return None
        except Exception:
            return self.save_qr_code(result)

    @staticmethod
    def save_qr_code(qr_code):
        # 创建临时文件保存二维码图片
        tmp_file = tempfile.NamedTemporaryFile(suffix='.png')
        try:
            tmp_file.write(qr_code)
            tmp_file.flush()
        except:
            print("[red]获取二维码失败[/red]")
            tmp_file.close()
            return None
        return tmp_file

    def confirm_login(self):
        chat = self.user_auth_chat
        author = self.user_auth_chat.other
        msg = Message(
            type=MsgType.Text,
            uid=MessageID(str(int(time.time()))),
        )
        if self.is_login():
            self.get_me()
            self.GetContactListBySql()
            msg.text = "登录成功"
        else:
            msg.text = "登录失败，请重新登录"
        self.send_efb_msgs(msg, chat=chat, author=author)

    def after_login(self):
        self.get_me()
        self.GetContactListBySql()
        self.GetGroupListBySql()

    @efb_utils.extra(name="Get QR Code",
           desc="重新扫码登录")
    def reauth(self, _: str = "") -> str:
        file = self.get_qrcode()
        chat = self.user_auth_chat
        author = self.user_auth_chat.other
        msg = Message(
            type=MsgType.Text,
            uid=MessageID(str(int(time.time()))),
        )

        if not file:
            if self.is_login():
                self.after_login()
                return "登录成功"
            else:
                return "获取二维码失败，请稍后再试"
        else:
            msg.type = MsgType.Image
            msg.path = Path(file.name)
            msg.file = file
            msg.mime = 'image/png'
            self.send_efb_msgs(msg, chat=chat, author=author)
        return "请扫描二维码登录"

    @efb_utils.extra(name="Force Logout",
           desc="强制退出")
    def force_logout(self, _: str = "") -> str:
        res = self.bot.post(44, params=EmptyJsonResponse())
        if self.is_login():
            return "退出失败，原因: %s" % res
        else:
            self.wxid = None
            return "退出成功"

    @staticmethod
    def send_efb_msgs(efb_msgs: Union[Message, List[Message]], **kwargs):
        if not efb_msgs:
            return
        efb_msgs = [efb_msgs] if isinstance(efb_msgs, Message) else efb_msgs
        if 'deliver_to' not in kwargs:
            kwargs['deliver_to'] = coordinator.master
        for efb_msg in efb_msgs:
            for k, v in kwargs.items():
                setattr(efb_msg, k, v)
            coordinator.send_message(efb_msg)
            if efb_msg.file:
                efb_msg.file.close()

    def system_msg(self, content : Dict):
        self.logger.debug(f"system_msg:{content}")
        msg = Message()
        sender = content["sender"]
        if "name" in content:
            name = content["name"]
        else:
            name  = '\u2139 System'

        chat = ChatMgr.build_efb_chat_as_system_user(EFBSystemUser(
            uid = sender,
            name = name
        ))

        try:
            author = chat.get_member(SystemChatMember.SYSTEM_ID)
        except KeyError:
            author = chat.add_system_member()

        if "commands" in content:
            msg.commands = MessageCommands(content["commands"])
        if "message" in content:
            msg.text = content['message']
        if "target" in content:
            msg.target = content['target']

        self.send_efb_msgs(msg, uid=MessageID(str(int(time.time()))), chat=chat, author=author, type=MsgType.Text)

    def handle_msg(self , msg : Dict[str, Any] , author : 'ChatMember' , chat : 'Chat'):
        emojiList = re.findall('\[[\w|！|!| ]+\]' , msg["message"])
        for emoji in emojiList:
            try:
                msg["message"] = msg["message"].replace(emoji, WC_EMOTICON_CONVERSION[emoji])
            except:
                pass

        if msg["msgid"] not in self.cache:
            self.cache[msg["msgid"]] = msg["type"]
            master_message = coordinator.master.get_message_by_id(chat=chat, msg_id=msg["msgid"])
            if master_message is not None:
                return
        else:
            if self.cache[msg["msgid"]] == msg["type"]:
                return

        self._schedule_mark_as_read(msg, chat)

        try:
            if ("FileStorage" in msg["filepath"]) and ("Cache" not in msg["filepath"]):
                msg["timestamp"] = int(time.time())
                msg["filepath"] = msg["filepath"].replace("\\","/")
                msg["filepath"] = f'''{self.dir}{msg["filepath"]}'''
                self.file_msg[msg["filepath"]] = ( msg , author , chat )
                return
            if msg["type"] == "video":
                msg["timestamp"] = int(time.time())
                msg["filepath"] = msg["thumb_path"].replace("\\","/").replace(".jpg", ".mp4")
                msg["filepath"] = f'''{self.dir}{msg["filepath"]}'''
                self.file_msg[msg["filepath"]] = ( msg , author , chat )
                return
        except:
            ...

        if msg["type"] == "voice":
            file_path = re.search("clientmsgid=\"(.*?)\"", msg["message"]).group(1) + ".amr"
            msg["timestamp"] = int(time.time())
            msg["filepath"] = f'''{self.dir}{msg["self"]}/{file_path}'''
            self.file_msg[msg["filepath"]] = ( msg , author , chat )
            return

        try:
            processed = MsgProcess(msg, chat, self.direct_transfer)
            self.send_efb_msgs(
                MsgWrapper(msg, processed),
                author=author,
                chat=chat,
                uid=MessageID(str(msg['msgid']))
            )
            if getattr(self, "delete_media_after_send", False) and msg.get("type") in MEDIA_DELETE_TYPES:
                resolved_path = (
                    resolve_hooked_wechat_image_path(msg.get("filepath"))
                    if msg.get("type") == "image" else None
                )
                self._delete_media_files(msg.get("filepath"), resolved_path)
        except Exception:
            if msg.get("type") not in MEDIA_RETRY_TYPES:
                raise
            self.logger.exception(
                "Failed to process media: type=%s msgid=%s filepath=%s",
                msg.get("type"), msg.get("msgid"), msg.get("filepath"),
            )
            try:
                self._send_media_failure(msg.get("filepath"), msg, author, chat)
            except Exception:
                self.logger.exception("Failed to send media failure message")

    def _mark_as_read_response_ok(self, response: Dict[str, Any]) -> bool:
        return (
            isinstance(response, dict)
            and response.get("result") == "OK"
            and str(response.get("msg")) == "1"
        )

    def _mark_chat_as_read(self, chat_uid: ChatID, reason: str) -> None:
        if not self.mark_as_read_enabled or not chat_uid:
            return

        chat_key = str(chat_uid)
        with self.mark_as_read_lock:
            timer = self.mark_as_read_timers.pop(chat_key, None)
            if timer is not None and timer is not threading.current_thread():
                timer.cancel()

        try:
            response = self.bot.MarkAsRead(wxid=chat_key)
        except Exception:
            self.logger.exception("Failed to mark chat as read: chat=%s reason=%s", chat_key, reason)
            return

        if not self._mark_as_read_response_ok(response):
            self.logger.warning(
                "Native mark-as-read failed: chat=%s reason=%s response=%s",
                chat_key,
                reason,
                response,
            )
            return
        self.logger.debug("Marked chat as read: chat=%s reason=%s", chat_key, reason)

    def _schedule_mark_as_read(self, msg: Dict[str, Any], chat: 'Chat') -> None:
        if not self.mark_as_read_enabled:
            return
        if msg.get("isSendMsg") in (1, True, "1"):
            return
        if msg.get("type") in {"sysmsg", "sysnotify", "eventnotify"}:
            return

        chat_uid = getattr(chat, "uid", None)
        if not chat_uid:
            return

        chat_key = str(chat_uid)
        with self.mark_as_read_lock:
            timer = self.mark_as_read_timers.get(chat_key)
            if timer is not None and timer.is_alive():
                return

            timer = threading.Timer(
                self.mark_as_read_delay,
                self._mark_chat_as_read,
                args=(chat_key, "inbound"),
            )
            timer.daemon = True
            self.mark_as_read_timers[chat_key] = timer
            timer.start()
        self.logger.debug(
            "Scheduled mark-as-read: chat=%s delay=%ss msgid=%s",
            chat_key,
            self.mark_as_read_delay,
            msg.get("msgid"),
        )

    def _voice_database_names(self, refresh=False):
        cached = getattr(self, "_voice_db_names", None)
        if cached is not None and not refresh:
            return list(cached)

        names = []
        dbkey = getattr(self, "dbkey", None)
        discover = getattr(dbkey, "database_names", None)
        if callable(discover):
            try:
                names = [
                    name
                    for name in (discover("MediaMSG") or [])
                    if isinstance(name, str) and name.startswith("MediaMSG")
                ]
            except Exception:
                self.logger.debug("Failed to discover WeChat media databases", exc_info=True)

        if not names:
            try:
                handles = self.bot.GetDatabaseHandles().get("data") or []
                names = [
                    item.get("db_name")
                    for item in handles
                    if isinstance(item, dict)
                    and isinstance(item.get("db_name"), str)
                    and item["db_name"].startswith("MediaMSG")
                ]
            except Exception:
                self.logger.debug("Failed to discover native media database handles", exc_info=True)

        if not names:
            names = list(VOICE_DATABASE_NAMES)
        return sorted(set(names), key=lambda name: (len(name), name))

    def _media_retry_payload(self, path, msg, author, chat):
        retry_msg = {
            key: msg[key]
            for key in MEDIA_RETRY_FIELDS
            if key in msg
        }
        retry_msg["type"] = msg.get("type")
        retry_msg["filepath"] = path
        author_uid = getattr(author, "uid", None)
        retry_payload = {
            "path": path,
            "type": msg.get("type"),
            "msg": retry_msg,
            "chat": {
                "uid": getattr(chat, "uid", None),
                "name": getattr(chat, "name", None),
            },
            "author": {
                "uid": author_uid,
                "name": getattr(author, "name", None),
                "alias": getattr(author, "alias", None),
                "is_self": bool(
                    (msg.get("self") and author_uid == msg.get("self"))
                    or (self.wxid and author_uid == self.wxid)
                ),
            },
        }
        retry_payload["expires_at"] = time.time() + max(self.time_out, 1)
        retry_id = secrets.token_hex(8)
        with self.media_retry_cache_lock:
            self.media_retry_cache[retry_id] = retry_payload
            self._persist_media_retry_cache()
        return retry_id

    @staticmethod
    def _media_retry_command(retry_id):
        return MessageCommand(
            name="Retry",
            callable_name="retry_media",
            kwargs={"retry_id": retry_id},
        )

    def _send_media_failure(self, path, msg, author, chat, text=None, uid=None):
        media_type = msg.get("type")
        if media_type not in MEDIA_RETRY_TYPES or not path:
            return

        retry_payload = self._media_retry_payload(path, msg, author, chat)
        failed_msg = dict(msg)
        failed_msg["type"] = "text"
        failed_msg["filepath"] = path
        failed_msg["message"] = text or f"[{media_type} 下载失败,请在手机端查看]"
        message = MsgProcess(failed_msg, chat, self.direct_transfer)
        commands = MessageCommands([self._media_retry_command(retry_payload)])
        if isinstance(message, list):
            for item in message:
                item.commands = commands
        else:
            message.commands = commands
        self.send_efb_msgs(
            MsgWrapper(failed_msg, message),
            author=author,
            chat=chat,
            uid=MessageID(str(uid or msg.get("msgid"))),
        )

    def _delete_media_files(self, *paths):
        for path in {path for path in paths if path and os.path.isfile(path)}:
            try:
                os.remove(path)
            except OSError:
                self.logger.warning("Failed to delete media attachment: %s", path, exc_info=True)

    def _load_media_retry_cache(self):
        try:
            with self.media_retry_cache_path.open(encoding="utf-8") as file:
                persisted = json.load(file)
        except FileNotFoundError:
            return
        except (OSError, TypeError, ValueError):
            self.logger.warning("Failed to load media retry cache: %s", self.media_retry_cache_path, exc_info=True)
            return

        if not isinstance(persisted, dict):
            self.logger.warning("Ignoring invalid media retry cache: %s", self.media_retry_cache_path)
            return

        now = time.time()
        valid = {
            retry_id: payload
            for retry_id, payload in persisted.items()
            if isinstance(retry_id, str)
            and isinstance(payload, dict)
            and isinstance(payload.get("expires_at"), (int, float))
            and payload["expires_at"] > now
        }
        with self.media_retry_cache_lock:
            self.media_retry_cache.update(valid)
            if len(valid) != len(persisted):
                self._persist_media_retry_cache()

    def _persist_media_retry_cache(self):
        cache_path = self.media_retry_cache_path
        temporary_path = None
        try:
            with self.media_retry_cache_lock:
                persisted = dict(self.media_retry_cache)
                cache_path.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(
                    mode="w",
                    encoding="utf-8",
                    dir=cache_path.parent,
                    prefix=f".{cache_path.name}.",
                    suffix=".tmp",
                    delete=False,
                ) as file:
                    temporary_path = file.name
                    json.dump(persisted, file, ensure_ascii=False)
                    file.flush()
                    os.fsync(file.fileno())
                os.replace(temporary_path, cache_path)
        except (OSError, TypeError, ValueError):
            self.logger.warning("Failed to persist media retry cache: %s", cache_path, exc_info=True)
            if temporary_path:
                try:
                    os.remove(temporary_path)
                except OSError:
                    pass

    def _remove_media_retry(self, retry_id):
        with self.media_retry_cache_lock:
            self.media_retry_cache.pop(retry_id, None)
            self._persist_media_retry_cache()

    def _build_media_retry_context(self, payload):
        chat_info = payload.get("chat") or {}
        author_info = payload.get("author") or {}
        chat_uid = chat_info.get("uid")
        chat_name = chat_info.get("name") or chat_uid
        author_uid = author_info.get("uid")

        if not chat_uid:
            raise EFBMessageError("重试失败，缺少聊天信息")

        if "@chatroom" in chat_uid:
            chat = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
                uid=chat_uid,
                name=chat_name,
            ))
            if author_info.get("is_self"):
                author = chat.self
            else:
                author = ChatMgr.build_efb_chat_as_member(chat, EFBGroupMember(
                    uid=author_uid,
                    name=author_info.get("name") or author_uid,
                    alias=author_info.get("alias"),
                ))
        else:
            chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                uid=chat_uid,
                name=chat_name,
            ))
            author = chat.self if author_info.get("is_self") else chat.other
        return chat, author

    def retry_media(self, retry_id):
        if not isinstance(retry_id, str):
            return "重试上下文已失效，请重新接收媒体"
        with self.media_retry_cache_lock:
            media = self.media_retry_cache.get(retry_id)
        if not isinstance(media, dict):
            return "重试上下文已失效，请重新接收媒体"
        if media.get("expires_at", 0) <= time.time():
            self._remove_media_retry(retry_id)
            return "重试上下文已失效，请重新接收媒体"

        path = media.get("path")
        media_type = media.get("type")
        if media_type not in MEDIA_RETRY_TYPES or not path:
            return "不支持重试此媒体"

        retry_path = path
        if media_type == "image":
            retry_path = resolve_hooked_wechat_image_path(path) or path
        if not os.path.isfile(retry_path):
            return "媒体附件已不存在，无法重试"

        msg = dict(media.get("msg") or {})
        msg["type"] = media_type
        msg["filepath"] = retry_path
        chat = author = None
        try:
            chat, author = self._build_media_retry_context(media)
            processed = MsgProcess(msg, chat, self.direct_transfer)
            self.send_efb_msgs(
                MsgWrapper(msg, processed),
                author=author,
                chat=chat,
                uid=MessageID(f"{msg.get('msgid', int(time.time()))}-retry-{time.time_ns()}"),
            )
        except Exception:
            self.logger.exception(
                "Failed to retry media: type=%s msgid=%s filepath=%s",
                media_type, msg.get("msgid"), retry_path,
            )
            try:
                if chat is None or author is None:
                    raise EFBMessageError("重试失败，缺少聊天信息")
                self._send_media_failure(
                    path,
                    msg,
                    author,
                    chat,
                    text=f"[{media_type} 重试失败,请在手机端查看]",
                    uid=f"{msg.get('msgid', int(time.time()))}-retry-failed-{time.time_ns()}",
                )
            except Exception:
                self.logger.exception("Failed to send media retry failure message")
            return "媒体重试失败，请稍后再试"

        if self.delete_media_after_send and media_type in MEDIA_DELETE_TYPES:
            self._delete_media_files(path, retry_path)
        self._remove_media_retry(retry_id)
        return "媒体重试发送成功"

    def _process_pending_file(self, path):
        flag = False
        msg, author, chat = self.file_msg[path]
        media_type = msg.get("type")
        retry_payload = None
        output_msg = msg
        resolved_path = resolve_hooked_wechat_image_path(path) if msg["type"] == "image" else None
        if resolved_path:
            msg["filepath"] = resolved_path
            flag = True
        elif os.path.isfile(path):
            flag = True
        elif (int(time.time()) - msg["timestamp"]) > self.time_out:
            retry_payload = self._media_retry_payload(path, msg, author, chat) if media_type in MEDIA_RETRY_TYPES else None
            output_msg = dict(msg)
            output_msg['message'] = f"[{media_type} 下载超时,请在手机端查看]"
            output_msg["type"] = "text"
            flag = True
        elif msg["type"] == "voice":
            sql = f'SELECT Buf FROM Media WHERE Reserved0 = {msg["msgid"]}'
            queried_databases = []

            def query_voice_databases(database_names):
                queried_databases.clear()
                query_failed = False
                query_error = None
                for db_name in database_names:
                    queried_databases.append(db_name)
                    try:
                        dbresp = self.query_database(db_name=db_name, sql=sql)
                        if not isinstance(dbresp, dict) or dbresp.get("result") != "OK":
                            query_failed = True
                            query_error = "voice database query returned %r" % (dbresp,)
                            continue

                        dbresult = dbresp.get("data") or []
                        data_rows = dbresult
                        if dbresult and dbresult[0] and dbresult[0][0] == "Buf":
                            data_rows = dbresult[1:]
                    except Exception as exc:
                        query_failed = True
                        query_error = repr(exc)
                        continue

                    if data_rows:
                        return data_rows[-1][0], False, None
                return None, query_failed, query_error

            database_names = self._voice_database_names()
            for attempt in range(2):
                filebuffer, query_failed, query_error = query_voice_databases(database_names)
                if filebuffer is None and query_failed:
                    self._voice_db_names = None
                    if attempt == 0:
                        try:
                            self.bot.invalidate_db_handles()
                        except Exception:
                            self.logger.debug("Failed to invalidate native database handles", exc_info=True)
                        database_names = self._voice_database_names(refresh=True)
                        continue

                    self.logger.error(
                        "[voice-db-failure] msgid=%s db=%s sql=%s error=%s",
                        msg.get("msgid"),
                        ",".join(queried_databases),
                        sql,
                        query_error,
                    )
                    break

                self._voice_db_names = list(database_names)
                if filebuffer is not None:
                    try:
                        decoded = bytes(base64.b64decode(filebuffer))
                        with open(msg["filepath"], 'wb') as f:
                            f.write(decoded)
                    except Exception as e:
                        self.logger.error(
                            "[voice-file-failure] msgid=%s path=%s error=%r",
                            msg.get("msgid"),
                            msg.get("filepath"),
                            e,
                            exc_info=True,
                        )
                    else:
                        flag = True
                else:
                    self.logger.debug(
                        "[voice-db-empty] msgid=%s db=%s sql=%s",
                        msg.get("msgid"),
                        ",".join(queried_databases),
                        sql,
                    )
                break

        if flag:
            processed = MsgProcess(output_msg, chat, self.direct_transfer)
            if retry_payload:
                commands = MessageCommands([self._media_retry_command(retry_payload)])
                if isinstance(processed, list):
                    for item in processed:
                        item.commands = commands
                else:
                    processed.commands = commands
            self.send_efb_msgs(
                MsgWrapper(output_msg, processed),
                author=author,
                chat=chat,
                uid=MessageID(str(output_msg['msgid'])),
            )
            self.file_msg.pop(path, None)
            if retry_payload is None and getattr(self, "delete_media_after_send", False) and media_type in MEDIA_DELETE_TYPES:
                self._delete_media_files(path, output_msg.get("filepath"))

    def handle_file_msg(self):
        while True:
            if len(self.file_msg) == 0:
                time.sleep(1)
            else:
                for path in list(self.file_msg.keys()):
                    msg = {}
                    try:
                        msg = self.file_msg[path][0]
                        self._process_pending_file(path)
                    except Exception:
                        pending = self.file_msg.pop(path, None)
                        if pending:
                            failed_msg, author, chat = pending
                            if failed_msg.get("type") in MEDIA_RETRY_TYPES:
                                try:
                                    self._send_media_failure(path, failed_msg, author, chat)
                                except Exception:
                                    self.logger.exception("Failed to send media failure message")
                        self.logger.exception(
                            "Failed to process pending media: type=%s msgid=%s filepath=%s",
                            msg.get("type"), msg.get("msgid"), msg.get("filepath", path),
                        )
                time.sleep(1)

            if len(self.delete_file):
                for k in list(self.delete_file.keys()):
                    file_path = k
                    begin_time = self.delete_file[k]
                    if  (int(time.time()) - begin_time) > self.time_out:
                        try:
                            os.remove(file_path)
                        except:
                            pass
                        del self.delete_file[file_path]

    def process_friend_request(self , v3 , v4):
        self.logger.debug(f"process_friend_request:{v3} {v4}")
        res = self.bot.VerifyApply(v3 = v3 , v4 = v4)
        if str(res['msg']) != "0":
            return "Success"
        else:
            return "Failed"

    def process_transfer(self, transcationid , transferid , wxid):
        res = self.bot.GetTransfer(transcationid = transcationid , transferid = transferid , wxid = wxid)
        if str(res["msg"]) != "0":
            return "Success"
        else:
            return "Failed"

    def add_friend(self , v3):
        res = self.bot.AddContactByV3(v3 = v3 , msg = "")
        if str(res['msg']) != "0":
            return "Success"
        else:
            return "Failed"

    # 定时任务
    def scheduled_job(self):
        count = 0
        content = {
            "name": self.channel_name,
            "sender": self.channel_name,
            "message": "检测到未登录状态，请发送 /extra 重新扫码登录",
        }
        while True:
            time.sleep(1)
            count += 1
            if count % 1800 == 0:
                if self.wxid is not None:
                    self.GetContactListBySql()
            if count % 1800 == 3:
                if getattr(coordinator, 'master', None) is not None and not self.is_login():
                    self.wxid = None
                    self.system_msg(content)

    #获取全部联系人
    def get_chats(self) -> Collection['Chat']:
        return []

    #获取联系人
    def get_chat(self, chat_uid: ChatID) -> 'Chat':
        if "@chatroom" in chat_uid:
            for group in self.groups:
                if group.uid == chat_uid:
                    return group
        else:
            for friend in self.friends:
                if friend.uid == chat_uid:
                    return friend
        raise EFBChatNotFound

    #发送消息
    def send_message(self, msg : Message) -> Message:
        chat_uid = msg.chat.uid

        if msg.edit:
            pass     # todo

        if self.wxid is None:
            if self.is_login():
                self.get_me()
                self.GetContactListBySql()
            else:
                content = {
                    "name": self.user_auth_chat.name,
                    "sender": self.user_auth_chat.uid,
                    "message": "尚未登录，请发送 /extra 扫码登录"
                }
                self.system_msg(content)
                return msg

        self._mark_chat_as_read(chat_uid, "outbound")

        if msg.text:
            match = re.search(self.forward_pattern, msg.text)
            if match:
                if match.group(1) == hashlib.md5(self.channel_id.encode('utf-8')).hexdigest():
                    msgid = match.group(2)
                    self.logger.debug(f"提取到的消息 ID: {msgid}")
                    self.bot.ForwardMessage(wxid = chat_uid, msgid = msgid)
                else:
                    self.logger.debug(f"非本 slave 消息: {match.group(1)}/{match.group(2)}")
                return msg

        res= {"msg": "1"}
        msg_ids: list[MessageID] = []
        if msg.type == MsgType.Voice:
            f = tempfile.NamedTemporaryFile(prefix='voice_message_', suffix=".mp3")
            AudioSegment.from_ogg(msg.file.name).export(f, format="mp3")
            msg.file = f
            msg.file.name = "语音留言.mp3"
            msg.type = MsgType.Video
            msg.filename = os.path.basename(f.name)

        if msg.type in [MsgType.Text]:
            if msg.text.startswith('/changename'):
                newname = msg.text.strip('/changename ')
                res = self.bot.SetChatroomName(chatroom_id = chat_uid , chatroom_name = newname)
            elif msg.text.startswith('/getmemberlist'):
                memberlist = self.bot.GetChatroomMemberList(chatroom_id = chat_uid)
                message = '群组成员包括：'
                for wxid in memberlist['members'].split('^G'):
                    name = self.get_name_by_wxid(wxid)
                    message += '\n' + wxid + ' : ' + name
                self.system_msg({'sender':chat_uid, 'message':message})
                return msg
            elif msg.text.startswith('/getstaticinfo'):
                info = msg.text[15::]
                if info == 'friends':
                    message = str(self.friends)
                elif info == 'groups':
                    message = str(self.groups)
                elif info == 'group_members':
                    message = json.dumps(self.group_members)
                elif info == 'contacts':
                    message = json.dumps(self.contacts)
                else:
                    message = '当前仅支持查询friends, groups, group_members, contacts'
                self.system_msg({'sender':chat_uid, 'message':message})
                return msg
            elif msg.text.startswith('/helpcomwechat'):
                message = '''/search - 按关键字匹配好友昵称搜索联系人

/addtogroup - 按wxid添加好友到群组

/getmemberlist - 查看群组用户wxid

/at - 后面跟wxid，多个用英文,隔开，最后可用空格隔开，带内容。

/sendcard - 后面格式'wxid nickname'

/changename - 修改群组名称

/addfriend - 后面格式'wxid message'

/getstaticinfo - 可获取friends, groups, contacts信息'''
                self.system_msg({'sender':chat_uid, 'message':message})
                return msg
            elif msg.text.startswith('/search'):
                keyword = msg.text[8::]
                message = 'result:'
                for key, value in self.contacts.items():
                    if keyword in key or any(keyword in value[field] for field in ('nickname', 'remark')):
                        message += '\n' + str(key) + " : " + str(value)
                self.system_msg({'sender':chat_uid, 'message':message})
                return msg
            elif msg.text.startswith('/addtogroup'):
                users = msg.text[12::]
                res = self.bot.AddChatroomMember(chatroom_id = chat_uid, wxids = users)
            elif msg.text.startswith('/forward'):
                if isinstance(msg.target, Message):
                    msgid = msg.target.uid
                    if msgid.isdecimal():
                        url = f"ehforwarderbot://{hashlib.md5(self.channel_id.encode('utf-8')).hexdigest()}/forward/{msgid}"
                        prompt = "请将这条信息转发到目标聊天中"
                        text = f"{url}\n{prompt}"
                        if msg.target.text:
                            match = re.search(self.forward_pattern, msg.target.text)
                            if match:
                                msg.target.text = f"{msg.target.text[0:match.start()]}{text}"
                            else:
                                msg.target.text = f"{msg.target.text}\n\n---\n{text}"
                        else:
                            msg.target.text = text
                        self.send_efb_msgs(msg.target, edit=True)
                    else:
                        text = f"无法转发{msgid},不是有效的微信消息"
                        self.system_msg({'sender': chat_uid, 'message': text, 'target': msg.target})
                    return msg
            elif msg.text.startswith('/at'):
                users_message = msg.text[4::].split(' ', 1)
                if isinstance(msg.target, Message):
                    users = msg.target.author.uid
                    message = msg.text[4::]
                elif len(users_message) == 2:
                    users, message = users_message
                else:
                    users, message = users_message[0], ''
                if users != '':
                    #TODO get msgid for SendAt
                    res = self.bot.SendAt(chatroom_id = chat_uid, wxids = users, msg = message)
                else:
                    msg_ids.append(self.send_text(chat_uid, msg))
            elif msg.text.startswith('/sendcard'):
                user_nickname = msg.text[10::].split(' ', 1)
                if len(user_nickname) == 2:
                    user, nickname = user_nickname
                else:
                    user, nickname = user_nickname[0], ''
                if user != '':
                    #TODO get msgid for SendCard
                    res = self.bot.SendCard(receiver = chat_uid, share_wxid = user, nickname = nickname)
                else:
                    msg_ids.append(self.send_text(chat_uid, msg))
            elif msg.text.startswith('/addfriend'):
                user_invite = msg.text[11::].split(' ', 1)
                if len(user_invite) == 2:
                    user, invite = user_invite
                else:
                    user, invite = user_invite[0], ''
                if user != '':
                    res = self.bot.AddContactByWxid(wxid = user, msg = invite)
                else:
                    msg_ids.append(self.send_text(chat_uid, msg))
            else:
                # Standard text message or quote reply
                msg_ids.append(self.send_text(chat_uid, msg))
        elif msg.type in [MsgType.Link]:
            msg_ids.append(self.send_text(chat_uid, msg))
        elif msg.type in [MsgType.Image]:
            msg_ids.append(self.send_image(chat_uid, msg))
            if msg.text:
                msg_ids.append(self.send_text(chat_uid, msg))
        elif msg.type in [MsgType.File, MsgType.Video]:
            msg_ids.append(self.send_file(chat_uid, msg))
            if msg.text:
                msg_ids.append(self.send_text(chat_uid, msg))
            if msg.type == MsgType.Video:
                res["msg"] = 1
        elif msg.type in [MsgType.Animation, MsgType.Sticker]:
            msg_ids.append(self.send_emotion(chat_uid, msg))
            if msg.text:
                msg_ids.append(self.send_text(chat_uid, msg))

        ids = [item for item in msg_ids if item is not None]
        if not (str(res.get("msg", "1")) == "0" or ids):
            self.logger.warning(f"Failed to get msgid confirmation for message type {msg.type} to {chat_uid} with {msg.uid}")
            if "@openim" in chat_uid:  # 上游 bug，永远不返回企业微信的 msgid
                return msg
            raise EFBMessageError("发送失败，请在手机端确认")
        elif ids:
            # 保存所有消息 id 以在撤回消息时使用
            msg.uid = dump_message_ids(ids)

        return msg

    def _get_file_lock(self, wxid: ChatID) -> threading.Lock:
        """Gets or creates a lock for the given chat ID."""
        with self._file_locks_lock:
            if wxid not in self._file_locks:
                self._file_locks[wxid] = threading.Lock()
            return self._file_locks[wxid]

    def _wait(self, key: Any, timeout: int) -> Optional[MessageID]:
        """Waits for the event associated with key and returns the msgid."""
        event = self.sent_msgs.get(key)
        if not event:
            self.logger.error(f"No event found for key {key} before waiting.")
            return None

        self.logger.debug(f"Waiting for event for key: {key} with timeout {timeout}s")
        event_set = event.wait(timeout=timeout)

        with self.pending_lock:
            # Always remove the key from pending and results after waiting or timeout
            self.sent_msgs.pop(key, None)
            received_msgid = self.sent_msg_results.pop(key, None)

        if not event_set:
            self.logger.warning(f"Timeout waiting for send confirmation for key: {key}")
            return None

        if not received_msgid:
            self.logger.error(f"Event signaled for key {key}, but no msgid found in results.")
            return None

        self.logger.debug(f"Successfully received msgid {received_msgid} for key {key}")
        return received_msgid

    def send_text(self, wxid: ChatID, msg: Message):
        """Sends a text message and waits for confirmation."""
        text_to_send = msg.text

        if isinstance(msg.target, Message) and text_to_send:
            msgid = next((item for item in load_message_ids(msg.target.uid) if item.isdecimal()), None)
            send_quote_text = getattr(self.bot, "SendQuoteText", None)
            if msgid and callable(send_quote_text):
                key = (wxid, text_to_send, msgid)
                with self.pending_lock:
                    self.sent_msgs[key] = threading.Event()
                send_quote_text(wxid=wxid, msg=text_to_send, target_msgid=msgid)
            else:
                text_to_send = qutoed_text(msg.target.text, text_to_send)
                key = (wxid, text_to_send)
                with self.pending_lock:
                    self.sent_msgs[key] = threading.Event()
                self.bot.SendText(wxid=wxid, msg=text_to_send)
        else:
            key = (wxid, text_to_send)
            with self.pending_lock:
                self.sent_msgs[key] = threading.Event()
            self.bot.SendText(wxid=wxid, msg=text_to_send)

        return self._wait(key, self.send_timeout)

    def _save_file(self, msg: Message, rename: bool = False):
        name = os.path.basename(msg.file.name)
        if rename and msg.filename and msg.filename != name:
            name = msg.filename

        local_path = f"{self.dir}{self.wxid}/{name}"
        load_temp_file_to_local(msg.file, local_path)
        self.delete_file[local_path] = int(time.time())
        return self.base_path + "\\" + self.wxid + "\\" + name

    @staticmethod
    def _send_file_with_lock(fn: Callable):
        def deco(self, wxid: ChatID, msg: Message):
            key = (wxid, None, self.file_lock_key)

            with self.pending_lock:
                self.sent_msgs[key] = threading.Event()

            with self._get_file_lock(wxid):
                fn(self, wxid, msg)

                return self._wait(key, self.send_timeout)
        return deco

    @_send_file_with_lock
    def send_image(self, wxid: ChatID, msg: Message):
        self.bot.SendImage(receiver=wxid, img_path=self._save_file(msg))

    @_send_file_with_lock
    def send_file(self, wxid: ChatID, msg: Message):
        self.bot.SendFile(receiver=wxid, file_path=self._save_file(msg, True))

    @_send_file_with_lock
    def send_emotion(self, wxid: ChatID, msg: Message):
        self.bot.SendEmotion(wxid=wxid, img_path=self._save_file(msg))

    def get_chat_picture(self, chat: 'Chat') -> BinaryIO:
        wxid = chat.uid
        result = self.get_picture_by_sql(wxid = wxid)
        if result:
            return download_file(result)
        else:
            return None

    def get_chat_member_picture(self, chat_member: 'ChatMember') -> Optional[BinaryIO]:
        wxid = chat_member.uid
        result = self.get_picture_by_sql(wxid = wxid)
        if result:
            return download_file(result)
        else:
            return None

    def poll(self):
        timer = threading.Thread(target = self.scheduled_job)
        timer.daemon = True
        timer.start()

        while True:
            time.sleep(1)
            try:
                #防止偶尔 comwechat 启动落后
                if self.bot.run(main_thread = False) is not None:
                    break
            except Exception as e:
                self.logger.error("Start failed. Reason: %s" % e)

        t = threading.Thread(target = self.handle_file_msg)
        t.daemon = True
        t.start()

    def send_status(self, status: 'Status'):
        if not isinstance(status, MessageRemoval):
            raise EFBOperationNotSupported()

        message = status.message
        references = list(dict.fromkeys(load_message_ids(message.uid)))
        chat_uid = str(message.chat.uid)
        if not references:
            raise EFBMessageError("撤回消息缺少有效的消息 ID")

        failures = []
        for server_msgid in references:
            if not server_msgid.isdecimal():
                raise EFBMessageError(f"无效的消息 ID: {server_msgid}")

            self.revoke_message_ids[server_msgid] = True
            try:
                response = self.bot.RevokeMessage(
                    wxid=chat_uid,
                    msgid=server_msgid,
                )
            except Exception as exc:
                self.revoke_message_ids.pop(server_msgid, None)
                failures.append(str(exc))
                continue

            reason = self._revoke_failure_reason(response)
            if reason is not None:
                self.revoke_message_ids.pop(server_msgid, None)

                failures.append(reason)

        if failures:
            reason = "; ".join(failures)
            if len(failures) == len(references):
                raise EFBMessageError(f"消息撤回失败：{reason}")
            raise EFBMessageError(f"部分消息撤回失败：{reason}")

    @staticmethod
    def _revoke_failure_reason(response: Any) -> Optional[str]:
        if isinstance(response, dict) and response.get("result") == "OK" and "msg" not in response:
            return "上游不支持撤回消息"
        if not isinstance(response, dict) or str(response.get("msg")) != "1":
            return response.get("err_msg") if isinstance(response, dict) else response
        return None

    def stop_polling(self):
        with self.mark_as_read_lock:
            timers = list(self.mark_as_read_timers.values())
            self.mark_as_read_timers.clear()
        for timer in timers:
            timer.cancel()
        self.db.stop_worker()

    def get_message_by_id(self, chat: 'Chat', msg_id: MessageID) -> Optional['Message']:
        ...

    def get_name_by_wxid(self, wxid):
        contact = self.get_contact_by_wxid(wxid)
        if not contact:
            return wxid
        nickname = contact["nickname"]
        remark = contact["remark"]
        if remark:
            return f"{remark}({nickname})"
        return nickname or wxid

    @staticmethod
    def non_blocking_lock_wrapper(lock: threading.Lock) :
        def wrapper(func):
            def inner(*args, **kwargs):
                if not lock.acquire(False):
                    return
                try:
                    return func(*args, **kwargs)
                finally:
                    lock.release()
            return inner
        return wrapper

    @non_blocking_lock_wrapper(contact_update_lock)
    def get_me(self):
        self.me = self.bot.GetSelfInfo()["data"]
        self.wxid = self.me["wxId"]

    def query_database(self, db_name: Optional[str] = None, sql: str = "", **params) -> Dict:
        """Prefer dbkey-backed SQLCipher reads, then fall back to native handles."""
        dbkey_result = self.dbkey.query(db_name, sql)
        if dbkey_result is not None:
            return dbkey_result
        if db_name:
            params["db_name"] = db_name
        if sql:
            params["sql"] = sql
        return self.bot.QueryDatabase(**params)

    def get_contact_by_sql(self, wxid: str) -> Optional[List[str]]:
        if not wxid.endswith("@openim"):
            db = "MicroMsg.db"
            sql = f"select UserName,Alias,Remark,NickName,Type from Contact where UserName='{wxid}';"
        else:
            db = "OpenIMContact.db"
            sql = f"select UserName,'' as Alias,Remark,NickName,Type from OpenIMContact where UserName='{wxid}';"
        result = self.query_database(db_name=db, sql=sql)
        data = result.get("data") or []
        if len(data) > 1:
            return data[1]
        return None

    def get_contact_list_by_sql(self) -> Dict:
        contact_data: Dict[str, Dict[str, str]] = {}
        contact_response = self.query_database(
            db_name="MicroMsg.db",
            sql="select UserName,Alias,Remark,NickName,Type from Contact",
        )
        contact_list = contact_response.get("data") or []
        for index in range(1, len(contact_list)):
            wxid = contact_list[index][0]
            contact_data[wxid] = {
                "alias": contact_list[index][1],
                "remark": contact_list[index][2],
                "nickname": contact_list[index][3],
                "type": contact_list[index][4],
            }
        openim_response = self.query_database(
            db_name="OpenIMContact.db",
            sql="select UserName,'' as Alias,Remark,NickName,Type from OpenIMContact",
        )
        openim_list = openim_response.get("data") or []
        for index in range(1, len(openim_list)):
            wxid = openim_list[index][0]
            contact_data[wxid] = {
                "alias": openim_list[index][1],
                "remark": openim_list[index][2],
                "nickname": openim_list[index][3],
                "type": openim_list[index][4],
            }
        return contact_data

    def get_picture_by_sql(self, wxid: str) -> Optional[str]:
        if not wxid.endswith("@openim"):
            sql = f"select usrName,smallHeadImgUrl,bigHeadImgUrl from ContactHeadImgUrl where usrName='{wxid}';"
            result = self.query_database(db_name="MicroMsg.db", sql=sql)
        else:
            sql = f"select UserName,SmallHeadImgUrl,BigHeadImgUrl from OpenIMContact where UserName='{wxid}';"
            result = self.query_database(db_name="OpenIMContact.db", sql=sql)
        try:
            if result["data"][1][2] != "":
                return result["data"][1][2]
            if result["data"][1][1] != "":
                return result["data"][1][1]
            return None
        except Exception:
            return None

    def get_all_group_members_by_sql(self) -> Dict:
        group_data: Dict[str, Dict[str, str]] = {}
        response = self.query_database(
            db_name="MicroMsg.db",
            sql="select ChatRoomName,RoomData from ChatRoom",
        )
        member_list = response.get("data") or []
        chatroom = ChatRoom.ChatRoomData()
        for index in range(1, len(member_list)):
            group_member = {}
            chatroom.ParseFromString(bytes(base64.b64decode(member_list[index][1])))
            for member in chatroom.members:
                group_member[member.wxID] = member.displayName or ""
            group_data[member_list[index][0]] = group_member
        return group_data

    def get_group_alias_by(self, group_wxid, member_wxid):
        return self.group_members.get(group_wxid, {}).get(member_wxid) or None

    def get_contact_by_wxid(self, wxid):
        contact = self.contacts.get(wxid)
        if contact is not None:
            return contact

        data = self.get_contact_by_sql(wxid=wxid)
        if not data:
            return None

        contact = {
            "nickname": data[3] or "",
            "remark": data[2] or "",
        }
        self.contacts[wxid] = contact
        return contact

    def is_friend(self, wxid):
        contact = self.get_contact_by_wxid(wxid)
        return bool(contact and contact.get("remark"))

    def get_group_member(self, group_wxid, member_wxid):
        contact = self.get_contact_by_wxid(member_wxid) or {}
        group_alias = self.get_group_alias_by(group_wxid, member_wxid)
        if self.is_friend(member_wxid):
            name = contact.get("remark", "")
        else:
            name = contact.get("nickname") or member_wxid
        return EFBGroupMember(
            uid=member_wxid,
            name=name,
            alias=group_alias,
        )

    def get_nickname_by_wxid(self, wxid):
        contact = self.get_contact_by_wxid(wxid)
        return contact["nickname"] if contact and contact["nickname"] else wxid

    #定时更新 Start
    @non_blocking_lock_wrapper(contact_update_lock)
    def GetContactListBySql(self):
        new_chats = []
        modified_chats = []
        contacts = self.get_contact_list_by_sql()
        for contact in contacts:
            data = contacts[contact]
            self.contacts[contact] = {
                "nickname": data["nickname"] or "",
                "remark": data["remark"] or "",
            }
            name = self.get_name_by_wxid(contact)
            if str(data["type"]) in {"0", "4"}:
                continue

            if "@chatroom" in contact:
                new_entity = EFBGroupChat(
                    uid=contact,
                    name=name
                )
                try:
                    self.get_chat(contact)
                    modified_chats.append(contact)
                except EFBChatNotFound:
                    self.groups.append(ChatMgr.build_efb_chat_as_group(new_entity))
                    new_chats.append(contact)
            else:
                new_entity = EFBPrivateChat(
                    uid=contact,
                    name=name
                )
                try:
                    self.get_chat(contact)
                    modified_chats.append(contact)
                except EFBChatNotFound:
                    self.friends.append(ChatMgr.build_efb_chat_as_private(new_entity))
                    new_chats.append(contact)

        self.GetGroupListBySql()

        if new_chats or modified_chats:
            coordinator.send_status(ChatUpdates(channel=self, new_chats=new_chats, modified_chats=modified_chats))

    def load(self):
        rows = self.db.get_all_group_aliases()
        for r in rows:
            self.group_members[r.group_uid] = self.group_members.get(r.group_uid, {})
            self.group_members[r.group_uid][r.wxid] = r.group_alias

    def merge_group_members(self, group, new_members):
        self.group_members[group] = self.group_members.get(group, {})
        for wxid, alias in new_members.items():
            alias = alias or ""
            if self.group_members[group].get(wxid, None) != alias:
                self.group_members[group][wxid] = alias
                self.db.update_group_alias(group, wxid, alias)

    def GetGroupListBySql(self):
        groups = self.get_all_group_members_by_sql()
        for group, members in groups.items():
            with contextlib.suppress(EFBChatNotFound):
                chat = self.get_chat(group)
                for wxid, alias in members.items():
                    ChatMgr.build_efb_chat_as_member(chat, self.get_group_member(group, wxid))
            self.merge_group_members(group, members)

    def extract_alias(self, msg):
        sender = msg["sender"]
        if "<refermsg>" in msg["message"]:
            xml = etree.fromstring(msg["message"])
            id = xml.xpath('string(/msg/appmsg/refermsg/chatusr)')
            alias = xml.xpath('string(/msg/appmsg/refermsg/displayname)')
            name = self.get_nickname_by_wxid(id)
            if alias and alias != name:
                self.merge_group_members(sender, {
                    id: alias
                })
                return

        if "<atuserlist>" in msg["extrainfo"]:
            xml = etree.fromstring(msg["extrainfo"])
            at_user = xml.xpath('string(/msgsource/atuserlist)')
            user_list = [user for user in at_user.split(",") if user]
            if len(user_list) == 1:
                try:
                    name = self.get_nickname_by_wxid(user_list[0])
                    alias = re.search("^@(.*)\u2005", msg["message"]).group(1)
                    if alias != name:
                        self.merge_group_members(sender, {
                            user_list[0]: alias
                        })
                except:
                    print_exc()
    #定时更新 End

class EmptyJsonResponse:
    def json(self):
        return {}
