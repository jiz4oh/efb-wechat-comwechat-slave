import logging, tempfile
import time
import threading
from traceback import print_exc
from pydub import AudioSegment
import os
import base64
import pickle
from pathlib import Path
from xml.sax.saxutils import escape

import re
import json
import hashlib
from ehforwarderbot.chat import SystemChat, PrivateChat , GroupChat, SystemChatMember, ChatMember, SelfChatMember
from typing import Tuple, Optional, Collection, BinaryIO, Dict, Any , Union , List
from datetime import datetime
from cachetools import TTLCache

from ehforwarderbot import MsgType, Chat, Message, Status, coordinator
from wechatrobot import WeChatRobot

from . import __version__ as version

from ehforwarderbot.channel import SlaveChannel
from ehforwarderbot.types import MessageID, ChatID, InstanceID
from ehforwarderbot import utils as efb_utils
from ehforwarderbot.exceptions import EFBException, EFBChatNotFound
from ehforwarderbot.message import MessageCommand, MessageCommands
from ehforwarderbot.status import MessageRemoval

from .ChatMgr import ChatMgr
from .CustomTypes import EFBGroupChat, EFBPrivateChat, EFBGroupMember, EFBSystemUser
from .MsgDeco import qutoed_text, efb_image_wrapper, efb_file_wrapper, efb_voice_wrapper, efb_video_wrapper, efb_text_simple_wrapper
from .MsgProcess import MsgProcess, MsgWrapper
from .Utils import download_file , load_config , load_temp_file_to_local , WC_EMOTICON_CONVERSION, dump_message_ids, load_message_ids
from .Utils import load_local_file_to_temp, convert_silk_to_mp3
from .Utils import extract_jielong_template
from .Constant import QUOTE_MESSAGE

from rich.console import Console
from rich import print as rprint
from io import BytesIO
from PIL import Image
from typing import Callable

class ComWeChatChannel(SlaveChannel):
    channel_name : str = "ComWechatChannel"
    channel_emoji : str = "💻"
    channel_id : str = "honus.comwechat"
    file_lock_key = "__file_op__"

    bot : WeChatRobot = None
    config : Dict = {}

    friends : EFBPrivateChat = []
    groups : EFBGroupChat    = []

    contacts : Dict = {}            # {wxid : {alias : str , remark : str, nickname : str , type : int}} -> {wxid : name(after handle)}
    group_members : Dict = {}       # {"group_id" : { "wxID" : "displayName"}}

    time_out : int = 120
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
    group_update_lock = threading.Lock()

    @staticmethod
    def update_contacts_wrapper(func):
        def wrapper(self, *args, **kwargs):
            if not self.friends and not self.groups:
                self.get_me()
                self.GetContactListBySql()
                self.GetGroupListBySql()
            return func(self, *args, **kwargs)
        return wrapper

    def __init__(self, instance_id: InstanceID = None):
        super().__init__(instance_id=instance_id)
        self.logger.info("ComWeChat Slave Channel initialized.")
        self.logger.info("Version: %s" % self.__version__)
        self.config = load_config(efb_utils.get_config_path(self.channel_id))
        self.bot = WeChatRobot()

        # Mechanism for waiting for send confirmation
        self.sent_msgs: Dict[str, threading.Event]  = {}
        self.sent_msg_results: Dict[str, MessageID] = {}   # key -> msgid
        self.pending_lock = threading.Lock()
        self._file_locks: Dict[ChatID, threading.Lock] = {} # Locks for file operations per chat
        self._file_locks_lock = threading.Lock() # Lock for accessing _file_locks dict
        self.send_timeout = self.config.get("send_timeout", 15) # Timeout for waiting send confirmation

        self.qr_file = None
        self.wxid = None
        self.base_path = self.config["base_path"] if "base_path" in self.config else self.bot.get_base_path()
        self.dir = self.config["dir"]
        if not self.dir.endswith(os.path.sep):
            self.dir += os.path.sep
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
                    self.GetGroupListBySql()
                return func(*args, **kwargs)
            return wrapper

        @self.bot.on("sent_msg")
        @update_contacts_wrapper
        def on_sent_msg(msg: Dict):
            """Callback for messages sent by the bot (potentially from other devices or API)."""
            self.logger.debug(f"on_sent_msg received: {msg}")
            sender: str = msg.get("sender")
            msgid = msg.get("msgid")
            message_content = msg.get("message")
            filepath = msg.get("filepath")
            msg_type = msg.get("type")

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
            if sender.startswith('gh_'):
                chat.vendor_specific = {'is_mp' : True}
                self.logger.debug(f'modified_chat:{chat}')
            author = chat.other
            self.handle_msg(msg, author, chat)

        self.group_member_lock = threading.Lock()
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
                name = self.contacts[wxid]
            except:
                name = wxid

            if "<atuserlist>" in msg["extrainfo"]:
                at_user = re.search("<atuserlist>(.*)<\/atuserlist>", msg["extrainfo"]).group(1)
                user_list = [user for user in at_user.split(",") if user]
                if len(user_list) == 1:
                    try:
                        alias = msg["message"].split("\u2005", 1)[0].split("@")[-1]
                        if alias != name:
                            self.group_members[sender] = self.group_members.get(sender, {})
                            self.group_members[sender][user_list[0]] = alias
                    except:
                        print_exc()

            author = ChatMgr.build_efb_chat_as_member(chat, EFBGroupMember(
                uid = wxid,
                name = name,
                alias = self.get_group_members(sender).get(wxid , None),
            ))
            self.handle_msg(msg, author, chat)

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
            else:
                chat = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                    uid = sender,
                    name = name,
                ))

            newmsgid = re.search("<newmsgid>(.*?)<\/newmsgid>", msg["message"]).group(1)

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
            apply_content = re.search('content="(.*?)"', msg["message"]).group(1)
            url = re.search('bigheadimgurl="(.*?)"', msg["message"]).group(1)
            v3 = re.search('encryptusername="(v3.*?)"', msg["message"]).group(1)
            v4 = re.search('ticket="(v4.*?)"', msg["message"]).group(1)
            text = (
                "好友申请:\n"
                f"名字: {fromnickname}\n"
                f"验证内容: {apply_content}\n"
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

            content["sender"] = sender
            content["message"] = text
            content["name"] = name
            # if "v3" in username:
            #     content["commands"] = commands
            # 暂时屏蔽
            self.system_msg(content)

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
            print("[red]获取二维码失败[/red]", flush=True)
            tmp_file.close()
            return None
        return tmp_file

    def login_prompt(self):
        file = self.get_qrcode()
        chat = self.user_auth_chat
        author = self.user_auth_chat.other
        msg = Message(
            type=MsgType.Text,
            uid=MessageID(str(int(time.time()))),
        )

        if not file:
            is_login = self.is_login()
            if is_login:
                msg.text = "登录成功"
            else:
                msg.text = "登录失败，未知错误，请使用 /extra 重新尝试登录"
        else:
            msg.commands = MessageCommands([
                MessageCommand(
                    name=("Confirm"),
                    callable_name="confirm_login",
                ),
            ])
            msg.type = MsgType.Image
            msg.path = Path(file.name)
            msg.file = file
            msg.mime = 'image/png'
        self.send_efb_msgs(msg, chat=chat, author=author)

    def confirm_login(self):
        chat = self.user_auth_chat
        author = self.user_auth_chat.other
        msg = Message(
            type=MsgType.Text,
            uid=MessageID(str(int(time.time()))),
        )
        if self.is_login():
            self.get_me()
            self.load()
            self.GetContactListBySql()
            self.GetGroupListBySql()
            msg.text = "登录成功"
        else:
            msg.text = "登录失败，请使用重新登录"
        self.send_efb_msgs(msg, chat=chat, author=author)

    @efb_utils.extra(name="Get QR Code",
           desc="重新扫码登录")
    def reauth(self, _: str = "") -> str:
        self.login_prompt()
        return "扫码成功之后，请点击 confirm 进行下一步"

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

        self.send_efb_msgs(msg, uid=int(time.time()), chat=chat, author=author, type=MsgType.Text)

    def handle_msg(self , msg : Dict[str, Any] , author : 'ChatMember' , chat : 'Chat'):
        emojiList = re.findall('\[[\w|！|!| ]+\]' , msg["message"])
        for emoji in emojiList:
            try:
                msg["message"] = msg["message"].replace(emoji, WC_EMOTICON_CONVERSION[emoji])
            except:
                pass

        if msg["msgid"] not in self.cache:
            self.cache[msg["msgid"]] = msg["type"]
        else:
            if self.cache[msg["msgid"]] == msg["type"]:
                return

        try:
            if ("FileStorage" in msg["filepath"]) and ("Cache" not in msg["filepath"]):
                msg["timestamp"] = int(time.time())
                msg["filepath"] = msg["filepath"].replace("\\","/")
                msg["filepath"] = f'''{self.dir}{msg["filepath"]}'''
                self._send_file_msg(msg , author , chat )
                return
            if msg["type"] == "video":
                msg["timestamp"] = int(time.time())
                msg["filepath"] = msg["thumb_path"].replace("\\","/").replace(".jpg", ".mp4")
                msg["filepath"] = f'''{self.dir}{msg["filepath"]}'''
                self._send_file_msg(msg , author , chat )
                return
        except Exception as e:
            self.logger.warning(f"Failed to process file msg: {e}")
            ...

        if msg["type"] == "voice":
            file_path = re.search("clientmsgid=\"(.*?)\"", msg["message"]).group(1) + ".amr"
            msg["timestamp"] = int(time.time())
            msg["filepath"] = f'''{self.dir}{msg["self"]}/{file_path}'''
            self._send_file_msg(msg , author , chat )
            return

        self.send_efb_msgs(MsgWrapper(msg, MsgProcess(msg, chat)), author=author, chat=chat, uid=MessageID(str(msg['msgid'])))

    def handle_file_msg(self):
        while True:
            if len(self.file_msg) == 0:
                time.sleep(1)
            else:
                for path in list(self.file_msg.keys()):
                    flag = False
                    msg = self.file_msg[path][0]
                    author: ChatMember = self.file_msg[path][1]
                    chat : Chat= self.file_msg[path][2]
                    commands = []
                    msg_type = msg["type"]
                    if os.path.exists(path):
                        flag = True
                    elif (int(time.time()) - msg["timestamp"]) > self.time_out:
                        msg['message'] = f"[{msg_type} 下载超时,请在手机端查看]"
                        msg["type"] = "text"
                        chattype = "Unknown"
                        if isinstance(chat, GroupChat):
                            chattype = "group"
                        elif isinstance(chat, PrivateChat):
                            chattype = "private"
                        commands.append(
                            MessageCommand(
                                name=("Retry"),
                                callable_name="retry_download",
                                kwargs={
                                    "msgid": msg["msgid"],
                                    "msgtype": msg_type,
                                    "chattype": chattype,
                                    "chatuid": chat.uid,
                                },
                            )
                        )
                        flag = True
                    elif msg["type"] == "voice":
                        sql = f'SELECT Buf FROM Media WHERE Reserved0 = {msg["msgid"]}'
                        dbresult = self.bot.QueryDatabase(db_handle=self.bot.GetDBHandle("MediaMSG0.db"), sql=sql)["data"]
                        if len(dbresult) == 2:
                            filebuffer = dbresult[1][0]
                            decoded = bytes(base64.b64decode(filebuffer))
                            with open(msg["filepath"], 'wb') as f:
                                f.write(decoded)
                            f.close()
                            flag = True

                    if flag:
                        m = MsgWrapper(msg, MsgProcess(msg, chat))[0]
                        m.edit = True
                        m.edit_media = True
                        if commands: 
                            m.commands = MessageCommands(commands)
                        m.vendor_specific["wechat_msgtype"] = msg_type
                        del self.file_msg[path]
                        self.send_efb_msgs(m, author=author, chat=chat, uid=MessageID(str(msg['msgid'])))

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

    def _send_file_msg(self, msg: Message, author: ChatMember, chat: Chat):
        # text = f"{msg['type']} is downloading, please wait..."
        # efb_msg = Message(
        #     type=MsgType.Text,
        #     text=text
        # )
        # self.send_efb_msgs(efb_msg, author=author, chat=chat, uid=MessageID(str(msg['msgid'])))
        self.file_msg[msg["filepath"]] = ( msg , author , chat )

    def retry_download(self, msgid, msgtype, chattype, chatuid):
        path = self.GetMsgCdn(msgid)
        efb_msgs = self._build_media_msg(msgtype, path)
        if not efb_msgs:
            return f"[下载失败]"
        efb_msgs = [efb_msgs] if isinstance(efb_msgs, Message) else efb_msgs
        if chattype == "group":
            c = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
                uid = chatuid,
            ))
        elif chattype == "private":
            c = ChatMgr.build_efb_chat_as_private(EFBPrivateChat(
                uid = chatuid
            ))
        else:
            return f"[unsupported chat type: {chattype}]"
        master_message = coordinator.master.get_message_by_id(chat=c, msg_id=msgid)
        self.send_efb_msgs(efb_msgs, uid=msgid, author=master_message.author, chat=master_message.chat, edit=True, edit_media=True)
        return "下载成功"

    def retry_download_target(self, target: Message = None):
        path = self.GetMsgCdn(target.uid)
        if target.type == MsgType.Image:
            msgtype = "image"
        elif target.type == MsgType.File:
            msgtype = "share"
        elif target.type == MsgType.Voice:
            msgtype = "voice"
        elif target.type == MsgType.Video:
            msgtype = "video"
        else:
            msgtype = target.vendor_specific.get("wechat_msgtype", None)
        efb_msgs = self._build_media_msg(msgtype, path)
        if not efb_msgs:
            return
        efb_msgs = [efb_msgs] if isinstance(efb_msgs, Message) else efb_msgs

        author = target.author
        chat = target.chat
        self.send_efb_msgs(efb_msgs, uid=target.uid, author=author, chat=chat, edit=True, edit_media=True)

    def _build_media_msg(self, msgtype, path):
        if not path:
            return efb_text_simple_wrapper(f"[重试 {msgtype} 失败,请在手机端查看,可通过 /retry 回复本条消息再次重试]")
        file = load_local_file_to_temp(path)
        filename = os.path.basename(path)
        if msgtype == "image":
            return efb_image_wrapper(file, filename=filename)
        elif msgtype == "share":
            return efb_file_wrapper(file, filename=filename)
        elif msgtype == "voice":
            return efb_voice_wrapper(convert_silk_to_mp3(file) , file.name + ".ogg")
        elif msgtype == "video":
            return efb_video_wrapper(file, filename=filename)
        else:
            self.logger.warn(f"[unsupported type: {msgtype}]")
            return

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
                    self.GetGroupListBySql()
                    self.GetContactListBySql()
            if count % 1800 == 3:
                if getattr(coordinator, 'master', None) is not None and not self.is_login():
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
                self.load()
                self.GetContactListBySql()
                self.GetGroupListBySql()
            else:
                content = {
                    "name": self.channel_name,
                    "sender": self.channel_name,
                    "message": "尚未登录，请发送 /extra 扫码登录"
                }
                self.system_msg(content)
                return msg

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
                    try:
                        name = self.contacts[wxid]
                    except:
                        try:
                            nickname = self.bot.GetChatroomMemberNickname(chatroom_id = chat_uid, wxid = wxid)['nickname']
                            name = nickname or wxid
                            self.group_members[chat_uid] = self.group_members[chat_uid] or {}
                            self.group_members[chat_uid][wxid] = nickname
                        except:
                            name = wxid
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
            elif msg.text.startswith('/+1'):
                if isinstance(msg.target, Message):
                    template = extract_jielong_template(msg.target.text)
                    if template:
                        message = msg.text[4::]
                        self.plus_one(template, chat_uid, message)
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
                    if keyword in value:
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
                    msg_ids.append(self.send_text(chat_uid, msg.text))
            elif msg.text.startswith('/retry'):
                if isinstance(msg.target, Message):
                    self.retry_download_target(target=msg.target)
                    return msg
                else:
                    message = "回复超时消息时使用"
                    self.system_msg({'sender':chat_uid, 'message':message})
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
        elif msg.type in [MsgType.Animation, MsgType.Sticker]:
            msg_ids.append(self.send_emotion(chat_uid, msg))
            if msg.text:
                msg_ids.append(self.send_text(chat_uid, msg))

        ids = [item for item in msg_ids if item is not None]
        if not (str(res.get("msg", "1")) == "0" or ids):
            self.logger.warning(f"Failed to get msgid confirmation for message type {msg.type} to {chat_uid} with {msg.uid}")
            if "@openim" in chat_uid:  # 上游 bug，永远不返回企业微信的 msgid
                return msg
            target = Message(
                uid=MessageID(msg.uid),
                chat=msg.chat,
            )
            self.system_msg({'sender': chat_uid, 'message':f"发送消息失败，请在手机端确认", 'target': target})
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
        key = None

        if isinstance(msg.target, Message) and text_to_send:
            msgid = msg.target.uid
            if isinstance(msg.target.author, SelfChatMember):
                displayname = self.me["wxNickName"]
                sender = self.wxid
            else:
                sender = msg.target.author.uid
                displayname = msg.target.author.name
            ids = load_message_ids(msgid)
            # 因为微信会将视频/文件等拆分成多条消息，默认使用第一条做回复目标，如果是视频 + 文本，则回复视频
            msgid = ids[0]
            content = escape(msg.target.vendor_specific.get("wx_xml", ""), {
                "\n": "&#x0A;",
                "\t": "&#x09;",
                '"': "&quot;",
            }) or msg.target.text
            comwechat_info = msg.target.vendor_specific.get("comwechat_info", {})
            if comwechat_info.get("type", None) == "animatedsticker":
                refer_type = 47
            elif msg.target.type == MsgType.Image:
                refer_type = 3
            elif msg.target.type == MsgType.Voice:
                refer_type = 34
            elif msg.target.type == MsgType.Video:
                refer_type = 43
            elif msg.target.type == MsgType.Sticker:
                refer_type = 47
            elif msg.target.type == MsgType.Location:
                refer_type = 48
            elif msg.target.type == MsgType.File:
                refer_type = 49
            elif comwechat_info.get("type", None) == "share":
                refer_type = 49
            else:
                refer_type = 1
            if content:
                content = "<content>%s</content>" % content
            else:
                content = "<content />"
            xml = QUOTE_MESSAGE % (self.wxid, text_to_send, refer_type, msgid, sender, sender, displayname, content)
            key = (wxid, xml)
            with self.pending_lock:
                self.sent_msgs[key] = threading.Event()
            self.bot.SendXml(wxid=wxid, xml=xml, img_path="")
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
        result = self.bot.GetPictureBySql(wxid = wxid)
        if result:
            return download_file(result)
        else:
            return None

    def get_chat_member_picture(self, chat_member: 'ChatMember') -> Optional[BinaryIO]:
        wxid = chat_member.uid
        result = self.bot.GetPictureBySql(wxid = wxid)
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
        #TODO 撤回消息
        #self.bot.SendXml(wxid=wxid, xml=xml, img_path="")
        ...

    def stop_polling(self):
        ...

    def get_message_by_id(self, chat: 'Chat', msg_id: MessageID) -> Optional['Message']:
        ...

    def get_name_by_wxid(self, wxid):
        try:
            name = self.contacts[wxid]
            if name == "":
                name = wxid
        except:
            data = self.bot.GetContactBySql(wxid = wxid)
            if data:
                name = data[3]
                if name == "":
                    name = wxid
            else:
                name = wxid
        return name

    def GetMsgCdn(self, msgid):
        try:
            res = self.bot.GetCdn(msgid=msgid)
            if res["msg"] == 1:
                path = res["path"].replace("\\","/").replace("C:/users/user/My Documents/WeChat Files/", self.dir )
                count = 1
                while True:
                    if os.path.exists(path):
                        break
                    elif count > 12:  # telegram 超过 15s 会报错
                        self.logger.warning(f"Timeout when retrying download {msgid} at {path}.")
                        return
                    count += 1
                    time.sleep(1)

                self.logger.debug(f"Download {path} successfully.")
                return path
        except Exception as e:
            self.logger.warning(f"Error occurred when retrying download {msgid}. {e}")

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
        self.name = self.me["wxNickName"]
        self.wxid = self.me["wxId"]

    #定时更新 Start
    @non_blocking_lock_wrapper(contact_update_lock)
    def GetContactListBySql(self):
        contacts = self.bot.GetContactListBySql()
        for contact in contacts:
            data = contacts[contact]
            name = (f"{data['remark']}({data['nickname']})") if data["remark"] else data["nickname"]

            self.contacts[contact] = name
            if data["type"] == 0 or data["type"] == 4:
                continue

            if "@chatroom" in contact:
                new_entity = EFBGroupChat(
                    uid=contact,
                    name=name
                )
                self.groups.append(ChatMgr.build_efb_chat_as_group(new_entity))
            else:
                new_entity = EFBPrivateChat(
                    uid=contact,
                    name=name
                )
                self.friends.append(ChatMgr.build_efb_chat_as_private(new_entity))

    def dump(self):
        data = {
            "group_memebers": self.group_members
        }
        file = self.base_path + "\\" + self.wxid + "\\comwechat.efb.pkl"
        with open(file,"wb") as f:
            pickle.dump(data, f)

    def load(self):
        file = self.base_path + "\\" + self.wxid + "\\comwechat.efb.pkl"
        if os.path.exists(file):
            with open(file, 'rb') as fp:
                data = pickle.load(fp)
                self.group_members = data.get("group_memebers", {})

    def get_group_members(self, sender):
        members = self.group_members.get(sender, None)
        if members is None:
           if self.group_member_lock.acquire(False):
                members = self.bot.GetGroupMembersBySql(sender)
                self.merge_group_members(sender, members)
                self.group_member_lock.release()
           else:
                return {}
        return members

    def merge_group_members(self, group, new_members):
        is_updated = False
        for wxid, alias in members.items():
            if self.group_members[group].get(wxid, None) != alias:
                self.group_members[group][wxid] = alias
                is_updated = True
        if is_updated:
            self.dump()

    @non_blocking_lock_wrapper(group_update_lock)
    def GetGroupListBySql(self):
        groups = self.bot.GetAllGroupMembersBySql()
        for group, members in groups.items():
            self.group_members[group] = self.group_members.get(group, {})
            self.merge_group_members(group, members)
        for group in self.groups:
            for wxid, alias in self.group_members.get(group.uid, {}).items():
                name = self.get_name_by_wxid(wxid)
                try:
                    m = group.get_member(wxid)
                    if name != wxid:
                        m.name = name
                except KeyError:
                    m = group.add_member(uid=wxid, name=name)
                if alias != m.name:
                    m.alias = alias
                    continue
    #定时更新 End

    def plus_one(self, template, sender, placeholder = ""):
        alias = self.group_members.get(sender,{}).get(self.wxid, None)

        text = template.format(placeholder=f"{alias or self.name} {placeholder}")
        efb_msg = Message(
            type=MsgType.Text,
            text=text
        )
        msgid = self.send_text(sender, efb_msg)
        chatname = self.get_name_by_wxid(sender)

        chat = ChatMgr.build_efb_chat_as_group(EFBGroupChat(
            uid = sender,
            name = chatname,
        ))

        self.send_efb_msgs(efb_msg, uid=msgid or int(time.time()), chat=chat, author=chat.self)
        return ""

class EmptyJsonResponse:
    def json(self):
        return {}
