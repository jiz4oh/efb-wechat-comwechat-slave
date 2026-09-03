import hashlib
import logging
import threading
import unittest

from cachetools import TTLCache
from ehforwarderbot import MsgType
from ehforwarderbot.chat import PrivateChat
from ehforwarderbot.exceptions import EFBMessageError
from ehforwarderbot.message import Message
from ehforwarderbot.status import MessageRemoval

from efb_wechat_comwechat_slave.ComWechat import ComWeChatChannel
from efb_wechat_comwechat_slave.Utils import dump_message_ids, load_message_ids


class RecordingBot:
    def __init__(self, response=None):
        self.response = response or {"msg": 1, "result": "OK"}
        self.calls = []

    def RevokeMessage(self, **kwargs):
        self.calls.append(kwargs)
        return self.response


class SendingBot(RecordingBot):
    def __init__(self, channel):
        super().__init__()
        self.channel = channel

    def SendText(self, *, wxid, msg):
        for event_key, event in self.channel.sent_msgs.items():
            self.channel.sent_msg_results[event_key] = "123"
            event.set()
        return {"msg": 1, "result": "OK", "localref": "local:1:123"}


class EditingBot(RecordingBot):
    def __init__(self, response=None):
        super().__init__(response)
        self.events = []
        self.next_id = 900

    def RevokeMessage(self, **kwargs):
        self.events.append(("revoke", kwargs))
        return super().RevokeMessage(**kwargs)

    def SendText(self, *, wxid, msg):
        self.events.append(("text", {"wxid": wxid, "msg": msg}))
        self.next_id += 1
        return {
            "msg": 1,
            "result": "OK",
            "localref": f"local:1:{self.next_id}",
        }


class RevokeTest(unittest.TestCase):
    def make_channel(self, response=None):
        channel = ComWeChatChannel.__new__(ComWeChatChannel)
        channel.logger = logging.getLogger("test-revoke")
        channel.pending_lock = threading.Lock()
        channel.sent_msgs = {}
        channel.sent_msg_results = {}
        channel.cache = TTLCache(maxsize=200, ttl=300)
        channel.file_lock_key = "__file_op__"
        channel.revoke_message_ids = TTLCache(maxsize=200, ttl=300)
        channel.bot = RecordingBot(response)
        return channel

    def make_message(self, channel, uid):
        chat = PrivateChat(channel=channel, uid="wxid-chat", name="chat")
        return Message(chat=chat, uid=uid)

    def test_send_message_returns_local_uids(self):
        channel = self.make_channel()
        channel.bot = SendingBot(channel)
        channel.wxid = "wxid-self"
        channel.mark_as_read_enabled = False
        channel.send_timeout = 1
        message = Message(
            chat=PrivateChat(channel=channel, uid="wxid-chat", name="chat"),
            text="hello",
            type=MsgType.Text,
        )

        channel.send_message(message)

        self.assertEqual(message.uid, "local:1:123")

    def make_edit_channel(self, response=None):
        channel = self.make_channel(response)
        channel.bot = EditingBot(response)
        channel.wxid = "wxid-self"
        channel.mark_as_read_enabled = False
        return channel

    def make_edit_message(self, channel, uid, text="", message_type=MsgType.Text, edit_media=False):
        return Message(
            chat=PrivateChat(channel=channel, uid="wxid-chat", name="chat"),
            uid=uid,
            text=text,
            type=message_type,
            edit=True,
            edit_media=edit_media,
        )

    def test_edit_retracts_all_references_before_resending(self):
        channel = self.make_edit_channel()
        message = self.make_edit_message(channel, "123,124", text="edited")

        channel.send_message(message)

        self.assertEqual(channel.bot.events, [
            ("revoke", {"wxid": "wxid-chat", "msgid": "123"}),
            ("revoke", {"wxid": "wxid-chat", "msgid": "124"}),
            ("text", {"wxid": "wxid-chat", "msg": "edited"}),
        ])
        self.assertEqual(message.uid, "local:1:901")

    def test_editing_media_caption_retracts_only_caption(self):
        channel = self.make_edit_channel()
        message = self.make_edit_message(
            channel,
            "local:1:10,local:1:11",
            text="new caption",
            message_type=MsgType.Image,
        )

        channel.send_message(message)

        self.assertEqual(channel.bot.events, [
            ("revoke", {"wxid": "wxid-chat", "msgid": "local:1:11"}),
            ("text", {"wxid": "wxid-chat", "msg": "new caption"}),
        ])
        self.assertEqual(message.uid, "local:1:10,local:1:901")

    def test_editing_media_without_caption_keeps_media_reference(self):
        channel = self.make_edit_channel()
        message = self.make_edit_message(
            channel,
            "local:1:10,local:1:11",
            message_type=MsgType.Image,
        )

        channel.send_message(message)

        self.assertEqual(channel.bot.events, [
            ("revoke", {"wxid": "wxid-chat", "msgid": "local:1:11"}),
        ])
        self.assertEqual(message.uid, "local:1:10")

    def test_editing_media_with_edit_media_resends_media(self):
        channel = self.make_edit_channel()

        def send_image(wxid, message):
            channel.bot.events.append(("image", {"wxid": wxid}))
            return "local:1:902"

        channel.send_image = send_image
        message = self.make_edit_message(
            channel,
            "local:1:10",
            message_type=MsgType.Image,
            edit_media=True,
        )

        channel.send_message(message)

        self.assertEqual(channel.bot.events, [
            ("revoke", {"wxid": "wxid-chat", "msgid": "local:1:10"}),
            ("image", {"wxid": "wxid-chat"}),
        ])
        self.assertEqual(message.uid, "local:1:902")

    def test_edit_rejects_commands_before_retracting(self):
        channel = self.make_edit_channel()
        message = self.make_edit_message(channel, "123", text="/search edited")

        with self.assertRaisesRegex(EFBMessageError, "不支持编辑命令消息"):
            channel.send_message(message)

        self.assertEqual(channel.bot.events, [])

    def test_edit_rejects_missing_or_invalid_uid(self):
        for uid in (None, "abc"):
            with self.subTest(uid=uid):
                channel = self.make_edit_channel()
                message = self.make_edit_message(channel, uid, text="edited")

                with self.assertRaises(EFBMessageError):
                    channel.send_message(message)

                self.assertEqual(channel.bot.events, [])

    def test_edit_does_not_resend_when_retract_fails(self):
        channel = self.make_edit_channel({
            "msg": 0,
            "result": "ERROR",
            "err_msg": "revoke message failed",
        })
        message = self.make_edit_message(channel, "123", text="edited")

        with self.assertRaisesRegex(EFBMessageError, "消息撤回失败"):
            channel.send_message(message)

        self.assertEqual(channel.bot.events, [
            ("revoke", {"wxid": "wxid-chat", "msgid": "123"}),
        ])

    def test_editing_forward_marker_sends_text_instead_of_forwarding(self):
        channel = self.make_edit_channel()
        marker = hashlib.md5(channel.channel_id.encode("utf-8")).hexdigest()
        message = self.make_edit_message(
            channel,
            "123",
            text=f"ehforwarderbot://{marker}/forward/456",
        )

        channel.send_message(message)

        self.assertEqual(channel.bot.events[-1], (
            "text",
            {"wxid": "wxid-chat", "msg": f"ehforwarderbot://{marker}/forward/456"},
        ))

    def test_comma_delimited_uid_recalls_every_server_id(self):
        channel = self.make_channel()
        uid = dump_message_ids(["123", "124"])

        channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, uid)))

        self.assertEqual(channel.bot.calls, [
            {"wxid": "wxid-chat", "msgid": "123"},
            {"wxid": "wxid-chat", "msgid": "124"},
        ])
        self.assertTrue(channel.revoke_message_ids["123"])
        self.assertTrue(channel.revoke_message_ids["124"])

    def test_failed_revoke_request_removes_feedback_suppression_marker(self):
        class FailingBot(RecordingBot):
            def RevokeMessage(self, **kwargs):
                raise RuntimeError("network")

        channel = self.make_channel()
        channel.bot = FailingBot()

        with self.assertRaisesRegex(EFBMessageError, "消息撤回失败"):
            channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "123")))

        self.assertNotIn("123", channel.revoke_message_ids)

    def test_upstream_revoke_failure_reports_reason(self):
        channel = self.make_channel({
            "msg": 0,
            "result": "ERROR",
            "err_msg": "revoke message failed",
        })

        with self.assertRaisesRegex(EFBMessageError, "消息撤回失败.*revoke message failed"):
            channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "123")))

        self.assertNotIn("123", channel.revoke_message_ids)

    def test_upstream_without_revoke_result_is_unsupported(self):
        channel = self.make_channel({"result": "OK"})

        with self.assertRaisesRegex(EFBMessageError, "上游不支持撤回消息"):
            channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "123")))

        self.assertNotIn("123", channel.revoke_message_ids)

    def test_failed_revoke_call_is_upstream_failure(self):
        class FailingBot(RecordingBot):
            def RevokeMessage(self, **kwargs):
                raise RuntimeError("some network error")

        channel = self.make_channel()
        channel.bot = FailingBot()

        with self.assertRaisesRegex(EFBMessageError, "消息撤回失败.*some network error"):
            channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "123")))

        self.assertNotIn("123", channel.revoke_message_ids)

    def test_duplicate_server_ids_are_recalled_once(self):
        channel = self.make_channel()

        channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "123,123")))

        self.assertEqual(len(channel.bot.calls), 1)

    def test_partial_failure_reports_remaining_reasons(self):
        class PartiallyFailingBot(RecordingBot):
            def RevokeMessage(self, **kwargs):
                self.calls.append(kwargs)
                if kwargs["msgid"] == "123":
                    return {"msg": 1, "result": "OK"}
                return {"msg": 0, "result": "ERROR", "err_msg": "revoke message failed"}

        channel = self.make_channel()
        channel.bot = PartiallyFailingBot()

        with self.assertRaisesRegex(EFBMessageError, "部分消息撤回失败.*revoke message failed"):
            channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "123,124")))

        self.assertEqual(channel.bot.calls, [
            {"wxid": "wxid-chat", "msgid": "123"},
            {"wxid": "wxid-chat", "msgid": "124"},
        ])
        self.assertIn("123", channel.revoke_message_ids)
        self.assertNotIn("124", channel.revoke_message_ids)

    def test_nondecimal_server_id_is_rejected(self):
        channel = self.make_channel()

        with self.assertRaises(EFBMessageError):
            channel.send_status(MessageRemoval(channel, channel, self.make_message(channel, "abc")))

        self.assertEqual(channel.bot.calls, [])

    def test_message_id_helpers_preserve_old_and_new_formats(self):
        self.assertEqual(load_message_ids(dump_message_ids(["123"])), ["123"])
        self.assertEqual(load_message_ids("123,456"), ["123", "456"])


if __name__ == "__main__":
    unittest.main()
