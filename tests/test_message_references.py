import logging
import unittest

from cachetools import TTLCache
from ehforwarderbot.chat import PrivateChat
from ehforwarderbot.message import Message
from ehforwarderbot.status import MessageRemoval

from efb_wechat_comwechat_slave.ComWechat import ComWeChatChannel
from efb_wechat_comwechat_slave.Utils import is_message_reference


class RecordingBot:
    def __init__(self):
        self.calls = []

    def GetChatMsgBySvrId(self, **kwargs):
        return {
            "result": "OK",
            "data": {"msgid": kwargs["msgid"], "localref": "local:7:123"},
        }

    def RevokeMessage(self, **kwargs):
        self.calls.append(kwargs)
        return {"msg": 1, "result": "OK"}


class MessageReferenceTest(unittest.TestCase):
    def make_channel(self):
        channel = ComWeChatChannel.__new__(ComWeChatChannel)
        channel.logger = logging.getLogger("test-message-references")
        channel.bot = RecordingBot()
        channel.dbkey = type("DbKey", (), {"database_names": lambda _self, _prefix: ["MSG0.db"]})()
        channel.query_database = lambda **_kwargs: {"result": "OK", "data": [["localId"], ["123"]]}
        channel.revoke_message_ids = TTLCache(maxsize=20, ttl=30)
        return channel

    def test_validates_server_and_local_references(self):
        self.assertTrue(is_message_reference("123"))
        self.assertTrue(is_message_reference("local:7:123"))
        self.assertFalse(is_message_reference("0"))
        self.assertFalse(is_message_reference("local:0:123"))
        self.assertFalse(is_message_reference("local:7:0"))
        self.assertFalse(is_message_reference("local:7"))

    def test_send_response_prefers_server_id_then_local_reference(self):
        parse = ComWeChatChannel._send_message_reference

        self.assertEqual(parse({"result": "OK", "svrid": "456"}), None)
        self.assertEqual(parse({"result": "OK", "localref": "local:7:123"}), "local:7:123")
        self.assertIsNone(parse({"result": "ERROR", "localref": "local:7:123"}))

    def test_resolves_server_feedback_to_local_reference_from_database(self):
        channel = self.make_channel()

        self.assertEqual(channel._message_references("456"), ["456", "local:1:123"])
        self.assertEqual(channel.bot.calls, [])

    def test_revoke_passes_local_reference_to_native(self):
        channel = self.make_channel()
        chat = PrivateChat(channel=channel, uid="wxid-chat", name="chat")
        message = Message(chat=chat, uid="local:7:123")

        channel.send_status(MessageRemoval(channel, channel, message))

        self.assertEqual(channel.bot.calls, [{"wxid": "wxid-chat", "msgid": "local:7:123"}])


if __name__ == "__main__":
    unittest.main()
