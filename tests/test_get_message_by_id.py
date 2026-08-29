import logging
import unittest
from unittest.mock import patch

from ehforwarderbot import MsgType
from ehforwarderbot.chat import PrivateChat
from ehforwarderbot.message import Message

from efb_wechat_comwechat_slave.ComWechat import ComWeChatChannel


class RecordingBot:
    def __init__(self, response):
        self.response = response
        self.calls = []

    def GetChatMsgBySvrId(self, **kwargs):
        self.calls.append(kwargs)
        return self.response


class GetMessageByIdTest(unittest.TestCase):
    def make_channel(self, response):
        channel = ComWeChatChannel.__new__(ComWeChatChannel)
        channel.logger = logging.getLogger("test-get-message-by-id")
        channel.bot = RecordingBot(response)
        channel.direct_transfer = False
        return channel

    def test_converts_original_xml_to_an_efb_message(self):
        channel = self.make_channel({
            "result": "OK",
            "data": {
                "msgid": "123",
                "sender": "wxid_chat",
                "type": "share",
                "xml": "<msg><appmsg><type>57</type></appmsg></msg>",
            },
        })
        chat = PrivateChat(channel=channel, uid="wxid_chat", name="chat")

        converted = Message(type=MsgType.Text, text="converted")
        with patch("efb_wechat_comwechat_slave.ComWechat.MsgProcess", return_value=converted) as process:
            message = channel.get_message_by_id(chat, "123")

        self.assertEqual(channel.bot.calls, [{"msgid": "123"}])
        process.assert_called_once_with(
            {
                "msgid": "123",
                "sender": "wxid_chat",
                "type": "share",
                "xml": "<msg><appmsg><type>57</type></appmsg></msg>",
            },
            chat,
            channel.direct_transfer,
        )
        self.assertIs(message, converted)
        self.assertEqual(message.uid, "123")
        self.assertEqual(message.text, "converted")
        self.assertIs(message.author, chat.other)
        self.assertNotIn("comwechat_info", message.vendor_specific)

    def test_returns_none_when_message_belongs_to_another_chat(self):
        channel = self.make_channel({"result": "OK", "data": {"msgid": "123", "sender": "wxid_other"}})
        chat = PrivateChat(channel=channel, uid="wxid_chat", name="chat")

        self.assertIsNone(channel.get_message_by_id(chat, "123"))


if __name__ == "__main__":
    unittest.main()
