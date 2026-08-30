import ast
import unittest
from pathlib import Path
from typing import Dict, Optional


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "ComWechat.py"


class Message:
    pass


class SelfChatMember:
    pass


class SlaveChannel:
    pass


class MessageType:
    def __init__(self, name):
        self.name = name


class MsgType:
    Image = MessageType("Image")


def load_send_text():
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    function = next(node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == "ComWeChatChannel")
    function = next(node for node in function.body if isinstance(node, ast.FunctionDef) and node.name == "send_text")
    namespace = {
        "ChatID": str,
        "Message": Message,
        "MsgType": MsgType,
        "SelfChatMember": SelfChatMember,
        "SlaveChannel": SlaveChannel,
        "load_message_ids": lambda message_id: str(message_id).split(","),
        "qutoed_text": lambda quoted, text: f"「{quoted}」\\n - - - - - - - - - - - - - - - \\n{text}",
    }
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["send_text"]


def load_send_svrid():
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    channel = next(node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == "ComWeChatChannel")
    function = next(node for node in channel.body if isinstance(node, ast.FunctionDef) and node.name == "_send_svrid")
    function.decorator_list = []
    namespace = {"Dict": Dict, "Optional": Optional, "MessageID": str}
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["_send_svrid"]


class RecordingBot:
    def __init__(self):
        self.texts = []
        self.quotes = []

    def SendText(self, *, wxid, msg):
        self.texts.append((wxid, msg))
        return {"msg": 1, "result": "OK", "svrid": "1234567"}

    def SendQuoteText(self, *, wxid, msg, target_msgid):
        self.quotes.append((wxid, msg, target_msgid))
        return {"msg": 1, "result": "OK", "svrid": "1234567"}


class LegacyRecordingBot:
    def __init__(self):
        self.texts = []

    def SendText(self, *, wxid, msg):
        self.texts.append((wxid, msg))
        return {"msg": 1, "result": "OK", "svrid": "1234567"}


class Channel:
    def __init__(self):
        self.wxid = "wxid-self"
        self.me = {"wxNickName": "自己"}
        self.group_members = {}
        self.bot = RecordingBot()

    @staticmethod
    def _send_svrid(response):
        return str(response["svrid"]) if response.get("result") == "OK" else None


class SelfImageQuoteTest(unittest.TestCase):
    def test_send_response_supplies_server_id_without_downstream_matching(self):
        send_svrid = load_send_svrid()

        self.assertEqual(send_svrid({"msg": 1, "result": "OK", "svrid": "1234567"}), "1234567")
        self.assertIsNone(send_svrid({"msg": 0, "result": "ERROR"}))
        self.assertNotIn("sent_msgs", SOURCE.read_text(encoding="utf-8"))

    def test_reply_to_self_image_uses_native_quote_api(self):
        target = Message()
        target.author = SelfChatMember()
        target.deliver_to = SlaveChannel()
        target.uid = "123456"
        target.type = MsgType.Image
        target.text = ""

        message = Message()
        message.target = target
        message.text = "这是300w的三者"

        channel = Channel()
        svrid = load_send_text()(channel, "friend", message)

        self.assertEqual(channel.bot.texts, [])
        self.assertEqual(channel.bot.quotes, [("friend", "这是300w的三者", "123456")])
        self.assertEqual(svrid, "1234567")

    def test_reply_without_server_message_id_uses_text_fallback(self):
        target = Message()
        target.author = SelfChatMember()
        target.deliver_to = SlaveChannel()
        target.uid = ""
        target.type = MsgType.Image
        target.text = "原消息"

        message = Message()
        message.target = target
        message.text = "回复消息"

        channel = Channel()
        load_send_text()(channel, "friend", message)

        self.assertEqual(channel.bot.quotes, [])
        self.assertEqual(
            channel.bot.texts,
            [("friend", "「原消息」\\n - - - - - - - - - - - - - - - \\n回复消息")],
        )

    def test_reply_uses_text_fallback_without_native_quote_api(self):
        target = Message()
        target.author = SelfChatMember()
        target.deliver_to = SlaveChannel()
        target.uid = "123456"
        target.type = MsgType.Image
        target.text = "原消息"

        message = Message()
        message.target = target
        message.text = "回复消息"

        channel = Channel()
        channel.bot = LegacyRecordingBot()
        load_send_text()(channel, "friend", message)

        self.assertEqual(
            channel.bot.texts,
            [("friend", "「原消息」\\n - - - - - - - - - - - - - - - \\n回复消息")],
        )


if __name__ == "__main__":
    unittest.main()
