import ast
import threading
import unittest
from pathlib import Path


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
        "threading": threading,
        "load_message_ids": lambda message_id: str(message_id).split(","),
    }
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["send_text"]


class RecordingBot:
    def __init__(self):
        self.texts = []
        self.quotes = []

    def SendText(self, *, wxid, msg):
        self.texts.append((wxid, msg))

    def SendQuoteText(self, *, wxid, msg, target_msgid):
        self.quotes.append((wxid, msg, target_msgid))


class Channel:
    def __init__(self):
        self.wxid = "wxid-self"
        self.me = {"wxNickName": "自己"}
        self.group_members = {}
        self.sent_msgs = {}
        self.pending_lock = threading.Lock()
        self.send_timeout = 1
        self.bot = RecordingBot()

    def _wait(self, key, timeout):
        return key


class SelfImageQuoteTest(unittest.TestCase):
    def test_reply_to_self_image_uses_native_quote_api(self):
        target = Message()
        target.author = SelfChatMember()
        target.deliver_to = SlaveChannel()
        target.uid = "123456"
        target.type = MsgType.Image
        target.text = ""
        target.vendor_specific = {"comwechat_info": {}}

        message = Message()
        message.target = target
        message.text = "这是300w的三者"

        channel = Channel()
        load_send_text()(channel, "friend", message)

        self.assertEqual(channel.bot.texts, [])
        self.assertEqual(channel.bot.quotes, [("friend", "这是300w的三者", "123456")])


if __name__ == "__main__":
    unittest.main()
