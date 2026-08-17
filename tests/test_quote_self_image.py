import ast
import threading
import unittest
from pathlib import Path
from xml.sax.saxutils import escape


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
        "escape": escape,
        "threading": threading,
        "load_message_ids": lambda message_id: str(message_id).split(","),
        "QUOTE_MESSAGE": (
            "<fromusername>%s</fromusername><appmsg><title>%s</title>"
            "<type>57</type><refermsg><type>%d</type><svrid>%s</svrid>"
            "<fromusr>%s</fromusr><chatusr>%s</chatusr>"
            "<displayname>%s</displayname>%s</refermsg></appmsg>"
        ),
    }
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["send_text"]


class RecordingBot:
    def __init__(self):
        self.texts = []
        self.xmls = []

    def SendText(self, *, wxid, msg):
        self.texts.append((wxid, msg))

    def SendXml(self, *, wxid, xml, img_path):
        self.xmls.append((wxid, xml, img_path))


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
    def test_reply_to_self_image_sends_wechat_quote_xml(self):
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
        self.assertEqual(len(channel.bot.xmls), 1)
        xml = channel.bot.xmls[0][1]
        self.assertIn("<type>57</type>", xml)
        self.assertIn("<type>3</type>", xml)
        self.assertIn("<svrid>123456</svrid>", xml)


if __name__ == "__main__":
    unittest.main()
