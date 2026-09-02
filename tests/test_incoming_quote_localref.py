import ast
import unittest
from pathlib import Path
from typing import Callable, List


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "MsgDeco.py"


class Message:
    def __init__(self, **kwargs):
        self.__dict__.update(kwargs)


class MessageType:
    Text = "text"


class FakeXml:
    values = {
        "/msg/appmsg/type/text()": "57",
        "/msg/appmsg/title/text()": "123 回复",
        "/msg/appmsg/refermsg/type/text()": "1",
        "/msg/appmsg/refermsg/svrid/text()": "456",
        "/msg/appmsg/refermsg/fromusr/text()": "wxid-chat",
        "/msg/appmsg/refermsg/chatusr/text()": "wxid-other",
        "/msg/appmsg/refermsg/displayname/text()": "他人",
        "/msg/appmsg/refermsg/content/text()": "ETM 原消息",
    }

    def xpath(self, path):
        value = self.values.get(path)
        return [] if value is None else [value]


class FakeEtree:
    @staticmethod
    def fromstring(_text):
        return FakeXml()


class ChatMgr:
    @staticmethod
    def build_efb_chat_as_group(chat):
        return chat

    @staticmethod
    def build_efb_chat_as_private(chat):
        return chat


class EFBGroupChat(dict):
    pass


class EFBPrivateChat(dict):
    pass


class Master:
    def __init__(self, recorded_reference=None):
        self.recorded_reference = recorded_reference
        self.calls = []

    def get_message_by_id(self, *, chat, msg_id):
        self.calls.append(str(msg_id))
        if str(msg_id) == self.recorded_reference:
            return object()
        return None


class Coordinator:
    def __init__(self, recorded_reference=None):
        self.master = Master(recorded_reference)


def load_share_wrapper(coordinator):
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    function = next(
        node
        for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "efb_share_link_wrapper"
    )
    namespace = {
        "Callable": Callable,
        "List": List,
        "MessageID": str,
        "Message": Message,
        "MsgType": MessageType,
        "coordinator": coordinator,
        "etree": FakeEtree,
        "ChatMgr": ChatMgr,
        "EFBGroupChat": EFBGroupChat,
        "EFBPrivateChat": EFBPrivateChat,
        "qutoed_text": lambda quoted, text, prefix="": f"{prefix}{quoted}|{text}",
        "print_exc": lambda: None,
    }
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["efb_share_link_wrapper"]


class IncomingQuoteLocalRefTest(unittest.TestCase):
    message = {
        "message": "<msg />",
        "sender": "wxid-chat",
        "self": "wxid-self",
    }

    def test_other_sender_reply_to_etm_message_uses_localref_target(self):
        coordinator = Coordinator(recorded_reference="local:1:123")
        wrapper = load_share_wrapper(coordinator)

        result = wrapper(
            self.message,
            chat=object(),
            message_reference_resolver=lambda _svrid: ["456", "local:1:123"],
        )

        self.assertEqual(coordinator.master.calls, ["456", "local:1:123"])
        self.assertEqual(result.target.uid, "local:1:123")
        self.assertEqual(result.text, "123 回复")

    def test_unrecorded_reference_stays_as_quoted_text(self):
        coordinator = Coordinator()
        wrapper = load_share_wrapper(coordinator)

        result = wrapper(
            self.message,
            chat=object(),
            message_reference_resolver=lambda _svrid: ["456", "local:1:123"],
        )

        self.assertEqual(coordinator.master.calls, ["456", "local:1:123"])
        self.assertFalse(hasattr(result, "target"))
        self.assertEqual(result.text, "他人:ETM 原消息|123 回复")


if __name__ == "__main__":
    unittest.main()
