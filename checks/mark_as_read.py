import ast
import threading
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Dict
from unittest.mock import Mock


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "ComWechat.py"


class FakeTimer:
    def __init__(self, delay, function, args):
        self.delay = delay
        self.function = function
        self.args = args
        self.started = False
        self.cancelled = False

    def start(self):
        self.started = True

    def is_alive(self):
        return self.started and not self.cancelled

    def cancel(self):
        self.cancelled = True


def load_mark_as_read_methods():
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    channel = next(
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name == "ComWeChatChannel"
    )
    method_names = {
        "_mark_as_read_response_ok",
        "_mark_chat_as_read",
        "_schedule_mark_as_read",
    }
    methods = [
        node
        for node in channel.body
        if isinstance(node, ast.FunctionDef) and node.name in method_names
    ]
    namespace = {
        "Any": Any,
        "ChatID": str,
        "Dict": Dict,
        "threading": SimpleNamespace(
            Timer=FakeTimer,
            current_thread=threading.current_thread,
        ),
    }
    module = ast.Module(body=methods, type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return {name: namespace[name] for name in method_names}


class MarkAsReadTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.methods = load_mark_as_read_methods()

    def make_channel(self):
        channel = SimpleNamespace(
            mark_as_read_enabled=True,
            mark_as_read_delay=10,
            mark_as_read_timers={},
            mark_as_read_lock=threading.RLock(),
            bot=SimpleNamespace(MarkAsRead=Mock(return_value={"result": "OK", "msg": 1})),
            logger=Mock(),
        )
        for name, function in self.methods.items():
            setattr(channel, name, function.__get__(channel, type(channel)))
        return channel

    def test_schedules_once_per_chat_and_skips_self_and_system_messages(self):
        channel = self.make_channel()
        schedule = channel._schedule_mark_as_read

        schedule({"msgid": "1", "type": "text", "isSendMsg": 0}, SimpleNamespace(uid="wxid_a"))
        schedule({"msgid": "2", "type": "image", "isSendMsg": 0}, SimpleNamespace(uid="wxid_a"))
        schedule({"msgid": "3", "type": "text", "isSendMsg": 1}, SimpleNamespace(uid="wxid_b"))
        schedule({"msgid": "4", "type": "sysmsg", "isSendMsg": 0}, SimpleNamespace(uid="wxid_c"))

        self.assertEqual(list(channel.mark_as_read_timers), ["wxid_a"])
        timer = channel.mark_as_read_timers["wxid_a"]
        self.assertEqual(timer.delay, 10)
        self.assertTrue(timer.started)

    def test_mark_call_removes_timer_and_passes_chat_wxid(self):
        channel = self.make_channel()
        channel._schedule_mark_as_read(
            {"msgid": "1", "type": "text", "isSendMsg": 0},
            SimpleNamespace(uid="wxid_a"),
        )

        channel._mark_chat_as_read("wxid_a", "inbound")

        channel.bot.MarkAsRead.assert_called_once_with(wxid="wxid_a")
        self.assertEqual(channel.mark_as_read_timers, {})


if __name__ == "__main__":
    unittest.main()
