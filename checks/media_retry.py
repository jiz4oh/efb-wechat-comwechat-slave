import ast
import json
import os
import tempfile
import threading
import time
import types
import unittest
from pathlib import Path


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "ComWechat.py"


class FakeMessage:
    def __init__(self):
        self.commands = None


class FakeCommand:
    def __init__(self, name, callable_name, args=None, kwargs=None):
        self.name = name
        self.callable_name = callable_name
        self.args = args or []
        self.kwargs = kwargs or {}


def load_methods():
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    channel = next(node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == "ComWeChatChannel")
    names = {
        "_media_retry_payload",
        "_media_retry_command",
        "_load_media_retry_cache",
        "_persist_media_retry_cache",
        "_remove_media_retry",
        "_process_pending_file",
        "_voice_database_names",
        "retry_media",
    }
    methods = [node for node in channel.body if isinstance(node, ast.FunctionDef) and node.name in names]
    namespace = {
        "MEDIA_RETRY_TYPES": {"image", "video", "file", "share"},
        "MEDIA_RETRY_FIELDS": (
            "type", "message", "msgid", "svrid", "sender", "self", "wxid", "extrainfo", "thumb_path",
        ),
        "MessageCommand": FakeCommand,
        "MessageCommands": list,
        "MessageID": str,
        "MsgProcess": lambda msg, _chat, _direct: FakeMessage(),
        "MsgWrapper": lambda _msg, processed: processed,
        "resolve_hooked_wechat_image_path": lambda _path: None,
        "EFBMessageError": RuntimeError,
        "json": json,
        "os": os,
        "secrets": __import__("secrets"),
        "tempfile": tempfile,
        "time": time,
    }
    module = ast.Module(body=methods, type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace


class Channel:
    def __init__(self, methods, cache_path=None):
        self.file_msg = {}
        self.direct_transfer = False
        self.time_out = 10
        self.wxid = "wxid_self"
        self._cache_tempdir = None if cache_path else tempfile.TemporaryDirectory()
        self.media_retry_cache_path = (
            Path(cache_path)
            if cache_path
            else Path(self._cache_tempdir.name) / "media_retry_cache.json"
        )
        self.media_retry_cache_lock = threading.RLock()
        self.media_retry_cache = {}
        self.logger = types.SimpleNamespace(
            warning=lambda *args, **kwargs: None,
            exception=lambda *args, **kwargs: None,
        )
        self.sent = []
        self._voice_database_names = types.MethodType(methods["_voice_database_names"], self)
        self._media_retry_payload = types.MethodType(methods["_media_retry_payload"], self)
        self._media_retry_command = staticmethod(methods["_media_retry_command"])
        self._load_media_retry_cache = types.MethodType(methods["_load_media_retry_cache"], self)
        self._persist_media_retry_cache = types.MethodType(methods["_persist_media_retry_cache"], self)
        self._remove_media_retry = types.MethodType(methods["_remove_media_retry"], self)
        self._process_pending_file = types.MethodType(methods["_process_pending_file"], self)
        self._load_media_retry_cache()

    def send_efb_msgs(self, message, **kwargs):
        self.sent.append((message, kwargs))


class TestMediaRetry(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.methods = load_methods()

    def make_channel(self):
        channel = Channel(self.methods)
        channel.retry_media = types.MethodType(self.methods["retry_media"], channel)
        return channel

    @staticmethod
    def context():
        chat = types.SimpleNamespace(uid="wxid_friend", name="Friend")
        author = types.SimpleNamespace(uid="wxid_friend", name="Friend", alias=None)
        return chat, author

    def test_timeout_message_has_retry_command_and_keeps_attachment_for_retry(self):
        channel = self.make_channel()
        chat, author = self.context()
        path = "/tmp/attachment-that-is-not-ready.mp4"
        msg = {
            "type": "video",
            "filepath": path,
            "timestamp": 0,
            "msgid": 123,
            "sender": "wxid_friend",
            "self": "wxid_self",
        }
        channel.file_msg[path] = (msg, author, chat)

        self.methods["_process_pending_file"](channel, path)

        self.assertNotIn(path, channel.file_msg)
        failure, _kwargs = channel.sent[0]
        command = failure.commands[0]
        self.assertEqual(command.name, "Retry")
        self.assertEqual(command.callable_name, "retry_media")
        self.assertEqual(list(command.kwargs), ["retry_id"])
        retry_id = command.kwargs["retry_id"]
        self.assertLessEqual(len(json.dumps(command.kwargs, separators=(",", ":")).encode()), 64)
        self.assertEqual(channel.media_retry_cache[retry_id]["path"], path)
        self.assertEqual(channel.media_retry_cache[retry_id]["type"], "video")

    def test_retry_checks_disk_and_reuploads_existing_file(self):
        channel = self.make_channel()
        chat, author = self.context()
        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "video.mp4")
            Path(path).write_bytes(b"video")
            retry_id = channel._media_retry_payload(
                path,
                {"type": "video", "msgid": 456},
                author,
                chat,
            )
            channel._build_media_retry_context = lambda _payload: (chat, author)

            result = channel.retry_media(retry_id)

            self.assertEqual(result, "媒体重试发送成功")
            self.assertEqual(len(channel.sent), 1)
            self.assertTrue(Path(path).exists())
            self.assertNotIn(retry_id, channel.media_retry_cache)

    def test_file_timeout_has_retry_command_and_can_retry_existing_attachment(self):
        channel = self.make_channel()
        chat, author = self.context()
        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "document.pdf")
            msg = {
                "type": "file",
                "filepath": path,
                "timestamp": 0,
                "msgid": 458,
            }
            channel.file_msg[path] = (msg, author, chat)

            self.methods["_process_pending_file"](channel, path)

            failure, _kwargs = channel.sent[0]
            retry_id = failure.commands[0].kwargs["retry_id"]
            self.assertEqual(channel.media_retry_cache[retry_id]["type"], "file")

            Path(path).write_bytes(b"pdf")
            channel._build_media_retry_context = lambda _payload: (chat, author)
            result = channel.retry_media(retry_id)

            self.assertEqual(result, "媒体重试发送成功")
            self.assertTrue(Path(path).exists())
            self.assertNotIn(retry_id, channel.media_retry_cache)

    def test_retry_context_survives_process_reload(self):
        chat, author = self.context()
        with tempfile.TemporaryDirectory() as tmpdir:
            cache_path = str(Path(tmpdir) / "retry-cache.json")
            path = str(Path(tmpdir) / "video.mp4")
            Path(path).write_bytes(b"video")
            channel = Channel(self.methods, cache_path)
            retry_id = channel._media_retry_payload(
                path,
                {"type": "video", "msgid": 457},
                author,
                chat,
            )

            reloaded = self.make_channel()
            reloaded.media_retry_cache_path = Path(cache_path)
            reloaded.media_retry_cache.clear()
            reloaded._load_media_retry_cache()
            reloaded._build_media_retry_context = lambda _payload: (chat, author)

            result = reloaded.retry_media(retry_id)

            self.assertEqual(result, "媒体重试发送成功")
            self.assertEqual(len(reloaded.sent), 1)
            self.assertTrue(Path(path).exists())

    def test_retry_does_not_upload_missing_file(self):
        channel = self.make_channel()
        chat, author = self.context()
        retry_id = channel._media_retry_payload(
            "/tmp/missing.mp4",
            {"type": "video"},
            author,
            chat,
        )
        result = channel.retry_media(retry_id)
        self.assertEqual(result, "媒体附件已不存在，无法重试")
        self.assertEqual(channel.sent, [])

if __name__ == "__main__":
    unittest.main()
