import ast
import base64
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import Mock


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "ComWechat.py"


def load_process_pending_file():
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    channel = next(
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name == "ComWeChatChannel"
    )
    function = next(
        node
        for node in channel.body
        if isinstance(node, ast.FunctionDef) and node.name == "_process_pending_file"
    )
    namespace = {
        "base64": base64,
        "os": __import__("os"),
        "time": time,
        "resolve_hooked_wechat_image_path": lambda _path: None,
        "MsgProcess": lambda msg, _chat, _direct_transfer: msg,
        "MsgWrapper": lambda _msg, processed: processed,
        "MessageID": str,
    }
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["_process_pending_file"]


class VoiceDbFallbackTest(unittest.TestCase):
    def make_channel(self, bot):
        channel = Mock()
        channel.file_msg = {}
        channel.bot = bot
        channel.query_database = bot.QueryDatabase
        channel.direct_transfer = False
        channel.time_out = 500
        channel.logger = Mock()
        channel.send_efb_msgs = Mock()
        return channel

    def test_single_row_voice_data_is_written_and_sent(self):
        bot = Mock()
        bot.GetDBHandle.return_value = 42
        bot.QueryDatabase.return_value = {
            "result": "OK",
            "data": [[base64.b64encode(b"voice-data").decode()]],
        }
        channel = self.make_channel(bot)
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "voice.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 123}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertEqual(Path(path).read_bytes(), b"voice-data")
            self.assertNotIn(path, channel.file_msg)
            channel.send_efb_msgs.assert_called_once()

    def test_voice_database_exception_keeps_message_pending_for_retry(self):
        bot = Mock()
        bot.GetDBHandle.return_value = 42
        bot.QueryDatabase.side_effect = RuntimeError("database handle unavailable")
        channel = self.make_channel(bot)
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "voice.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 456}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertIn(path, channel.file_msg)
            bot.invalidate_db_handles.assert_called_once_with()
            channel.send_efb_msgs.assert_not_called()

    def test_header_only_voice_data_stays_pending(self):
        bot = Mock()
        bot.GetDBHandle.return_value = 42
        bot.QueryDatabase.return_value = {"result": "OK", "data": [["Buf"]]}
        channel = self.make_channel(bot)
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "voice.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 789}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertIn(path, channel.file_msg)
            self.assertFalse(Path(path).exists())
            channel.send_efb_msgs.assert_not_called()


if __name__ == "__main__":
    unittest.main()
