import ast
import base64
import re
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
    voice_database_names = next(
        node
        for node in channel.body
        if isinstance(node, ast.FunctionDef) and node.name == "_voice_database_names"
    )
    function = next(
        node
        for node in channel.body
        if isinstance(node, ast.FunctionDef) and node.name == "_process_pending_file"
    )
    namespace = {
        "base64": base64,
        "os": __import__("os"),
        "re": re,
        "time": time,
        "resolve_hooked_wechat_image_path": lambda _path: None,
        "MsgProcess": lambda msg, _chat, _direct_transfer: msg,
        "MsgWrapper": lambda _msg, processed: processed,
        "MessageID": str,
        "VOICE_DATABASE_NAMES": ("MediaMSG0.db", "MediaMSG1.db", "MediaMSG2.db"),
    }
    module = ast.Module(body=[voice_database_names, function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    def process_pending_file(channel, path):
        channel._voice_database_names = namespace["_voice_database_names"].__get__(channel)
        return namespace["_process_pending_file"](channel, path)

    return process_pending_file


class VoiceDbFallbackTest(unittest.TestCase):
    def make_channel(self, bot):
        channel = Mock()
        channel.file_msg = {}
        channel.bot = bot
        channel.query_database = bot.QueryDatabase
        channel.dbkey = Mock()
        channel.dbkey.database_names.return_value = [
            "MediaMSG0.db",
            "MediaMSG1.db",
            "MediaMSG2.db",
        ]
        channel._voice_db_names = None
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

    def test_voice_data_is_found_in_a_nonzero_media_database(self):
        bot = Mock()

        def query_database(**kwargs):
            if kwargs["db_name"] == "MediaMSG2.db":
                return {
                    "result": "OK",
                    "data": [[base64.b64encode(b"voice-from-shard-2").decode()]],
                }
            return {"result": "OK", "data": []}

        bot.QueryDatabase.side_effect = query_database
        channel = self.make_channel(bot)
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "voice.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 321}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertEqual(Path(path).read_bytes(), b"voice-from-shard-2")
            self.assertNotIn(path, channel.file_msg)
            channel.send_efb_msgs.assert_called_once()
            self.assertEqual(
                [call.kwargs["db_name"] for call in bot.QueryDatabase.call_args_list],
                ["MediaMSG0.db", "MediaMSG1.db", "MediaMSG2.db"],
            )

    def test_successful_voice_query_caches_database_names(self):
        bot = Mock()
        bot.QueryDatabase.return_value = {"result": "OK", "data": []}
        channel = self.make_channel(bot)
        channel.dbkey.database_names.return_value = []
        bot.GetDatabaseHandles.return_value = {
            "data": [{"db_name": "MediaMSG0.db"}],
        }
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            for msgid in (654, 655):
                path = str(Path(tmpdir) / (str(msgid) + ".amr"))
                message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": msgid}
                channel.file_msg[path] = (message, None, None)
                process_pending_file(channel, path)

        self.assertEqual(
            channel._voice_db_names,
            ["MediaMSG0.db"],
        )
        channel.dbkey.database_names.assert_called_once_with("MediaMSG")
        bot.GetDatabaseHandles.assert_called_once_with()
        bot.invalidate_db_handles.assert_not_called()

    def test_cached_database_names_skip_all_discovery(self):
        bot = Mock()
        bot.QueryDatabase.return_value = {"result": "OK", "data": []}
        channel = self.make_channel(bot)
        channel._voice_db_names = ["MediaMSG2.db"]
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "cached.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 656}
            channel.file_msg[path] = (message, None, None)
            process_pending_file(channel, path)

        channel.dbkey.database_names.assert_not_called()
        bot.GetDatabaseHandles.assert_not_called()
        bot.QueryDatabase.assert_called_once_with(
            db_name="MediaMSG2.db",
            sql="SELECT Buf FROM Media WHERE Reserved0 = 656",
        )

    def test_query_error_on_one_cached_shard_checks_later_shards(self):
        bot = Mock()
        bot.QueryDatabase.side_effect = [
            {"result": "ERROR", "data": []},
            {
                "result": "OK",
                "data": [[base64.b64encode(b"voice-from-later-shard").decode()]],
            },
        ]
        channel = self.make_channel(bot)
        channel._voice_db_names = ["MediaMSG0.db", "MediaMSG2.db"]
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "later-shard.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 659}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertEqual(Path(path).read_bytes(), b"voice-from-later-shard")

        self.assertEqual(channel._voice_db_names, ["MediaMSG0.db", "MediaMSG2.db"])
        channel.dbkey.database_names.assert_not_called()
        bot.GetDatabaseHandles.assert_not_called()
        bot.invalidate_db_handles.assert_not_called()

    def test_failed_query_refreshes_database_names_once(self):
        bot = Mock()
        bot.QueryDatabase.side_effect = [
            {"result": "ERROR", "data": []},
            {"result": "OK", "data": []},
            {
                "result": "OK",
                "data": [[base64.b64encode(b"voice-after-refresh").decode()]],
            },
        ]
        channel = self.make_channel(bot)
        channel.dbkey.database_names.side_effect = [
            ["MediaMSG0.db"],
            ["MediaMSG0.db", "MediaMSG2.db"],
        ]
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "refresh.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 657}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertEqual(Path(path).read_bytes(), b"voice-after-refresh")

        self.assertEqual(channel._voice_db_names, ["MediaMSG0.db", "MediaMSG2.db"])
        self.assertEqual(channel.dbkey.database_names.call_count, 2)
        bot.GetDatabaseHandles.assert_not_called()
        bot.invalidate_db_handles.assert_called_once_with()

    def test_invalid_voice_data_does_not_refresh_database_names(self):
        bot = Mock()
        bot.QueryDatabase.return_value = {
            "result": "OK",
            "data": [["not-base64"]],
        }
        channel = self.make_channel(bot)
        process_pending_file = load_process_pending_file()

        with tempfile.TemporaryDirectory() as tmpdir:
            path = str(Path(tmpdir) / "invalid.amr")
            message = {"type": "voice", "filepath": path, "timestamp": 9999999999, "msgid": 658}
            channel.file_msg[path] = (message, None, None)

            process_pending_file(channel, path)

            self.assertIn(path, channel.file_msg)
            self.assertFalse(Path(path).exists())

        channel.dbkey.database_names.assert_called_once_with("MediaMSG")
        bot.GetDatabaseHandles.assert_not_called()
        bot.invalidate_db_handles.assert_not_called()
        channel.send_efb_msgs.assert_not_called()


if __name__ == "__main__":
    unittest.main()
