import ast
import sys
import unittest
import importlib.util
from pathlib import Path
from unittest.mock import Mock, patch


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "dbkey.py"


def load_dbkey():
    spec = importlib.util.spec_from_file_location("testdbkey", SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class DbKeyPriorityTest(unittest.TestCase):
    def test_read_only_query_prefers_db_key(self):
        channel = Mock()
        channel.wxid = "wxid_test"
        channel.channel_id = "honus.comwechat"
        channel.dir = "/tmp/wechat-files/"
        channel.config = {"dir": "/tmp/wechat-files/"}
        DbKeyManager = load_dbkey().DbKeyManager

        manager = DbKeyManager(channel, data_dir=str(Path("/tmp/profile-dir")), wechat_root="/tmp/wechat-files")
        reader = Mock()
        reader.query.return_value = [["UserName"], ["wxid_a"]]
        with patch.object(manager, "_discover_key_path", return_value=Path("/tmp/profile-dir/wxid_dbkey.json")), patch.object(
            manager, "_get_reader", return_value=reader
        ):
            response = manager.query("MicroMsg.db", "select UserName from Contact")
        self.assertEqual(response, {"result": "OK", "data": [["UserName"], ["wxid_a"]]})
        reader.query.assert_called_once()

    def test_missing_key_falls_back_to_native(self):
        channel = Mock()
        channel.wxid = None
        channel.channel_id = "honus.comwechat"
        DbKeyManager = load_dbkey().DbKeyManager

        manager = DbKeyManager(channel, data_dir="/nonexistent", wechat_root="/nonexistent")
        self.assertIsNone(manager.query("MicroMsg.db", "select UserName from Contact"))


if __name__ == "__main__":
    unittest.main()
