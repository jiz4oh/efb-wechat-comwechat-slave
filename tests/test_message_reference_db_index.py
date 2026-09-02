import ast
import re
import unittest
from pathlib import Path


SOURCE = Path(__file__).parents[1] / "efb_wechat_comwechat_slave" / "ComWechat.py"


def load_message_references():
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"), filename=str(SOURCE))
    channel = next(
        node
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name == "ComWeChatChannel"
    )
    function = next(
        node
        for node in channel.body
        if isinstance(node, ast.FunctionDef) and node.name == "_message_references"
    )
    namespace = {
        "MessageID": str,
        "re": re,
        "is_message_reference": lambda value: (
            str(value).isdigit() and int(value) > 0
        )
        or bool(re.fullmatch(r"local:\d+:\d+", str(value))),
    }
    module = ast.Module(body=[function], type_ignores=[])
    ast.fix_missing_locations(module)
    exec(compile(module, str(SOURCE), "exec"), namespace)
    return namespace["_message_references"]


class MessageReferencePrefixIndexTest(unittest.TestCase):
    def test_msg_filename_maps_to_one_based_prefix_index(self):
        class Bot:
            def GetDatabaseHandles(self):
                raise AssertionError("must not query native database indexes")

        class DbKey:
            @staticmethod
            def database_names(_prefix):
                return ["MSG0.db"]

        class Channel:
            bot = Bot()
            dbkey = DbKey()

            @staticmethod
            def query_database(**_kwargs):
                return {"result": "OK", "data": [["localId"], ["55212"]]}

        references_method = load_message_references()
        references = references_method(Channel(), "7220974329073302334")

        self.assertEqual(
            references,
            ["7220974329073302334", "local:1:55212"],
        )

    def test_second_message_database_uses_prefix_index_two(self):
        class DbKey:
            @staticmethod
            def database_names(_prefix):
                return ["MSG1.db"]

        class Channel:
            dbkey = DbKey()

            @staticmethod
            def query_database(**_kwargs):
                return {"result": "OK", "data": [["localId"], ["55370"]]}

        references_method = load_message_references()
        self.assertEqual(
            references_method(Channel(), "7220974329073302334"),
            ["7220974329073302334", "local:2:55370"],
        )


if __name__ == "__main__":
    unittest.main()
