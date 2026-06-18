import importlib.util
import pathlib
import sys
import tempfile
import types
import unittest


MODULE_PATH = pathlib.Path(__file__).resolve().parents[1] / "efb_wechat_comwechat_slave" / "Utils.py"


class FakeAudioSegment:
    def __init__(self, calls):
        self.calls = calls

    def export(self, out_path, **kwargs):
        self.calls.append(("export", out_path, kwargs))
        with open(out_path, "wb") as f:
            f.write(b"ogg-data")


def load_utils_module():
    package_name = "efb_wechat_comwechat_slave"
    module_name = f"{package_name}.Utils"

    for name in [
        module_name,
        package_name,
        "ehforwarderbot",
        "ehforwarderbot.types",
        "requests",
        "yaml",
        "pilk",
        "pydub",
    ]:
        sys.modules.pop(name, None)

    package = types.ModuleType(package_name)
    package.__path__ = [str(MODULE_PATH.parent)]
    sys.modules[package_name] = package

    ehforwarderbot_types_module = types.ModuleType("ehforwarderbot.types")
    ehforwarderbot_types_module.MessageID = str
    sys.modules["ehforwarderbot.types"] = ehforwarderbot_types_module

    sys.modules["requests"] = types.ModuleType("requests")
    sys.modules["yaml"] = types.ModuleType("yaml")

    pilk_module = types.ModuleType("pilk")
    pilk_module.decode_calls = []

    def fake_decode(src, dest):
        pilk_module.decode_calls.append((src, dest))
        with open(dest, "wb") as f:
            f.write(b"pcm-data")

    pilk_module.decode = fake_decode
    sys.modules["pilk"] = pilk_module

    pydub_module = types.ModuleType("pydub")
    pydub_module.calls = []

    class AudioSegmentModule:
        @staticmethod
        def from_raw(file, sample_width, frame_rate, channels):
            pydub_module.calls.append(
                ("from_raw", getattr(file, "name", None), sample_width, frame_rate, channels)
            )
            return FakeAudioSegment(pydub_module.calls)

        @staticmethod
        def from_file(path, format=None):
            pydub_module.calls.append(("from_file", path, format))
            return FakeAudioSegment(pydub_module.calls)

    pydub_module.AudioSegment = AudioSegmentModule
    sys.modules["pydub"] = pydub_module

    spec = importlib.util.spec_from_file_location(module_name, MODULE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module, pilk_module, pydub_module


class TestVoiceConversion(unittest.TestCase):
    def setUp(self):
        self.utils_module, self.pilk_module, self.pydub_module = load_utils_module()

    def _temp_voice_file(self, header):
        temp = tempfile.NamedTemporaryFile(delete=False)
        temp.write(header + b"payload")
        temp.flush()
        temp.close()
        self.addCleanup(lambda: pathlib.Path(temp.name).unlink(missing_ok=True))
        return temp.name

    def test_silk_voice_uses_pilk_decode_then_exports_ogg(self):
        source = self._temp_voice_file(b"#!SILK_V3")

        with open(source, "rb") as voice_file:
            converted = self.utils_module.convert_silk_to_mp3(voice_file)
            self.addCleanup(converted.close)
            self.assertEqual(converted.read(), b"ogg-data")

        self.assertEqual(len(self.pilk_module.decode_calls), 1)
        self.assertEqual(self.pydub_module.calls[0][0], "from_raw")
        self.assertEqual(self.pydub_module.calls[1][0], "export")

    def test_amr_voice_uses_amr_decoder_then_exports_ogg(self):
        source = self._temp_voice_file(b"#!AMR\n")

        with open(source, "rb") as voice_file:
            converted = self.utils_module.convert_silk_to_mp3(voice_file)
            self.addCleanup(converted.close)
            self.assertEqual(converted.read(), b"ogg-data")

        self.assertEqual(self.pilk_module.decode_calls, [])
        self.assertEqual(self.pydub_module.calls[0], ("from_file", source, "amr"))
        self.assertEqual(self.pydub_module.calls[1][0], "export")


if __name__ == "__main__":
    unittest.main()
