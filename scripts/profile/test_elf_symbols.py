import json
from pathlib import Path
import tempfile
import unittest
from scripts.profile.elf_symbols import parse_symbols, resolve
from scripts.profile.factor_sampling_profile import Symbolicator


class SymbolTests(unittest.TestCase):
    def test_bounds_and_gaps(self):
        symbols = parse_symbols('00001000 00000010 T first\n00001040 00000020 t second\n00001090 00000000 T empty\n')
        starts = sorted(symbols)
        self.assertEqual(resolve(symbols, starts, 0x100f), (0x1000, 0x10, 'first'))
        for address in (0xfff, 0x1010, 0x103f, 0x1060, 0x1090):
            self.assertIsNone(resolve(symbols, starts, address))

    def test_summary_honors_exported_size(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'symbols.json'
            path.write_text(json.dumps(dict(string_table=['first'], data=[dict(
                debug_name='bench', symbol_table=[dict(rva=0x1000, size=0x10, symbol=0)])])))
            reader = Symbolicator(path)
            self.assertEqual(reader.resolve('bench', 0x100f), 'first')
            self.assertIsNone(reader.resolve('bench', 0x1010))
            self.assertIsNone(reader.resolve('absent', 0x1000))


if __name__ == '__main__':
    unittest.main()
