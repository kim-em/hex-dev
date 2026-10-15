"""Exercise the actual ordinary counts-mode region in the existing oracle job."""
import json
import os
from pathlib import Path
import subprocess
import unittest


@unittest.skipUnless(os.environ.get('HEX_METI_COUNTS_DRIVER'), 'counts driver not requested')
class ModeTests(unittest.TestCase):
    def test_real_degree_three_region_and_packet(self):
        result = subprocess.run([os.environ['HEX_METI_COUNTS_DRIVER'], 'metitarski', 'counts', '3'],
                                text=True, capture_output=True, timeout=120, check=True)
        path = Path('conformance-fixtures/HexRealClosure/metitarski-scaling.jsonl')
        expected = next(line for line in path.read_text().splitlines() if json.loads(line)['degree'] == 3)
        self.assertEqual(result.stdout, expected + '\n')
        events = [line for line in result.stderr.splitlines() if line.startswith('METI ')]
        self.assertEqual(events, ['METI BEGIN', 'METI END'])


if __name__ == '__main__':
    unittest.main()
