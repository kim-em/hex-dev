"""Memory observations remain optional when a measured process is killed."""
from pathlib import Path
import tempfile
import unittest

from scripts.bench.groebner_cli_measure import read_rss


class RssTests(unittest.TestCase):
    def test_missing_or_interrupted_output(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rss'
            self.assertIsNone(read_rss(path))
            for text in ['', '\n', 'Command terminated by signal 9\n', 'partial']:
                path.write_text(text)
                self.assertIsNone(read_rss(path))

    def test_completed_failure_memory(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rss'
            path.write_text('Command exited with non-zero status 1\n12345\n')
            self.assertEqual(read_rss(path), 12345)

    def test_zero_and_malformed_values(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rss'
            path.write_text('0\n')
            self.assertEqual(read_rss(path), 0)
            for text in ['-1', '1.5', '123 KiB', '١٢٣']:
                path.write_text(text)
                self.assertIsNone(read_rss(path))


if __name__ == '__main__':
    unittest.main()
