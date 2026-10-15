"""Refusal controls for the retained core-use checker."""
import contextlib
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('core_use_check', HERE / 'check_bindings.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.base = Path(self.directory.name)
        for source in HERE.iterdir():
            if source.is_file():
                shutil.copyfile(source, self.base / source.name)
        self.addCleanup(patch.stopall)
        patch.object(checker, 'BASE', self.base).start()

    def run_check(self):
        with contextlib.redirect_stdout(io.StringIO()):
            checker.check()

    def rewrite(self, name, value):
        target = self.base / name
        target.write_bytes(gzip.compress((json.dumps(value) + '\n').encode(), mtime=0))
        record = json.loads((self.base / 'bindings.json').read_text())
        record['artifacts'][name] = hashlib.sha256(target.read_bytes()).hexdigest()
        (self.base / 'bindings.json').write_text(json.dumps(record))

    def test_untouched_archive(self):
        self.run_check()

    def test_raw_artifact_tamper(self):
        target = self.base / 'declaration-use.json.gz'
        target.write_bytes(target.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'artifact differs'):
            self.run_check()

    def test_artifact_binding_omission(self):
        target = self.base / 'bindings.json'
        record = json.loads(target.read_text())
        del record['artifacts']['declaration-use.json.gz']
        target.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'artifact scope differs'):
            self.run_check()

    def test_helper_binding_omission(self):
        target = self.base / 'bindings.json'
        record = json.loads(target.read_text())
        record['tools'].pop(next(iter(record['tools'])))
        target.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'helper scope differs'):
            self.run_check()

    def test_source_scope_omission(self):
        target = self.base / 'bindings.json'
        record = json.loads(target.read_text())
        del record['inputs']['HexSignDet/Support.lean']
        target.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'input scope differs'):
            self.run_check()

    def test_source_hash_tamper(self):
        target = self.base / 'bindings.json'
        record = json.loads(target.read_text())
        record['inputs']['HexSignDet/Support.lean'] = '0' * 64
        target.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'checkpoint bytes differ'):
            self.run_check()

    def test_missing_decision_with_refreshed_hash(self):
        record = json.loads(gzip.decompress((self.base / 'retention-decisions.json.gz').read_bytes()))
        record['decisions'].pop()
        self.rewrite('retention-decisions.json.gz', record)
        with self.assertRaisesRegex(ValueError, 'retention inventory differs'):
            self.run_check()

    def test_empty_rationale_with_refreshed_hash(self):
        record = json.loads(gzip.decompress((self.base / 'retention-decisions.json.gz').read_bytes()))
        record['decisions'][0]['rationale'] = ''
        self.rewrite('retention-decisions.json.gz', record)
        with self.assertRaisesRegex(ValueError, 'missing explicit API decision'):
            self.run_check()

    def test_document_omission_with_refreshed_hash(self):
        target = self.base / 'public-dispositions.md'
        target.write_text(target.read_text().replace('## `Hex.SignDet.Codec.Decimal.readInt`', '', 1))
        record = json.loads((self.base / 'bindings.json').read_text())
        record['artifacts'][target.name] = hashlib.sha256(target.read_bytes()).hexdigest()
        (self.base / 'bindings.json').write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'public disposition differs'):
            self.run_check()


if __name__ == '__main__':
    unittest.main()
