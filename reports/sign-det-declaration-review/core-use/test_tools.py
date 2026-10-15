"""Positive and refusal controls for the scoped core-use assessment."""
import contextlib
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


checker = load('core_use_check', 'check_bindings.py')
deriver = load('core_use_derive', 'derive.py')


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
        patch.object(deriver, 'BASE', self.base).start()

    def run_check(self, current=False):
        with contextlib.redirect_stdout(io.StringIO()):
            checker.check(current)

    def update_binding(self, change):
        path = self.base / 'bindings.json'
        record = json.loads(path.read_text())
        change(record)
        path.write_text(json.dumps(record))

    def rebind(self, name):
        checksum = hashlib.sha256((self.base / name).read_bytes()).hexdigest()
        self.update_binding(lambda record: record['artifacts'].__setitem__(name, checksum))

    def rewrite(self, name, value):
        (self.base / name).write_bytes(gzip.compress((json.dumps(value) + '\n').encode(), mtime=0))
        self.rebind(name)

    def json(self, name):
        return json.loads(gzip.decompress((self.base / name).read_bytes()))

    def raw_directory(self):
        output = self.base / 'raw'
        output.mkdir()
        for name in checker.RAW + checker.MANUAL:
            (output / name).write_text(json.dumps(self.json(name + '.gz')))
        return output

    def test_untouched_archive(self):
        self.run_check()

    def test_current_source_derivation(self):
        def run(output):
            subprocess.run([sys.executable, str(HERE / 'derive.py'), str(output)],
                           cwd=checker.ROOT, check=True, stdout=subprocess.DEVNULL)
        with patch.object(checker, 'run_derivation', run):
            self.run_check(current=True)

    def test_current_output_must_be_fresh(self):
        with patch.object(checker, 'run_derivation', lambda output: None):
            with self.assertRaisesRegex(ValueError, 'derived output missing'):
                self.run_check(current=True)

    def test_raw_artifact_tamper(self):
        path = self.base / 'declaration-use.json.gz'
        path.write_bytes(path.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'artifact differs'):
            self.run_check()

    def test_unbound_compressed_artifact(self):
        (self.base / 'extra.json.gz').write_bytes(gzip.compress(b'{}'))
        with self.assertRaisesRegex(ValueError, 'unbound compressed evidence'):
            self.run_check()

    def test_artifact_binding_omission(self):
        self.update_binding(lambda record: record['artifacts'].pop('declaration-use.json.gz'))
        with self.assertRaisesRegex(ValueError, 'artifact scope differs'):
            self.run_check()

    def test_helper_binding_omission(self):
        self.update_binding(lambda record: record['tools'].pop(next(iter(record['tools']))))
        with self.assertRaisesRegex(ValueError, 'helper scope differs'):
            self.run_check()

    def test_helper_hash_tamper(self):
        self.update_binding(lambda record: record['tools'].__setitem__(
            next(iter(record['tools'])), '0' * 64))
        with self.assertRaisesRegex(ValueError, 'checkpoint bytes differ'):
            self.run_check()

    def test_input_tag_mismatch(self):
        self.update_binding(lambda record: record.__setitem__('input_revision', '0' * 40))
        with self.assertRaisesRegex(ValueError, 'input tag differs'):
            self.run_check()

    def test_source_scope_omission(self):
        self.update_binding(lambda record: record['inputs'].pop('HexSignDet/Support.lean'))
        with self.assertRaisesRegex(ValueError, 'input scope differs'):
            self.run_check()

    def test_source_hash_tamper(self):
        self.update_binding(lambda record: record['inputs'].__setitem__(
            'HexSignDet/Support.lean', '0' * 64))
        with self.assertRaisesRegex(ValueError, 'checkpoint bytes differ'):
            self.run_check()

    def test_current_source_drift(self):
        changed = checker.ROOT / 'HexSignDet/Support.lean'
        original = Path.read_bytes
        def read(path):
            return original(path) + (b'changed' if path == changed else b'')
        with patch.object(Path, 'read_bytes', read):
            with self.assertRaisesRegex(ValueError, 'current core-use source differs'):
                self.run_check(current=True)

    def test_missing_decision_with_refreshed_hash(self):
        record = self.json('retention-decisions.json.gz')
        record['decisions'].pop()
        self.rewrite('retention-decisions.json.gz', record)
        with self.assertRaisesRegex(ValueError, 'retention inventory differs'):
            self.run_check()

    def test_empty_rationale_with_refreshed_hash(self):
        record = self.json('retention-decisions.json.gz')
        record['decisions'][0]['rationale'] = ''
        self.rewrite('retention-decisions.json.gz', record)
        with self.assertRaisesRegex(ValueError, 'missing explicit API decision'):
            self.run_check()

    def test_document_omission_with_refreshed_hash(self):
        path = self.base / 'public-dispositions.md'
        path.write_text(path.read_text().replace('## `Hex.SignDet.Codec.Decimal.readInt`', '', 1))
        self.rebind(path.name)
        with self.assertRaisesRegex(ValueError, 'public disposition inventory differs'):
            self.run_check()

    def test_rationales_cannot_move_between_headings(self):
        decisions = self.json('retention-decisions.json.gz')['decisions']
        first, second = (row['rationale'] for row in decisions[:2])
        path = self.base / 'public-dispositions.md'
        path.write_text(path.read_text().replace(first, '__SWAP__', 1)
                        .replace(second, first, 1).replace('__SWAP__', second, 1))
        self.rebind(path.name)
        with self.assertRaisesRegex(ValueError, 'public disposition section differs'):
            self.run_check()

    def test_client_count_binds_to_its_section(self):
        path = self.base / 'public-dispositions.md'
        first = self.json('retention-decisions.json.gz')['decisions'][0]
        count = len(first['clients'])
        path.write_text(path.read_text().replace(
            f'Alias-merged named clients: {count}.', f'Alias-merged named clients: {count + 1}.', 1))
        self.rebind(path.name)
        with self.assertRaisesRegex(ValueError, 'public disposition section differs'):
            self.run_check()

    def test_alternative_decisions_can_be_recorded(self):
        for choice in ('make_private', 'remove'):
            with self.subTest(choice=choice):
                record = self.json('retention-decisions.json.gz')
                first = record['decisions'][0]
                old = f"Decision: {first['decision']}. {first['rationale']}"
                first['decision'], first['rationale'] = choice, 'Synthetic review disposition.'
                path = self.base / 'public-dispositions.md'
                path.write_text(path.read_text().replace(
                    old, f"Decision: {choice}. {first['rationale']}", 1))
                self.rewrite('retention-decisions.json.gz', record)
                self.rebind(path.name)
                self.run_check()

    def test_readme_facts_are_checked(self):
        path = self.base / 'README.md'
        path.write_text(path.read_text().replace('| Core modules | 58 |', '| Core modules | 59 |'))
        self.rebind(path.name)
        with self.assertRaisesRegex(ValueError, 'README facts differ'):
            self.run_check()

    def test_missing_selected_evidence_is_refused(self):
        output = self.raw_directory()
        path = output / 'audit-imports.json'
        imports = json.loads(path.read_text())
        imports.remove('HexSignDet.FastCheck')
        path.write_text(json.dumps(imports))
        with self.assertRaisesRegex(ValueError, 'missing selected evidence imports'):
            deriver.derive(output)

    def test_private_helper_requires_public_path(self):
        output = self.raw_directory()
        helper = self.json('helper-paths.json.gz')[0]['helper']
        path = output / 'declaration-use.json'
        rows = json.loads(path.read_text())
        for row in rows:
            if (row['name'] == helper or row['name'].startswith(helper + '.') or
                    row['base_declaration'] == helper):
                row['users'], row['user_modules'], row['user_bases'] = [], {}, {}
        path.write_text(json.dumps(rows))
        with self.assertRaisesRegex(ValueError, 'private helper has no public path'):
            deriver.derive(output)

    def test_additional_constants_are_not_dropped(self):
        output = self.raw_directory()
        path = output / 'declaration-use.json'
        rows = json.loads(path.read_text())
        extra = dict(rows[0], name='Hex.SignDet.uninventoried', user_name='Hex.SignDet.uninventoried')
        rows.append(extra)
        path.write_text(json.dumps(rows))
        with self.assertRaisesRegex(ValueError, 'additional constant inventory differs'):
            deriver.derive(output)

    def test_unsupported_source_forms_are_refused(self):
        path = self.base / 'Source.lean'
        for source in ['partial def hidden : Nat := 0', 'public def hidden : Nat := 0',
                       'instance named : Inhabited Nat := ⟨0⟩']:
            with self.subTest(source=source):
                path.write_text(source)
                with self.assertRaises(ValueError):
                    deriver.check_source_forms(path)


if __name__ == '__main__':
    unittest.main()
