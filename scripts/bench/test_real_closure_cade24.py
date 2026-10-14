"""Reject changed archive bytes, inputs, policy arms and HTTP range responses."""
import ast
from copy import deepcopy
import io
import json
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch
import urllib.error
import zipfile
import zlib

from scripts.bench.real_closure_cade24 import (
    REPORT, bindings, digest, fetch, fetch_member, helper_calls, inflate, read_range, root_calls,
    selections, tower_stages, verify, verify_inventory)


class Response(io.BytesIO):
    def __init__(self, body, status=206, content_range='bytes 10-12/100'):
        super().__init__(body)
        self.status = status
        self.headers = {'Content-Range': content_range}


class RangeTests(unittest.TestCase):
    def test_finite_retries_for_transient_server_errors(self):
        error = urllib.error.HTTPError('https://example.test/z.zip', 500, 'temporary', {}, None)
        with patch('scripts.bench.real_closure_cade24.time.sleep'), \
                patch('scripts.bench.real_closure_cade24.urllib.request.urlopen') as opener:
            opener.side_effect = [error, error, Response(b'abc')]
            self.assertEqual(read_range('https://example.test/z.zip', 10, 3, 100, opener), b'abc')
            self.assertEqual(opener.call_count, 3)
            opener.reset_mock()
            opener.side_effect = error
            with self.assertRaises(urllib.error.HTTPError):
                read_range('https://example.test/z.zip', 10, 3, 100, opener)
            self.assertEqual(opener.call_count, 3)

    def test_bounded_response(self):
        def opener(request, timeout):
            self.assertEqual(request.headers['Range'], 'bytes=10-12')
            self.assertEqual(timeout, 60)
            return Response(b'abc')
        self.assertEqual(read_range('https://example.test/z.zip', 10, 3, 100, opener), b'abc')

    def test_refuse_unbounded_wrong_or_truncated_response(self):
        for response in [Response(b'abc', status=200),
                         Response(b'abc', content_range='bytes 9-11/100'),
                         Response(b'ab'), Response(b'abcd')]:
            with self.subTest(response=response), self.assertRaises(ValueError):
                read_range('https://example.test/z.zip', 10, 3, 100,
                           lambda *args, **kwargs: response)
        response = Response(b'abc')
        response.headers['Content-Encoding'] = 'gzip'
        with self.assertRaises(ValueError):
            read_range('https://example.test/z.zip', 10, 3, 100,
                       lambda *args, **kwargs: response)
        for start, size in [(0, 1_000_001), (-1, 3), (99, 3), (0, 0)]:
            with self.subTest(start=start, size=size), self.assertRaises(ValueError):
                read_range('https://example.test/z.zip', start, size, 100,
                           lambda *args, **kwargs: self.fail('invalid request sent'))

    def test_local_header_and_compressed_integrity(self):
        raw = b'archived input\n' * 3
        compressor = zlib.compressobj(wbits=-15)
        compressed = compressor.compress(raw) + compressor.flush()
        name = 'releases\\0\\example'
        member = dict(name=name, offset=50, size=len(raw),
                      compressed_size=len(compressed), crc32=zlib.crc32(raw),
                      sha256=digest(raw))
        header = struct.pack('<I5H3I2H', 0x04034B50, 20, 0, 8, 0, 0,
                             member['crc32'], len(compressed), len(raw), len(name), 0)
        def reader(url, offset, size, total):
            self.assertEqual(total, 1000)
            if offset == 50:
                self.assertEqual(size, 30)
                return header
            self.assertEqual((offset, size), (80, len(name) + len(compressed)))
            return name.encode() + compressed
        manifest = dict(archive_url='https://example.test/z.zip', archive_size=1000)
        self.assertEqual(fetch_member(manifest, member, reader), raw)
        for key, value in [('crc32', 0), ('size', 1), ('sha256', '0' * 64)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                inflate(compressed, dict(member, **{key: value}))
        for data in [compressed[:-1], compressed + b'junk', zlib.compress(raw)]:
            with self.subTest(data=data), self.assertRaises((ValueError, zlib.error)):
                inflate(data, member)
        with self.assertRaises(ValueError):
            fetch_member(manifest, dict(member, name='wrong'), reader)
        fields = list(struct.unpack('<I5H3I2H', header))
        for index, changed in [(2, 8), (3, 0), (6, 0), (7, 1), (8, 1),
                               (9, 1025), (10, 4097)]:
            invalid = fields.copy()
            invalid[index] = changed
            with self.subTest(header_field=index), self.assertRaises(ValueError):
                fetch_member(manifest, member,
                             lambda *args: struct.pack('<I5H3I2H', *invalid))


def fixture(folder):
    script = 'sqrt2 = Sqrt(2)\n' + '\n'.join(
        f'r{i} = MkRoots([{i}, 0, 1])[0]' for i in range(5)) + '\n'
    eager = 'set_param("rcf.lazy_algebraic_normalization", False)\n' + script
    archive = io.BytesIO()
    scripts = []
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as output:
        for name, text in [('tower8.py', script), ('tower8_eager_norm.py', eager)]:
            body = text.encode()
            output.writestr('cade24ex/' + name, body)
            scripts.append(dict(name=name, size=len(body), crc32=zlib.crc32(body),
                                sha256=digest(body), root_calls=root_calls(ast.parse(text)),
                                helper_calls=helper_calls(ast.parse(text)),
                                selections=selections(ast.parse(text)),
                                bindings=bindings(ast.parse(text))))
    release = dict(id='0', name='CADE-24 examples', file_id='example-id',
                   file_name='cade24ex.zip', upload_date='original-date', paper_title='Test paper')
    files = {
        'cade24ex.zip': archive.getvalue(),
        'releaseList.json': json.dumps([dict(Id='0', Name=release['name'],
            Description=release['paper_title'], Files=[dict(Type='Example',
            Id=release['file_id'], FileName=release['file_name'],
            UploadDate=release['upload_date'], Url='./0/' + release['file_id'])])]).encode(),
        'CADE24.html': b'<a href="http://z3.codeplex.com/downloads/get/606232">Examples</a>',
        'documents.json': json.dumps([dict(Id='689120', Title='CADE24')]).encode(),
    }
    members = []
    for name, body in files.items():
        (folder / name).write_bytes(body)
        members.append(dict(file=name, size=len(body), sha256=digest(body)))
    manifest = dict(members=members, release=release, scripts=scripts,
                    wiki=dict(id='689120', title='CADE24'))
    tower = dict(source='tower8.py', eager_source='tower8_eager_norm.py',
                 stages=tower_stages(ast.parse(script)))
    return manifest, tower


class SourceTests(unittest.TestCase):
    def test_inventory_runs_on_documentation_only_ci(self):
        workflow = (REPORT.parents[2] / '.github/workflows/ci.yml').read_text()
        step = workflow.split('      - name: Validate committed CADE-24 inventory (offline)\n', 1)[1]
        step = step.split('\n      - ', 1)[0]
        self.assertIn('run: python3 -m unittest scripts/bench/test_real_closure_cade24.py', step)
        self.assertNotIn('\n        if:', step)

    def test_committed_inventory_and_summary(self):
        manifest = json.loads((REPORT / 'source.json').read_text())
        tower = json.loads((REPORT / 'tower8.json').read_text())
        checks = json.loads((REPORT / 'source-checks.json').read_text())
        verify_inventory(manifest, tower, checks)
        for key in ['manifest_sha256', 'tower_inputs_sha256', 'verifier_sha256', 'archive_sha256']:
            with self.subTest(binding=key), self.assertRaises(ValueError):
                verify_inventory(manifest, tower, dict(checks, **{key: '0' * 64}))
        for stage in [0, 2]:
            changed = deepcopy(tower)
            changed['stages'][stage]['coefficients_ascending'][0] = '999'
            updated = dict(checks, tower_inputs_sha256=digest(
                json.dumps(changed, sort_keys=True).encode()))
            with self.subTest(stage=stage), self.assertRaises(ValueError):
                verify_inventory(manifest, changed, updated)

    def test_failed_fetch_is_retryable_without_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / 'source'
            manifest = dict(members=[dict(file='one'), dict(file='two')])
            with patch('scripts.bench.real_closure_cade24.fetch_member') as get:
                get.side_effect = [b'one', ValueError('server failure')]
                with self.assertRaises(ValueError):
                    fetch(target, manifest)
                self.assertFalse(target.exists())
                get.side_effect = [b'one', b'two']
                fetch(target, manifest)
                self.assertEqual((target / 'two').read_bytes(), b'two')
                with self.assertRaises(ValueError):
                    fetch(target, manifest)

    def test_complete_source_verification(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            manifest, tower = fixture(folder)
            result = verify(folder, manifest, tower)
            self.assertEqual(result['tower_degrees'], [2] * 5)
            self.assertTrue(result['clean_eager_identical_except_policy'])

    def test_changed_source_and_transcription(self):
        changes = [
            lambda m, t: m['release'].update(upload_date='wrong'),
            lambda m, t: m['scripts'][0].update(sha256='0' * 64),
            lambda m, t: m['scripts'][0]['root_calls'][0].update(coefficients_ascending='[9]'),
            lambda m, t: m['scripts'][0]['helper_calls'][0].update(arguments=['3']),
            lambda m, t: m['scripts'][0]['bindings'][0].update(targets=['sqrt3']),
            lambda m, t: t['stages'][0].update(returned_root_index=1),
            lambda m, t: t['stages'][2]['coefficients_ascending'].append('0'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            manifest, tower = fixture(folder)
            for index, change in enumerate(changes):
                m, t = deepcopy(manifest), deepcopy(tower)
                change(m, t)
                with self.subTest(index=index), self.assertRaises(ValueError):
                    verify(folder, m, t)
            for member in manifest['members']:
                path = folder / member['file']
                original = path.read_bytes()
                path.write_bytes(original + b'changed')
                with self.subTest(file=path.name), self.assertRaises(ValueError):
                    verify(folder, manifest, tower)
                path.write_bytes(original)

    def test_resealed_incorrect_source_metadata(self):
        changes = [
            ('releaseList.json', lambda rows: rows[0].update(Id='wrong')),
            ('releaseList.json', lambda rows: rows[0].update(Description='different paper')),
            ('releaseList.json', lambda rows: rows[0]['Files'][0].update(Id='wrong')),
            ('documents.json', lambda rows: rows[0].update(Title='different wiki')),
        ]
        for name, change in changes:
            with self.subTest(file=name), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                manifest, tower = fixture(folder)
                path = folder / name
                data = json.loads(path.read_text())
                change(data)
                body = json.dumps(data).encode()
                path.write_bytes(body)
                member = next(item for item in manifest['members'] if item['file'] == name)
                member.update(size=len(body), sha256=digest(body))
                with self.assertRaises(ValueError):
                    verify(folder, manifest, tower)

    def test_resealed_different_eager_program(self):
        policy = b'set_param("rcf.lazy_algebraic_normalization", False)\n'
        changes = [lambda body: body + b'r4 = r4 + 1\n',
                   lambda body: body + b'print(r4 > 0)\n',
                   lambda body: body.replace(policy, b''),
                   lambda body: policy + body,
                   lambda body: body.replace(b'False', b'True')]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                self.check_changed_eager(change)

    def check_changed_eager(self, change):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            manifest, tower = fixture(folder)
            path = folder / 'cade24ex.zip'
            with zipfile.ZipFile(path) as archive:
                files = {name: archive.read(name) for name in archive.namelist()}
            # Updating all archive hashes cannot hide a new arithmetic action.
            name = 'cade24ex/tower8_eager_norm.py'
            files[name] = change(files[name])
            with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED) as archive:
                for key, body in files.items():
                    archive.writestr(key, body)
            item = manifest['scripts'][1]
            item.update(size=len(files[name]), crc32=zlib.crc32(files[name]),
                        sha256=digest(files[name]),
                        root_calls=root_calls(ast.parse(files[name].decode())),
                        helper_calls=helper_calls(ast.parse(files[name].decode())),
                        selections=selections(ast.parse(files[name].decode())),
                        bindings=bindings(ast.parse(files[name].decode())))
            manifest['members'][0].update(size=path.stat().st_size, sha256=digest(path.read_bytes()))
            with self.assertRaises(ValueError):
                verify(folder, manifest, tower)


if __name__ == '__main__':
    unittest.main()
