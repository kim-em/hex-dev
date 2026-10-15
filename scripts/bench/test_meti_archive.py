"""Validate the actual capture and reject forged bindings after resealing."""
from copy import deepcopy
import gzip
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest

from scripts.bench.archive_meti_counts import ARCHIVE, document, sha, unpack, verify

ROOT = Path(__file__).resolve().parents[2]


class ArchiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = ROOT / ARCHIVE
        cls.files = unpack(cls.folder / 'capture.tar.gz')
        cls.index = document((cls.folder / 'archive.json').read_bytes())

    def test_actual_archive(self):
        result = verify(self.folder)
        self.assertEqual(result['source'], 'bff9b56cb6f222df142433a351409c0fd046c969')
        self.assertEqual((result['commands'], result['instrumented_modules'], result['linked_inputs']),
                         (20, 23, 421))
        self.assertEqual([r['poly_gcd'] for r in result['rows']], [19]*4)
        self.assertEqual([r['gmp_gcd'] for r in result['rows']],
                         [448870, 767726, 1200769, 1748034])

    def changed(self, mutate, expected):
        """Reseal both artifact indexes so tests reach the semantic bindings."""
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            for name in ['README.md', 'analysis.json', 'recipes.json']:
                shutil.copyfile(self.folder / name, folder / name)
            files, index = dict(self.files), deepcopy(self.index)
            mutate(files, index, folder)
            record = document(files['manifest.json'])
            for name in set(files) & set(record['artifacts']):
                record['artifacts'][name] = sha(files[name])
            files['manifest.json'] = json.dumps(record).encode()
            with (folder / 'capture.tar.gz').open('wb') as out, gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as zipped:
                with tarfile.open(fileobj=zipped, mode='w') as archive:
                    for name, data in files.items():
                        entry = tarfile.TarInfo(name)
                        entry.size = len(data)
                        archive.addfile(entry, io.BytesIO(data))
            index['files'] = {name: sha(data) for name, data in files.items()}
            index['archive_sha256'] = sha((folder / 'capture.tar.gz').read_bytes())
            index['recipes_sha256'] = sha((folder / 'recipes.json').read_bytes())
            (folder / 'archive.json').write_text(json.dumps(index))
            with self.assertRaisesRegex(ValueError, expected):
                verify(folder)

    @staticmethod
    def change_json(files, name, mutate):
        value = document(files[name])
        mutate(value)
        files[name] = json.dumps(value).encode()

    def test_manifest_protocol_and_bindings(self):
        changes = [
            lambda d: d.update(warmup=True),
            lambda d: d.update(rows=d['rows'][:-1]),
            lambda d: d['commands'][8]['argv'].__setitem__(2, '/other/10.stdout'),
            lambda d: d['commands'][7].update(exit_code=-9),
            lambda d: d['rows'][0]['observed']['counts'].update(poly_gcd=20),
            lambda d: d.update(source_hashes={}),
            lambda d: d.update(diagnostic_sha256='0'*64),
        ]
        messages = ['changed capture protocol', 'incomplete capture schedule', 'changed executed input',
                    'incomplete or changed command', 'changed counter/summary binding',
                    'changed source inventory', 'unexpected omitted snapshot']
        for change, message in zip(changes, messages):
            with self.subTest(change=change):
                self.changed(lambda f, i, p: self.change_json(f, 'manifest.json', change), message)

    def test_build_and_omitted_snapshot_bindings(self):
        changes = [
            lambda b: b.update(source_head='0'*40),
            lambda b: b['objects'][0].update(functions=[]),
            lambda b: b['commands'][1].__setitem__(4, '/other/source.c'),
            lambda b: b['link_inputs'].pop(next(iter(b['link_inputs']))),
            lambda b: b['commands'][-1].append('/other/unrecorded.o'),
            lambda b: b.update(observer_object_sha256='0'*64),
        ]
        messages = ['changed build/source/category binding', 'changed C instrumentation',
                    'changed module compiler recipe', 'changed recipe object identities',
                    'changed ordered linker recipe', 'unexpected omitted snapshot']
        for change, message in zip(changes, messages):
            with self.subTest(change=change):
                self.changed(lambda f, i, p: self.change_json(f, 'build/build.json', change), message)
        self.changed(lambda f, i, p: i['omitted_snapshots'].update(ordinary='0'*64), 'unexpected omitted snapshot')
        self.changed(lambda f, i, p: i['omitted_snapshots'].update(**{'7.stdout': sha(f.pop('7.stdout'))}),
                     'unexpected omitted snapshot')

    def test_generated_c_reconstruction_and_injection(self):
        for change in ['original-token', 'counter-number']:
            def mutate(files, index, folder):
                name = 'build/3.c'
                raw = files[name]
                files[name] = (raw + b'\n/* changed original */\n' if change == 'original-token' else
                               raw.replace(b'hex_meti_count(1);', b'hex_meti_count(0);', 1))
                self.assertNotEqual(raw, files[name])
                self.change_json(files, 'build/build.json',
                                 lambda b: b['objects'][0].update(observer_c_sha256=sha(files[name])))
            with self.subTest(change=change):
                self.changed(mutate, 'changed original C identity' if change == 'original-token' else
                             'changed C instrumentation')

    def test_packet_oracle_and_counter_bindings(self):
        self.changed(lambda f, i, p: f.__setitem__('7.stdout', f['10.stdout']), 'functional packet differs')
        self.changed(lambda f, i, p: self.change_json(f, '8.stdout', lambda d: d.update(descriptor_bytes=1)),
                     'changed oracle/packet binding')
        self.changed(lambda f, i, p: f.__setitem__('7.stderr', f['7.stderr'].replace(b'"poly_gcd":19', b'"poly_gcd":20')),
                     'changed counter/summary binding')
        self.changed(lambda f, i, p: f.__setitem__('7.stderr', f['7.stderr'] + b'METI BEGIN\n'),
                     'incomplete or duplicate counter region')
        self.changed(lambda f, i, p: f.__setitem__('6.stderr', b''), 'changed ordinary region')
        self.changed(lambda f, i, p: f.__setitem__('sources/scripts/bench/meti_counts.py', b'changed'),
                     'changed frozen source binding')

    def test_derived_results_and_unexpected_members(self):
        self.changed(lambda f, i, p: (p / 'analysis.json').write_text('{}'), 'changed derived analysis')
        self.changed(lambda f, i, p: (p / 'README.md').write_text('changed'), 'changed reported counts')
        self.changed(lambda f, i, p: f.update(extra=b'unrecorded'), 'changed retained artifact inventory')

    def test_exact_link_and_compile_recipes(self):
        def swap_link(b):
            link = b['commands'][-1]
            link[3], link[4] = link[4], link[3]
        changes = [
            (swap_link, 'changed ordered linker recipe'),
            (lambda b: b['commands'][-1].remove('-lgmp'), 'changed ordered linker recipe'),
            (lambda b: b['commands'][-1].__setitem__(0, '/other/compiler'), 'changed ordered linker recipe'),
            (lambda b: b['commands'][1].__setitem__(b['commands'][1].index('-O3'), '-O0'),
             'changed module compiler recipe'),
            (lambda b: b['commands'][-2].append('-DCHANGED'), 'changed observer compiler recipe')]
        for change, message in changes:
            with self.subTest(message=message):
                self.changed(lambda f, i, p: self.change_json(f, 'build/build.json', change), message)
        def changed_rsp(files, index, folder):
            path = folder / 'recipes.json'
            value = document(path.read_bytes())
            value['link_rsp'] += ' -lchanged'
            path.write_text(json.dumps(value))
        self.changed(changed_rsp, 'changed original link response')

    def test_setup_and_full_oracle_paths(self):
        changes = [lambda d: d['commands'][1].update(argv=['printf', '']),
                   lambda d: d['commands'][8]['argv'].__setitem__(2, '/elsewhere/7.stdout'),
                   lambda d: d['commands'][7]['argv'].__setitem__(0, '/elsewhere/metitarski-counts')]
        for change, message in zip(changes, ['changed setup command', 'changed executed input', 'changed executed input']):
            self.changed(lambda f, i, p: self.change_json(f, 'manifest.json', change), message)

    def test_tar_member_safety(self):
        for names, kind in [(['../escape'], tarfile.REGTYPE), (['/absolute'], tarfile.REGTYPE),
                            (['duplicate', 'duplicate'], tarfile.REGTYPE), (['link'], tarfile.SYMTYPE)]:
            with self.subTest(names=names), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'bad.tar.gz'
                with tarfile.open(path, 'w:gz') as archive:
                    for name in names:
                        entry = tarfile.TarInfo(name)
                        entry.type = kind
                        archive.addfile(entry)
                with self.assertRaises(ValueError):
                    unpack(path)


if __name__ == '__main__':
    unittest.main()
