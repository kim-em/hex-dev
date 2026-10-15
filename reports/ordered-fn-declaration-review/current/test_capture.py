"""Controls for independently enumerating the actual Lake library clients."""
import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('orderedfn_capture_tools', BASE / 'normalize.py')
tools = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tools)
HELPER = (ROOT / 'scripts/bench/sweep_freshness.py').read_bytes()


def fixture():
    return {
        'scripts/bench/sweep_freshness.py': HELPER,
        'lakefile.lean': b'''lean_lib Core where
lean_lib Checks where
  srcDir := "conformance"
  globs := #[.one `Checks.Use]
lean_lib Consumer where
  srcDir := "examples"
  globs := #[.submodules `Consumer]
lean_lib Support where
  srcDir := "bench"
  globs := #[`Support.Use].map Glob.one
''',
        'Core.lean': b'public import Core.Value\n',
        'Core/Value.lean': b'def value := 0\n',
        'conformance/Checks/Use.lean': b'public meta import Core\n',
        'examples/Consumer/Use.lean': b'import Core.Value\n',
        'bench/Support/Use.lean': b'import Core.Value\n',
        'bench/Driver.lean': b'import Core.Value\ndef main : IO Unit := pure ()\n',
    }


class CoverageTest(unittest.TestCase):
    def clients(self, files):
        with patch.object(tools, 'sources', return_value=files):
            return tools.library_clients(ROOT, ['Core.Value'])

    def test_configured_library_directories_include_examples_and_support(self):
        required, excluded = self.clients(fixture())
        self.assertEqual(set(required), {'Core', 'Core.Value', 'Checks.Use',
                                         'Consumer.Use', 'Support.Use'})
        self.assertEqual(excluded, {})
        self.assertEqual(required['Checks.Use'], 'conformance/Checks/Use.lean')
        self.assertNotIn('Driver', required)

    def test_new_client_is_discovered_without_an_authored_list(self):
        files = fixture()
        before, _ = self.clients(files)
        files['Core/Future.lean'] = b'import Core.Value\n'
        after, _ = self.clients(files)
        self.assertEqual(set(after) - set(before), {'Core.Future'})

    def test_dot_source_directory_keeps_root_library_modules(self):
        files = fixture()
        files['lakefile.lean'] = files['lakefile.lean'].replace(
            b'lean_lib Core where\n', b'lean_lib Core where\n  srcDir := "."\n')
        required, _ = self.clients(files)
        self.assertIn('Core.Value', required)

    def test_main_exclusion_is_derived_from_source(self):
        files = fixture()
        files['Core/Run.lean'] = b'import Core.Value\ndef main : IO Unit := pure ()\n'
        required, excluded = self.clients(files)
        self.assertNotIn('Core.Run', required)
        self.assertEqual(excluded, {'Core.Run': 'Core/Run.lean'})
        files['Core/Bad.lean'] = b'import Core.Run\n'
        with self.assertRaisesRegex(ValueError, 'imports an executable'):
            self.clients(files)

    def test_literal_concatenation_maps_and_glob_boundaries(self):
        globs = tools.glob_list('#[`A].map Glob.one ++ #[.submodules `B]')
        self.assertEqual(globs, [('one', 'A'), ('submodules', 'B')])
        self.assertFalse(tools.glob_matches(globs[1], 'B'))
        self.assertTrue(tools.glob_matches(globs[1], 'B.C'))
        self.assertFalse(tools.glob_matches(globs[1], 'BC'))
        self.assertEqual(tools.glob_list('#[`A] |>.map Glob.one'), [('one', 'A')])

    def test_unsupported_glob_expressions_are_refused(self):
        for expression in ('#[`A] ++ extra', '#[`A].map Glob.unknown',
                           '#[.one `A].map Glob.one'):
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                tools.glob_list(expression)

    def test_inline_fields_and_multiline_imports_are_refused(self):
        files = fixture()
        files['lakefile.lean'] = b'lean_lib Core where srcDir := "elsewhere"\n'
        with self.assertRaisesRegex(ValueError, 'inline library fields'):
            self.clients(files)
        files = fixture()
        files['Core.lean'] = b'import\n  Core.Value\n'
        with self.assertRaisesRegex(ValueError, 'unsupported import layout'):
            self.clients(files)
        files = fixture()
        files['lakefile.lean'] = b'package sample where\n  srcDir := "elsewhere"\n' + files['lakefile.lean']
        with self.assertRaisesRegex(ValueError, 'package-level srcDir'):
            self.clients(files)

    def test_real_omitted_clients_are_discovered(self):
        modules = ['HexOrderedFn.Search', 'HexOrderedFn.Oracle', 'HexOrderedFn.Real',
                   'HexOrderedFn.Extension', 'HexOrderedFn.Infinitesimal',
                   'HexOrderedFnTheory.Oracle', 'HexOrderedFnTheory.Evaluation',
                   'HexOrderedFnTheory.Real', 'HexOrderedFnTheory.Convergence',
                   'HexOrderedFnTheory.Progress', 'HexOrderedFnTheory.Extension',
                   'HexOrderedFnTheory.Hahn', 'HexOrderedFnTheory.Infinitesimal',
                   'HexOrderedFnTheory.Sign']
        required, excluded = tools.library_clients(ROOT, modules)
        for name in ('RealClosureConsumer.Ordered', 'RealClosureConsumer.Tower',
                     'HexOrderedFn.Conformance', 'HexSignDetTheory.Diagnostics.Nested.Inputs',
                     'HexSignDet.NestedSigns', 'HexSignDet.NestedTables',
                     'HexSignDet.InteractingTrace'):
            self.assertIn(name, required)
        self.assertIn('HexOrderedFnTheory.LiouvilleRun', excluded)

    def test_archive_and_live_scope_distinguish_new_tracked_clients(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path, data in fixture().items():
                destination = root / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(data)
            def git(*arguments):
                return subprocess.check_output(['git', *arguments], cwd=root,
                                               stderr=subprocess.PIPE, text=True).strip()
            git('init', '-q')
            git('add', '.')
            git('-c', 'user.name=Capture Control', '-c', 'user.email=control@example.invalid',
                'commit', '-qm', 'fixture')
            revision = git('rev-parse', 'HEAD')
            (root / 'Core/Future.lean').write_text('import Core.Value\n')
            archived, _ = tools.library_clients(root, ['Core.Value'], revision)
            live, _ = tools.library_clients(root, ['Core.Value'])
            self.assertNotIn('Core.Future', archived)
            self.assertIn('Core.Future', live)
            (root / 'Core/Future.lean').unlink()
            (root / 'Core/Value.lean').unlink()
            with self.assertRaises(FileNotFoundError):
                tools.library_clients(root, ['Core.Value'])

    def test_untracked_unicode_module_is_visible(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path, data in fixture().items():
                destination = root / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(data)
            subprocess.run(['git', 'init', '-q'], cwd=root, check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            (root / 'Core/É.lean').write_text('import Core.Value\n')
            required, _ = tools.library_clients(root, ['Core.Value'])
            self.assertIn('Core.É', required)

    def test_changed_parked_filter_is_refused(self):
        files = tools.sources(ROOT)
        original = b'n.getRoot.toString.startsWith'
        self.assertIn(original, files['lakefile.lean'])
        files['lakefile.lean'] = files['lakefile.lean'].replace(
            original, b'n.getRoot.toString.endsWith')
        with patch.object(tools, 'sources', return_value=files), \
                self.assertRaisesRegex(ValueError, 'unsupported parked glob predicate'):
            tools.library_clients(ROOT, ['HexOrderedFn.Oracle'])


if __name__ == '__main__':
    unittest.main()
