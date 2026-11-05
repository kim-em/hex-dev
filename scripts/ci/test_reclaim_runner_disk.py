"""Check that runner cleanup preserves active tools and follows no deletion links."""
from pathlib import Path
import tempfile
import unittest

from scripts.ci.reclaim_runner_disk import active_paths, unused_paths


class ReclaimRunnerDiskTests(unittest.TestCase):
    def test_preserves_active_prefixes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            python = root / "Python" / "3.14" / "bin" / "python3"
            node = root / "node" / "bin" / "node"
            for tool in [python, node]:
                tool.parent.mkdir(parents=True)
                tool.touch()
            unused = root / "go"
            unused.mkdir()
            self.assertEqual(unused_paths(root, {python, node}), [unused])

    def test_preserves_resolved_runtime_alias(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            runtime = root / "runtime"
            runtime.mkdir()
            executable = runtime / "python3"
            executable.touch()
            alias = root / "alias"
            alias.symlink_to(runtime, target_is_directory=True)
            unused = root / "unused"
            unused.mkdir()
            self.assertEqual(unused_paths(root, {executable}), [unused])

    def test_external_tools_do_not_keep_unused_caches(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            unused = root / "SDK"
            unused.mkdir()
            self.assertEqual(unused_paths(root, {Path("/usr/bin/python3")}), [unused])

    def test_missing_cache_is_empty(self):
        with tempfile.TemporaryDirectory() as temporary:
            self.assertEqual(unused_paths(Path(temporary) / "missing", set()), [])

    def test_active_python_is_retained(self):
        import sys
        self.assertIn(Path(sys.executable).resolve(), active_paths())


if __name__ == "__main__":
    unittest.main()
