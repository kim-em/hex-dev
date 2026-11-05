"""Check runtime retention, hosted-runner guards and exact deletion arguments."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.ci.reclaim_runner_disk import active_paths, main, unused_paths


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

    def test_preserves_path_symlink_to_external_tool(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cached = root / "SDK"
            cached.mkdir()
            tool = cached / "python3"
            tool.symlink_to("/usr/bin/python3")
            self.assertEqual(unused_paths(root, {tool}), [])

    def test_active_paths_preserves_lexical_tool_location(self):
        with tempfile.TemporaryDirectory() as temporary:
            alias = Path(temporary) / "node"
            alias.symlink_to("/usr/bin/python3")
            with patch("scripts.ci.reclaim_runner_disk.shutil.which", return_value=str(alias)):
                self.assertTrue({alias, alias.resolve()}.issubset(active_paths()))

    def test_rejects_self_hosted_deletion(self):
        environment = {"GITHUB_ACTIONS": "true", "RUNNER_ENVIRONMENT": "self-hosted",
                       "RUNNER_OS": "Linux"}
        with patch.dict("os.environ", environment, clear=True), patch("sys.argv", ["cleanup", "--apply"]):
            with self.assertRaises(SystemExit) as error:
                main()
            self.assertEqual(error.exception.code, 2)

    def test_rejects_root_aliases(self):
        for cache in ["/", "//", "/opt/.."]:
            with self.subTest(cache=cache):
                environment = {"GITHUB_ACTIONS": "true", "RUNNER_ENVIRONMENT": "github-hosted",
                               "RUNNER_OS": "Linux", "RUNNER_TOOL_CACHE": cache}
                with patch.dict("os.environ", environment, clear=True), patch("sys.argv", ["cleanup", "--apply"]):
                    with patch("scripts.ci.reclaim_runner_disk.subprocess.run") as run:
                        with self.assertRaises(SystemExit) as error:
                            main()
                        self.assertEqual(error.exception.code, 2)
                        run.assert_not_called()

    def test_deletes_only_selected_cache_entry(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            unused = root / "unused"
            unused.mkdir()
            environment = {"GITHUB_ACTIONS": "true", "RUNNER_ENVIRONMENT": "github-hosted",
                           "RUNNER_OS": "Linux", "RUNNER_TOOL_CACHE": str(root)}
            with patch.dict("os.environ", environment, clear=True), patch("sys.argv", ["cleanup", "--apply"]):
                with patch("scripts.ci.reclaim_runner_disk.subprocess.run") as run:
                    main()
                    run.assert_called_once_with(["sudo", "rm", "-rf", "--", str(unused)], check=True)

    def test_active_python_is_retained(self):
        import sys
        self.assertIn(Path(sys.executable).resolve(), active_paths())


if __name__ == "__main__":
    unittest.main()
