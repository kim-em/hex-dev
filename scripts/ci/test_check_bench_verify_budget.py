from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts/ci/check_bench_verify_budget.sh"
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from libgraph import load_libraries


class CheckBenchVerifyBudgetTests(unittest.TestCase):
    def run_script(
        self, *arguments: str, library_filter: str
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as directory:
            fake_lake = Path(directory) / "lake"
            fake_lake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lake.chmod(0o755)
            env = os.environ.copy()
            env.update(
                {
                    "PATH": f"{directory}:{env['PATH']}",
                    "HEX_LIBRARY_FILTER": library_filter,
                    "BENCH_VERIFY_HARD_CAP_SECONDS": "0",
                    "GITHUB_ACTIONS": "false",
                }
            )
            return subprocess.run(
                ["bash", str(SCRIPT), *arguments],
                cwd=REPO_ROOT,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )

    def test_filter_uses_explicit_library_owner(self) -> None:
        result = self.run_script(
            "HexPoly=hexpoly_bench",
            "HexRoots=hexroots_bench",
            "HexGF2=hexgf2_bench",
            library_filter="HexRoots",
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("::group::hexroots_bench", result.stdout)
        self.assertNotIn("::group::hexpoly_bench", result.stdout)
        self.assertNotIn("::group::hexgf2_bench", result.stdout)

    def test_filtered_legacy_argument_fails_closed(self) -> None:
        result = self.run_script("hexroots_bench", library_filter="HexRoots")
        self.assertEqual(result.returncode, 2)
        self.assertIn("filtered runs require Library=bench_executable", result.stdout)

    def test_workflow_pairs_match_lake_roots(self) -> None:
        workflow = (REPO_ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        block = workflow.split(
            "bash scripts/ci/check_bench_verify_budget.sh \\\n", 1
        )[1].split("          # These two interval", 1)[0]
        pairs = re.findall(r"\b(Hex[A-Za-z0-9]+)=([a-z0-9_]+_bench)\b", block)
        self.assertEqual(len(pairs), 47)

        lakefile = (REPO_ROOT / "lakefile.lean").read_text(encoding="utf-8")
        roots = dict(
            re.findall(
                r"lean_exe\s+([a-zA-Z0-9_]+)\s+where\s*\n"
                r"(?:\s+.*\n)*?\s+root\s*:=\s*`([A-Za-z0-9_.]+)",
                lakefile,
            )
        )
        library_names = set(load_libraries())
        for owner, executable in pairs:
            with self.subTest(executable=executable):
                root = roots[executable].replace(".", "").lower()
                candidates = [
                    library
                    for library in library_names
                    if root.startswith(library.lower())
                ]
                self.assertEqual(max(candidates, key=len), owner)


if __name__ == "__main__":
    unittest.main()
