"""Focused tests for the shared HexRCF python-flint bench protocol."""

from __future__ import annotations

import io
import json
import re
import unittest
from pathlib import Path
from unittest import mock

from scripts.oracle import flint_bench_driver as driver
from scripts.oracle import rcf_flint

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


class RcfFlintBenchTests(unittest.TestCase):
    def test_public_decider_handles_constant_sentence(self) -> None:
        sentence = {
            "quantifier": "exists_real",
            "bounds": None,
            "formula": {"tag": "tt"},
        }
        with (
            mock.patch.object(rcf_flint, "_carrier_factors", return_value=[]),
            mock.patch.object(rcf_flint, "_certified_roots", return_value=[]),
        ):
            self.assertTrue(rcf_flint.decide_sentence(sentence))

    def test_driver_delegates_to_shared_decider(self) -> None:
        sentence = {
            "quantifier": "forall_real",
            "bounds": None,
            "formula": {"tag": "ff"},
        }
        with (
            mock.patch.object(driver, "_require_flint"),
            mock.patch.object(driver, "decide_sentence", return_value=False) as decide,
        ):
            self.assertFalse(
                driver._dispatch(
                    {"family": "rcf", "op": "decide", "sentence": sentence}
                )
            )
        decide.assert_called_once_with(sentence)

    def test_driver_requires_sentence_object(self) -> None:
        with mock.patch.object(driver, "_require_flint"):
            with self.assertRaisesRegex(ValueError, "missing object 'sentence'"):
                driver._dispatch(
                    {"family": "rcf", "op": "decide", "sentence": "not-an-object"}
                )

    def test_protocol_reports_error_and_continues(self) -> None:
        sentence = {
            "quantifier": "exists_real",
            "bounds": None,
            "formula": {"tag": "tt"},
        }
        requests = [
            {"family": "rcf", "op": "decide", "sentence": sentence},
            {"family": "rcf", "op": "decide"},
            {"family": "rcf", "op": "decide", "sentence": sentence},
        ]
        stdin = io.StringIO("".join(json.dumps(req) + "\n" for req in requests))
        stdout = io.StringIO()
        with (
            mock.patch.object(driver, "_require_flint"),
            mock.patch.object(driver, "decide_sentence", return_value=True),
        ):
            driver._serve(stdin, stdout)
        replies = [json.loads(line) for line in stdout.getvalue().splitlines()]
        self.assertEqual(replies[0], {"ok": True, "result": True})
        self.assertFalse(replies[1]["ok"])
        self.assertIn("missing object 'sentence'", replies[1]["error"])
        self.assertEqual(replies[2], {"ok": True, "result": True})

    def test_exact_five_paired_registrations(self) -> None:
        source = (REPO_ROOT / "bench" / "HexRCF" / "Bench.lean").read_text(
            encoding="utf-8"
        )
        names = re.findall(
            r"^setup_fixed_benchmark (run(?:Lean|Flint)Decision\d+) where",
            source,
            re.MULTILINE,
        )
        expected = [
            f"run{engine}Decision{degree}"
            for degree in (16, 20, 24, 28, 32)
            for engine in ("Lean", "Flint")
        ]
        self.assertCountEqual(names, expected)
        self.assertIn("minTotalSeconds := 0.2", source)
        self.assertIn("warmupFirstIter := true", source)
        self.assertGreaterEqual(source.count("expectedHash := some (Hashable.hash true)"), 2)


if __name__ == "__main__":
    unittest.main()
