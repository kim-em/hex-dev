#!/usr/bin/env python3
"""Summarize the seven filtered HexMvGcd Phase 4 sampling profiles.

Capture the profiles first with ``scripts/profile/run_profile.sh``. The raw
Firefox profiles and their symbolication sidecars stay under ``/tmp``; this
script commits only the small reproducible analytical summary used by the
headline report.
"""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path
import subprocess

import factor_sampling_profile as sampling


ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports" / "bench-results"
PREFIX = "Hex.MvGcdBench.Profile."

CASES = (
    ("coprime-pairs", "runCoprime"),
    ("dense-gcds", "runDense"),
    ("sparse-stress", "runSparse"),
    ("swell", "runSwell"),
    ("rational", "runRational"),
    ("squarefree", "runSquarefree"),
    ("cofactor-heavy", "runCofactor"),
)


def bench_thread(profile: dict) -> dict:
    """Select the compiled benchmark thread from a filtered samply profile."""
    candidates = [
        thread
        for thread in profile["threads"]
        if "hexmvgcd_bench" in (thread.get("name") or "")
    ]
    if not candidates:
        raise SystemExit("no hexmvgcd_bench thread in the filtered profile")
    return max(candidates, key=lambda thread: thread["samples"]["length"])


def load_diagnostics(path: Path) -> dict:
    diagnostics = json.loads(path.read_text(encoding="utf-8"))
    sensitivity = diagnostics.get("sensitivity") or {}
    return {
        "confidence": diagnostics.get("confidence"),
        "calibration_residual_ms": diagnostics.get("calibration_residual_ms"),
        "total_timed_ms": diagnostics.get("total_timed_ms"),
        "retained_samples": diagnostics.get("retained_samples_bench_thread"),
        "rejected_samples": diagnostics.get("rejected_samples_bench_thread"),
        "off_thread_samples": diagnostics.get("off_bench_thread_samples_in_window"),
        "sensitivity_passed": sensitivity.get("verdict") == "passed",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--profile-dir", type=Path, default=Path("/tmp"),
        help="directory containing run_profile.sh outputs (default: /tmp)",
    )
    parser.add_argument(
        "--output", type=Path,
        default=RESULTS / "hex-mv-gcd-sampling-profiles.json",
    )
    parser.add_argument("--top", type=int, default=20)
    args = parser.parse_args()

    sampling.main_thread = bench_thread
    summaries = []
    for family, short_name in CASES:
        profile_path = args.profile_dir / f"hex-profile-{short_name}-0.json.gz"
        symbols_path = (
            args.profile_dir / f"hex-profile-{short_name}-0.json.syms.json"
        )
        diagnostics_path = Path(str(profile_path) + ".diagnostics.json")
        for path in (profile_path, symbols_path, diagnostics_path):
            if not path.exists():
                raise SystemExit(f"missing profile artifact: {path}")
        with gzip.open(profile_path) as handle:
            profile = json.load(handle)
        analysis = sampling.analyse(
            profile, sampling.Symbolicator(symbols_path), args.top
        )
        summaries.append(
            {
                "family": family,
                "target": PREFIX + short_name,
                "parameter": 0,
                "diagnostics": load_diagnostics(diagnostics_path),
                **analysis,
            }
        )

    commit = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"],
        check=True, capture_output=True, text=True,
    ).stdout.strip()
    record = {
        "schema": "hex-mv-gcd-sampling-profiles/1",
        "config": {
            "git_commit": commit,
            "rate_hz": 999,
            "target_nanos": 3_000_000_000,
            "samply_version": subprocess.run(
                ["samply", "--version"], check=True,
                capture_output=True, text=True,
            ).stdout.strip(),
        },
        "profiles": summaries,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
