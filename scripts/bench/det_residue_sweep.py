#!/usr/bin/env python3
"""Six fresh-module trials of integer and residue term-list determinant certificates."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

PREFIX = "HexPolyDetMathlib.ProofProbe"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(ProbePair(name, ProbeModule(f"{PREFIX}.HexBaseline"),
        ProbeModule(f"{PREFIX}.{name}", AXIOMS),
        {"component": "symbolic-det", "fresh_module_budget_ms": 45_000,
         "cleanup_timeout_seconds": 45})
        for name in ("Integer4", "Residue4", "ResidueFrobenius")),
    probe_target="HexPolyDetMathlibProofProbe",
    schema="hex-det-residue-probes-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-det-residue-probes",
    required_samples=6,
    absolute_only=True,
    retain_compiler_output=True,
)


def compiler_metrics(module, sample):
    if module.endswith(".HexBaseline"):
        return
    output = sample.get("compiler_output", "")
    hits = re.findall(r"^\s*det.symbolic.kernel ([0-9.e+-]+)(ms|s)$", output, re.MULTILINE)
    if len(hits) != 1:
        raise RuntimeError(f"{module}: expected one synchronous kernel check")
    value, unit = hits[0]
    sample["kernel_ms"] = float(value) * (1 if unit == "ms" else 1000)
    sample["phase_profile_ms"] = {
        name: float(value) * (1 if unit == "ms" else 1000)
        for name, value, unit in re.findall(
            r"^\s*det.symbolic.(\w+) ([0-9.e+-]+)(ms|s)$", output, re.MULTILINE)
    }
    route = "certificate" if module.endswith(".Integer4") else "residue-certificate"
    if f'"route":"{route}"' not in output:
        raise RuntimeError(f"{module}: required certificate route absent")


if __name__ == "__main__":
    if "--timeout" not in sys.argv:
        sys.argv.extend(["--timeout", "45"])
    raise SystemExit(run_cli(SPEC, Path(__file__), sample_observer=compiler_metrics))
