#!/usr/bin/env python3
"""Compare linear and indexed sign lookup in finite algebraic proof replay.

The two fresh modules prove the same original quartic/sqrt(2) sentence with
matched imports and options. Only rcf.algebraic.indexSigns differs. Timings
include source preparation, production, quotation and ordinary kernel proof
acceptance; they are build-only observations, not executable benchmarks or
evidence of decision completeness or a scaling law.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

PREFIX = "HexRCF.ProofProbe.FiniteSigns"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__ or "Finite algebraic sign lookup proof cost",
    pairs=(ProbePair(
        "linear-indexed-common-octic",
        ProbeModule(f"{PREFIX}.Linear", AXIOMS, "Hex.RCF.ProofProbe.FiniteSigns.Linear"),
        ProbeModule(f"{PREFIX}.Indexed", AXIOMS, "Hex.RCF.ProofProbe.FiniteSigns.Indexed"),
        {
            "question": "cost of indexed retrieval in the finite-cell proof checker",
            "coefficient_field_degree": 8,
            "sentence_degree": 2,
            "atoms": 3,
            "carrier_roots": 4,
            "matched_imports": "RealCoefficients and CertificationInputs, ordinary and meta",
            "heartbeats": 40_000_000,
            "recursion_limit": 32768,
            "scope": "fixed selected quartic and positive square-root inputs; full tactic",
        },
    ),),
    probe_target="HexRCFProofProbeMeasurements",
    schema="hex-rcf-finite-signs-v1",
    measurement="adjacent-alternating-fresh-module-build",
    output_stem="hex-rcf-finite-signs",
    extra_sources=(Path("scripts/bench/cpu_lease.py"),),
    required_samples=4,
    retain_compiler_output=True,
)


def check_sources() -> None:
    headers = []
    bodies = []
    for arm, indexed in (("Linear", "false"), ("Indexed", "true")):
        path = ROOT / "bench/HexRCF/ProofProbe/FiniteSigns" / f"{arm}.lean"
        header, separator, body = path.read_text().partition(
            f"namespace Hex.RCF.ProofProbe.FiniteSigns.{arm}"
        )
        if not separator:
            raise ValueError(f"{arm}: missing namespace boundary")
        headers.append(header)
        bodies.append(body.replace(f"rcf.algebraic.indexSigns {indexed}",
                                  "rcf.algebraic.indexSigns CONTROL").replace(
                                      f"FiniteSigns.{arm}", "FiniteSigns.ARM"))
    if headers[0] != headers[1] or bodies[0] != bodies[1]:
        raise ValueError("finite sign probes differ beyond namespace and lookup option")


if __name__ == "__main__":
    check_sources()
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
