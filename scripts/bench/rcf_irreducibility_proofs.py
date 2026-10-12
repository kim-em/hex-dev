#!/usr/bin/env python3
"""Compare reconstruction and imported reuse of one supplied RCF proof.

Both fresh modules prove the same degree-eight common-field sentence with
matched imports, including the owner's private executable factorizer closure.
Only the reference reconstructs its irreducibility theorem. This diagnoses
construction cost; it is neither automatic-certification evidence nor a
comparison of the ordinary-import consumer's smaller dependency cone.
"""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule,
    ProbePair,
    SweepSpec,
    run_retained_cli,
)

PREFIX = "HexRCF.ProofProbe.Supplied"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__ or "Supplied RCF irreducibility proof cost",
    pairs=(ProbePair(
        "octic-construction-reuse",
        ProbeModule(f"{PREFIX}.Reconstruct", AXIOMS,
                    "Hex.RCF.ProofProbe.Supplied.Reconstruct"),
        ProbeModule(f"{PREFIX}.Reuse", AXIOMS,
                    "Hex.RCF.ProofProbe.Supplied.Reuse"),
        {
            "question": "cost of reconstructing versus importing the same irreducibility proof",
            "common_field_degree": 8,
            "sentence_degree": 2,
            "atoms": 1,
            "goal": "forall x : Real, x^2 + selected_quartic + sqrt(2) > 0",
            "matched_imports": "both include the owner private executable closure",
            "construction_heartbeats": 8_000_000,
            "tactic_heartbeats": "default",
            "recursion_limit": 32768,
        },
    ),),
    probe_target="HexRCFProofProbeMeasurements",
    schema="hex-rcf-supplied-irreducibility-proofs-v1",
    measurement="adjacent-alternating-fresh-module-build",
    output_stem="hex-rcf-supplied-irreducibility-proofs",
    extra_sources=(
        Path("adapters/HexRCF/RealCoefficients/CommonTactic.lean"),
        Path("conformance/HexRCF/SuppliedIrreducible.lean"),
        Path("HexRCF/SPEC/hex-rcf.md"),
        Path("scripts/bench/cpu_lease.py"),
    ),
    required_samples=4,
    retain_compiler_output=True,
)

def check_imports() -> None:
    """Refuse an unmatched import cone before collecting any samples."""
    headers = []
    for name in ("Reconstruct", "Reuse"):
        source = (ROOT / "bench/HexRCF/ProofProbe/Supplied" / f"{name}.lean").read_bytes()
        header, separator, _body = source.partition(b"public section")
        if not separator:
            raise ValueError(f"{name}: missing public section boundary")
        headers.append(header)
    if headers[0] != headers[1]:
        raise ValueError("supplied-proof probes have different import headers")


if __name__ == "__main__":
    check_imports()
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
