#!/usr/bin/env python3
"""Initial generator precision with constructor and transport setup included.

Each fresh module independently checks its square and selected-root identity,
proves a sentence equivalence, produces a certificate and kernel-replays it.
The common imported baseline (including the original eight-bit target) is
prebuilt. No arm-specific validity or transport proof is prebuilt. This is a
fixed sqrt(2) experiment, not automatic common-field reconstruction or nested
transport. Six trial-major rounds rotate adjacent pairs and alternate AB/BA;
every completed observation is retained on the shared host.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Precision"


def probe(bits: int) -> ProbeModule:
    return ProbeModule(f"HexRCF.ProofProbe.Precision.Full{bits}", AXIOMS, f"{NAMESPACE}.Full{bits}")


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(ProbePair(f"bits-8-{bits}", probe(8), probe(bits), {
        "changed_dimension": "initial_generator_square_precision",
        "reference_bits": 8, "candidate_bits": bits,
        "same_goal": True, "same_selected_root": "positive sqrt(2)",
        "field_degree": 2, "source_atoms": 3, "source_coefficients": 1,
        "maximum_variable_exponent": 2, "generator_refinement_steps": 0,
        "arm_specific_constructor_and_transport_setup_timed": True,
        "proof_acceptance": "Hex.RCF.checkProof: shared fresh auxiliary theorem",
        "axiom_prints_per_arm": 1,
        "untimed_no_refinement_assertion": "Precision.FullAudit",
        "prebuilt_baseline": "same imports and original eight-bit target",
    }) for bits in (16, 32, 64)),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-precision-full-proofs-v2",
    measurement="adjacent-initial-precision-with-setup-olean-wall-v1",
    output_stem="hex-rcf-precision-full-proofs",
    required_samples=6,
    retain_compiler_output=True,
)

def check_sources() -> None:
    """Reject drift in formula, options, imports or proof acceptance between arms."""
    normalized = []
    for bits in (8, 16, 32, 64):
        source = (ROOT / f"bench/HexRCF/ProofProbe/Precision/Full{bits}.lean").read_text()
        source, count = re.subn(
            r"⟨Dyadic.ofInt \d+ >>> \(\d+ : Int\), 0, \d+⟩", "SQUARE", source)
        if count != 1:
            raise ValueError(f"Full{bits}: expected exactly one initial square")
        source = re.sub(r"Full(?:8|16|32|64)\b", "FullN", source)
        source = re.sub(r"precision_build(?:8|16|32|64)\b", "precision_buildN", source)
        normalized.append(source)
    if len(set(normalized)) != 1:
        raise ValueError("precision arms differ beyond the square and arm names")


if __name__ == "__main__":
    check_sources()
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
