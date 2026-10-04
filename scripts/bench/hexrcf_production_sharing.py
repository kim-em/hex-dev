#!/usr/bin/env python3
"""Retain deterministic syntax counts for actual fixed-field quoted proofs.

This is a structural audit, not a timed benchmark. Lake builds the private-body
inspection module and retains its complete output, source hashes and compiled
proof-module sizes. Imported library declarations remain constant references.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, checkout_state, dependency_checkouts,
    source_hashes,
)

SUITES = {
    "production": ("HexRCF.ProofProbe.Production.Sharing", {
        "Hex.RCF.ProofProbe.Production.closeSections": "Production/Close",
        "Hex.RCF.ProofProbe.Production.furtherSection": "Production/Further",
    }),
    "scaling": ("HexRCF.ProofProbe.Scaling.Sharing", {
        "Hex.RCF.ProofProbe.Scaling." + module + ".positive": "Scaling/" + module
        for module in ("Degree2", "Degree4", "Atoms1", "Atoms4", "Bits32", "Bits128")
    }),
}


def collect(output: Path, suite: str) -> None:
    target, proofs = SUITES[suite]
    spec = SweepSpec(
        description=__doc__,
        pairs=(ProbePair("syntax", ProbeModule(target), ProbeModule(target), {}),),
        probe_target="HexRCFProofProbe",
        schema="hex-rcf-" + suite + "-sharing-v1",
        measurement="deterministic-expression-audit",
        output_stem="hex-rcf-" + suite + "-sharing",
    )
    before = source_hashes(spec, Path(__file__))
    repository = checkout_state(ROOT)
    dependencies = dependency_checkouts()
    output.mkdir(parents=True, exist_ok=False)
    result = subprocess.run(
        ["lake", "build", target], cwd=ROOT, capture_output=True, text=True,
    )
    compiler = result.stdout + result.stderr
    (output / "compiler.log").write_text(compiler)
    if result.returncode:
        raise RuntimeError(f"Lake build failed; retained {output / 'compiler.log'}")
    after = source_hashes(spec, Path(__file__))
    if before != after:
        raise RuntimeError("audit source files changed during the build")
    rows = {}
    for line in compiler.splitlines():
        match = re.search(r"info: .*: (\{.*\})$", line)
        if not match:
            continue
        row = json.loads(match[1])
        proof = row.get("proof")
        if proof not in proofs:
            continue
        if proof in rows:
            raise RuntimeError(f"duplicate proof audit: {proof}")
        if not (0 < row["unique_syntax_nodes"] <= row["local_expression_tree_nodes"]
                <= row["expanded_local_reference_nodes"]):
            raise RuntimeError(f"inconsistent counts: {proof}")
        module = "HexRCF/ProofProbe/" + proofs[proof]
        artifacts = {}
        for suffix in (".olean", ".olean.private", ".olean.server"):
            path = ROOT / ".lake/build/lib/lean" / (module + suffix)
            data = path.read_bytes()
            artifacts[suffix] = {
                "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
            }
        row["module_artifacts"] = artifacts
        rows[proof] = row
    if set(rows) != set(proofs):
        raise RuntimeError(f"missing proof audits: {set(proofs) - set(rows)}")
    data = {
        "schema": spec.schema,
        "measurement": spec.measurement,
        "repository": repository,
        "dependencies": dependencies,
        "source_hashes": before,
        "scope": {
            "local_declarations": "reachable types and bodies in each proof's own module",
            "unique_syntax_nodes": "structurally equal Expr nodes counted once",
            "local_expression_tree_nodes": "expression trees per local declaration, constants as leaves",
            "expanded_local_reference_nodes": "trees with local declaration type/body substituted at each reference",
            "excluded": "imported declaration bodies, universe-level nodes, binder-name nodes, runtime work, heap identity",
        },
        "proofs": [rows[proof] for proof in proofs],
    }
    (output / "audit.json").write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(output / "audit.json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--suite", choices=tuple(SUITES), default="production")
    args = parser.parse_args()
    collect(args.output, args.suite)
