#!/usr/bin/env python3
"""Run shared-host real-formula evidence through the existing benchmark harnesses."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
BASELINE = ProbeModule("HexRealFormulaMathlib.ProofProbe.Baseline")
SPEC = SweepSpec(
    description="Shared real-formula reification, normalization and RCF adapter builds",
    pairs=tuple(
        ProbePair(name.lower(), BASELINE,
                  ProbeModule(f"HexRealFormulaMathlib.ProofProbe.{name}", AXIOMS),
                  {"component": component})
        for name, component in [
            ("Parameterized", "parameterized-reification-and-kernel-proof"),
            ("Alternation", "biconditional-prenex-reification-and-kernel-proof"),
            ("Normalization", "semantic-normalization-proof"),
        ]
    ) + (ProbePair(
        "adapter", ProbeModule("HexRCF.RealFormulaProbe.Baseline"),
        ProbeModule("HexRCF.RealFormulaProbe.Adapter", AXIOMS),
        {"component": "half-open-cubic-RCF-correspondence-proof"}),),
    probe_target="HexRealFormulaProofProbe",
    schema="hex-real-formula-proof-probes-v1",
    measurement="adjacent-fresh-module-builds",
    output_stem="hex-real-formula-proofs",
    required_samples=4,
    retain_compiler_output=True,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("track", choices=["compiled", "proofs"])
    parser.add_argument("--output", type=Path, required=True)
    args, forwarded = parser.parse_known_args()
    os.chdir(ROOT)
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            lease.close()
    else:
        raise RuntimeError("all measurement CPU leases are held")
    try:
        if args.track == "proofs":
            return run_cli(SPEC, Path(__file__), [
                "--shared-host", "--cpu", str(cpu), "--output", str(args.output), *forwarded])
        os.sched_setaffinity(0, {cpu})
        args.output.parent.mkdir(parents=True, exist_ok=True)
        command = [".lake/build/bin/hexrealformula_bench", "run", "--filter",
                   "Hex.RealFormula.Bench", "--export-file", str(args.output), *forwarded]
        paths = [Path("bench/HexRealFormula/Bench.lean"), Path("HexRealFormula.lean"),
                 *sorted(Path("HexRealFormula").glob("*.lean")),
                 Path("HexMvPoly/Mono.lean"), Path("HexMvPoly/Kernel.lean"),
                 Path("scripts/bench/real_formula_sweep.py"), Path("lean-toolchain"),
                 Path("lake-manifest.json")]
        context = {
            "command": command, "cpu": cpu, "host": platform.node(),
            "platform": platform.platform(), "load": os.getloadavg(),
            "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
            "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"])),
            "source_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        }
        args.output.with_suffix(".context.json").write_text(json.dumps(context, indent=2) + "\n")
        return subprocess.run(command).returncode
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
