#!/usr/bin/env python3
"""Fresh ordinary-kernel π/exp(1) source proofs, with matched public imports.

Four adjacent AB/BA rounds at each precision. The 60-second absolute ceiling
is an operational acceptance bound on this shared host, not a complexity claim.
"""
from pathlib import Path
import fcntl
import os
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

PREFIX = "HexIntervalMathlib.Constants."
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__ or "",
    pairs=tuple(ProbePair(
        f"precision-{k}", ProbeModule(PREFIX + "Baseline"),
        ProbeModule(PREFIX + f"Precision{k}", AXIOMS),
        {"precision": k, "pi_order": pn, "exp_order": en,
         "fresh_module_budget_ms": 60_000, "cleanup_timeout_seconds": 120},
    ) for k, pn, en in ((2, 2, 4), (8, 4, 8), (16, 8, 12))),
    probe_target="HexIntervalMathlibReplayProbe",
    schema="hex-interval-constants-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-interval-constants-probes",
    extra_sources=(Path("HexIntervalMathlib/Elementary/Constants.lean"),
                   Path("HexIntervalMathlib/Elementary/ExpLog.lean")),
    required_samples=4, absolute_only=True, retain_compiler_output=True,
)

if __name__ == "__main__":
    lease = None
    if "--shared-host" in sys.argv and not any(
        arg == "--cpu" or arg.startswith("--cpu=") for arg in sys.argv
    ):
        cpus = sorted(os.sched_getaffinity(0))
        offset = os.getpid() % len(cpus)
        for cpu in cpus[offset:] + cpus[:offset]:
            lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
            try:
                fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
                sys.argv.extend(["--cpu", str(cpu)])
                break
            except BlockingIOError:
                lease.close()
        else:
            raise RuntimeError("all measurement CPU leases are held")
    try:
        raise SystemExit(run_cli(SPEC, Path(__file__)))
    finally:
        if lease is not None:
            lease.close()
