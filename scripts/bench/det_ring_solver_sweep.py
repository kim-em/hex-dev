#!/usr/bin/env python3
"""Compare Mathlib ``ring`` with core ``grobner`` on closed determinant forms."""

from __future__ import annotations

import fcntl
import os
import re
import statistics
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule,
    ProbePair,
    SweepSpec,
    run_cli,
)
from scripts.bench.det_ring_solver_probes import CASES, PREFIX  # noqa: E402


GRIND_AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def ring_axioms(stem: str) -> tuple[str, ...]:
    if "Rational" in stem:
        return GRIND_AXIOMS
    if stem == "RingSolverInteger2":
        return ("propext", "Quot.sound")
    return ("propext",)


def family(stem: str) -> str:
    for name in ("Integer", "Rational", "Power"):
        if name in stem:
            return name.lower()
    raise ValueError(stem)


def dimension(stem: str) -> int:
    return int(stem[-1])


SPEC = SweepSpec(
    description=__doc__ or "closed determinant ring-solver comparison",
    pairs=tuple(
        ProbePair(
            stem,
            ProbeModule(f"{PREFIX}.{stem}Ring", ring_axioms(stem)),
            ProbeModule(f"{PREFIX}.{stem}Grobner", GRIND_AXIOMS),
            {"family": family(stem), "dimension": dimension(stem)},
        )
        for stem, _binders, _target in CASES
    ),
    probe_target="HexPolyDetMathlibProofProbe",
    schema="hex-poly-det-ring-solver-v1",
    measurement="paired-fresh-module-profiler-ring-vs-grobner",
    output_stem="hex-poly-det-ring-solver",
    required_samples=6,
    retain_compiler_output=True,
    extra_sources=(Path("scripts/bench/det_ring_solver_probes.py"),),
)


def profile_milliseconds(output: str, name: str) -> float:
    matches = re.findall(
        rf"^\s*{re.escape(name)}\s+([0-9]+(?:\.[0-9]+)?)(ms|s|us|μs|ns)$",
        output,
        flags=re.MULTILINE,
    )
    if not matches:
        raise ValueError(f"missing profiler counter {name!r}")
    value, unit = matches[-1]
    scale = {
        "s": 1000.0,
        "ms": 1.0,
        "us": 0.001,
        "μs": 0.001,
        "ns": 0.000001,
    }[unit]
    return float(value) * scale


def print_table(path: Path) -> None:
    import json

    record = json.loads(path.read_text())
    print(
        "| Case | ring kernel ms | grobner kernel ms | "
        "ring elaboration ms | grobner elaboration ms |"
    )
    print("|---|---:|---:|---:|---:|")
    for name, result in record["results"].items():
        samples = result["samples"]
        values = {}
        for role in ("reference", "candidate"):
            values[role] = {
                counter: statistics.median(
                    profile_milliseconds(sample[role]["compiler_output"], counter)
                    for sample in samples
                )
                for counter in ("type checking", "elaboration")
            }
        print(
            f"| {name} | {values['reference']['type checking']:.3f} | "
            f"{values['candidate']['type checking']:.3f} | "
            f"{values['reference']['elaboration']:.3f} | "
            f"{values['candidate']['elaboration']:.3f} |"
        )


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "--table":
        print_table(Path(sys.argv[2]))
        return 0
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
        return run_cli(SPEC, Path(__file__))
    finally:
        if lease is not None:
            lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
