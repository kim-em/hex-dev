#!/usr/bin/env python3
"""Compare Mathlib ``ring`` with core ``grobner`` on closed determinant forms."""

from __future__ import annotations

import argparse
from dataclasses import replace
import fcntl
import gzip
import json
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
from scripts.bench.det_ring_solver_probes import CASES, PREFIX, RING_AXIOMS  # noqa: E402
from scripts.bench import fresh_module_sweep as sweep  # noqa: E402


GRIND_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
CAPABILITIES = (
    ProbeModule(f"{PREFIX}.RingSolverAlgebraic", GRIND_AXIOMS),
    ProbeModule(f"{PREFIX}.RingSolverVariableExponent", ("propext",)),
)


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
            ProbeModule(f"{PREFIX}.{stem}Ring", RING_AXIOMS[stem]),
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
    extra_sources=(
        Path("scripts/bench/det_ring_solver_probes.py"),
        *(Path("bench/HexPolyDetMathlib/ProofProbe") / f"{name}.lean"
          for name in ("RingSolverAlgebraic", "RingSolverVariableExponent", "AlgebraicSupport")),
    ),
)


def profile_milliseconds(output: str, name: str) -> float:
    if "cumulative profiling times:" not in output:
        raise ValueError("missing cumulative profiler block")
    output = output.rsplit("cumulative profiling times:", 1)[1]
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
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            record = json.load(stream)
    else:
        record = json.loads(path.read_text(encoding="utf-8"))
    print(
        "| Family / n | ring wall | grobner wall | ring kernel | "
        "grobner kernel | ring elaboration | grobner elaboration |"
    )
    print("|---|---:|---:|---:|---:|---:|---:|")
    labels = {"integer": "integer", "rational": "rational", "power": "fixed powers"}
    for result in sorted(record["results"].values(), key=lambda r: (
        list(labels).index(r["family"]), r["dimension"]
    )):
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
            f"| {labels[result['family']]} / {result['dimension']} | "
            f"{result['median_reference_wall_nanos'] / 1e6:.2f} | "
            f"{result['median_candidate_wall_nanos'] / 1e6:.2f} | "
            f"{values['reference']['type checking']:.3f} | "
            f"{values['candidate']['type checking']:.3f} | "
            f"{values['reference']['elaboration']:.3f} | "
            f"{values['candidate']['elaboration']:.3f} |"
        )


def record_capabilities(path: Path, timeout: float = 60, warm_timeout: float = 600) -> int:
    """Retain fresh capability builds separately from the timing experiment."""
    env = sweep.environment()
    dirt = sweep.dirty_issues(dict(env["repository"]), dict(env["dependency_checkouts"]))
    if dirt:
        raise RuntimeError("dirty capability environment: " + "; ".join(dirt))
    hashes = sweep.source_hashes(SPEC, Path(__file__))
    warm_spec = replace(SPEC, pairs=(ProbePair("capabilities",
        CAPABILITIES[0], CAPABILITIES[1], {}),))
    sweep.warm_imports(warm_spec, warm_timeout)
    results = []
    for module in CAPABILITIES:
        observed = []
        try:
            sample = sweep.build_sample(module.module, timeout,
                sample_observer=lambda _m, r: observed.append(r), retain_compiler_output=True)
            sweep.validate_axioms(module.module, "capability", module, sample)
            results.append(dict(module=module.module, state="complete",
                command=["lake", "build", f"+{module.module}:olean"], **sample))
        except RuntimeError as exc:
            results.append(dict(module=module.module, state="failed", error=str(exc),
                sample=observed[-1] if observed else None))
    unchanged = hashes == sweep.source_hashes(SPEC, Path(__file__))
    complete = unchanged and all(r["state"] == "complete" for r in results)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(dict(schema="hex-poly-det-ring-capabilities-v1",
        environment=env, source_sha256=hashes, sources_unchanged=unchanged,
        complete=complete, results=results), indent=2, sort_keys=True) + "\n")
    print(path)
    return 0 if complete else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, add_help=False)
    parser.add_argument("--table", type=Path)
    parser.add_argument("--capabilities", type=Path)
    parser.add_argument("--shared-host", action="store_true")
    parser.add_argument("--cpu", type=int)
    args, forwarded = parser.parse_known_args(argv)
    if args.table:
        print_table(args.table)
        return 0
    if args.capabilities:
        options = sweep.parse_args(__doc__ or "capability probes", forwarded)
        return record_capabilities(args.capabilities, options.timeout, options.warm_timeout)
    lease = None
    cpu = args.cpu
    if args.shared_host and cpu is None:
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
        options = (["--shared-host"] if args.shared_host else [])
        if cpu is not None:
            options.extend(["--cpu", str(cpu)])
        return run_cli(SPEC, Path(__file__), [*options, *forwarded])
    finally:
        if lease is not None:
            lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
