#!/usr/bin/env python3
"""Six-round absolute fresh-module evidence for min_poly, smith, and hermite.

Every candidate has a preregistered 60-second absolute ceiling. Mathlib has
no corresponding tactic surface. A nonblocking CPU lease selects placement;
no host-activity threshold or retry policy filters completed measurements.
An external JSONL journal preserves each arm immediately, including failures
and timeout output, even if the complete sweep cannot finish.
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import statistics
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep  # noqa: E402

MANIFEST = ROOT / "scripts/bench/structural_tactic_probes.json"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
OWNERS = ("HexMinPolyMathlib", "HexSmithMathlib", "HexHermiteMathlib")


def specification(owner=None):
    cases = json.loads(MANIFEST.read_text())
    pairs = tuple(sweep.ProbePair(
        case["module"], sweep.ProbeModule(case["owner"] + ".ProofProbe.Baseline"),
        sweep.ProbeModule(case["module"], AXIOMS), case)
        for case in cases if owner is None or case["owner"] == owner)
    return sweep.SweepSpec(
        description=__doc__, pairs=pairs, probe_target="HexStructuralTacticProofProbe",
        schema="hex-structural-tactic-probes-v1",
        measurement="paired-fresh-module-olean-wall-absolute-v1",
        output_stem="hex-structural-tactic-probes", required_samples=6, absolute_only=True, retain_compiler_output=True,
        extra_sources=(Path("scripts/bench/structural_tactic_probes.py"),
                       Path("scripts/bench/structural_tactic_probes.json"),
                       *(Path(owner) / "SPEC" / name for owner, name in (
                           ("HexMinPolyMathlib", "hex-min-poly-mathlib.md"),
                           ("HexSmithMathlib", "hex-smith-mathlib.md"),
                           ("HexHermiteMathlib", "hex-hermite-mathlib.md"))),
                       Path("SPEC/matrix-tactics.md"), Path("SPEC/benchmarking.md")))


def acquire_cpu(requested=None):
    cpus = sorted(os.sched_getaffinity(0))
    if requested is not None:
        if requested not in cpus:
            raise RuntimeError("requested CPU is outside the process affinity")
        cpus = [requested]
    else:
        offset = os.getpid() % len(cpus)
        cpus = cpus[offset:] + cpus[:offset]
    for cpu in cpus:
        lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return cpu, lease
        except BlockingIOError:
            lease.close()
    raise RuntimeError("all eligible measurement CPU leases are held")


def compiler_metrics(output):
    timings = re.findall(r"^\s*type checking ([0-9.]+)(ms|s)$", output, re.MULTILINE)
    kernel_seconds = sum(float(value) / (1000 if unit == "ms" else 1) for value, unit in timings)
    certificates = []
    for line in output.splitlines():
        if "[HexMatrix.certificate]" in line:
            certificates.append(json.loads(line[line.index("{"):]))
    return {"kernel_seconds": kernel_seconds, "certificates": certificates}


def write_summary(path):
    record = json.loads(path.read_text())
    evidence = []
    for name, result in record["results"].items():
        metrics = [compiler_metrics(sample["candidate"]["compiler_output"])
                   for sample in result["samples"]]
        if any(not row["certificates"] for row in metrics):
            raise RuntimeError(f"missing certificate measurements: {name}")
        if any(row["certificates"] != metrics[0]["certificates"] for row in metrics):
            raise RuntimeError(f"certificate data changed across samples: {name}")
        evidence.append({"module": name, "family": result["family"],
                         "component": result["component"], "owner": result["owner"],
                         "median_fresh_seconds": result["median_candidate_wall_nanos"] / 1e9,
                         "max_fresh_seconds": result["max_candidate_wall_nanos"] / 1e9,
                         "median_baseline_delta_seconds": result["median_signed_wall_delta_nanos"] / 1e9,
                         "kernel_seconds": [row["kernel_seconds"] for row in metrics],
                         "median_kernel_seconds": statistics.median(row["kernel_seconds"] for row in metrics),
                         "certificates": metrics[0]["certificates"],
                         "artifacts": result["candidate"]["artifacts"],
                         "axioms": result["candidate"]["expected_axioms"],
                         "budget_status": result["fresh_module_budget_status"]})
    path.with_name("certificate-metrics.json").write_text(json.dumps(evidence, indent=2) + "\n")
    lines = ["# Structural tactic proof evidence", "",
             "Comparator status: **no-comparable-surface-in-named-comparator**.", "",
             f"Source commit: `{record['environment']['git_commit']}`. "
             "Each row retains six adjacent, alternating import-baseline/candidate pairs. "
             "The absolute ceiling is 60 seconds per candidate; every completed sample counts.", "",
             "Kernel seconds are Lean's cumulative `type checking` profile. Certificate statistics "
             "and profiler output are included in the measured frontend cost. Full compiler output, "
             "raw timings, source hashes, axiom sets, artifact sizes, and host context are in the JSON.", "",
             "| Module | Fresh median (s) | Fresh max (s) | Paired delta median (s) | Kernel median (s) | Budget |",
             "|---|---:|---:|---:|---:|---|"]
    for row in evidence:
        lines.append(f"| `{row['module']}` | {row['median_fresh_seconds']:.3f} | "
                     f"{row['max_fresh_seconds']:.3f} | {row['median_baseline_delta_seconds']:.3f} | "
                     f"{row['median_kernel_seconds']:.3f} | {row['budget_status']} |")
    path.with_name("summary.md").write_text("\n".join(lines) + "\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--owner", choices=OWNERS)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--directory", type=Path,
                        help="external output directory, outside the measured checkout")
    args, forwarded = parser.parse_known_args(argv)
    directory = (args.directory or Path(tempfile.mkdtemp(prefix="hex-structural-tactics-"))).resolve()
    if directory.is_relative_to(ROOT):
        parser.error("the journal directory must be outside the measured checkout")
    directory.mkdir(parents=True, exist_ok=True)
    cpu, lease = acquire_cpu(args.cpu)
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    spec = specification(args.owner)
    journal = directory / "samples.jsonl"
    if journal.exists():
        parser.error("the evidence directory already contains samples; choose a new directory")
    header = {"environment": sweep.environment(), "source_sha256": sweep.source_hashes(spec, Path(__file__)),
              "samples": 6, "fresh_module_budget_ms": 60_000,
              "comparator_status": "no-comparable-surface-in-named-comparator"}
    journal.write_text(json.dumps({"header": header}) + "\n")

    def observe(module, sample):
        with journal.open("a") as stream:
            stream.write(json.dumps({"module": module, "sample": sample}) + "\n")

    try:
        output = directory / "sweep.json"
        status = sweep.run_cli(spec, Path(__file__), [
            "--shared-host", "--cpu", str(cpu), "--output", str(output), *forwarded],
            sample_observer=observe)
        write_summary(output)
        return status
    except Exception as exc:
        (directory / "failure.json").write_text(json.dumps({"error": str(exc),
            "exception": type(exc).__name__, "release_quality": False}, indent=2) + "\n")
        print(f"Incomplete sweep; retained evidence at {directory}: {exc}", file=sys.stderr)
        return 2
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
