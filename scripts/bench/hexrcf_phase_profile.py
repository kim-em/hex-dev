#!/usr/bin/env python3
"""Retain one ordinary-kernel fixed-field proof attribution sample.

Lean's profiler reports exclusive category times. This is a representative
attribution, not a timing comparison or a precision/depth scaling claim.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.fresh_module_sweep import (
    ProbeModule, ProbePair, SweepSpec, artifact_sizes, build_sample,
    configure_shared_host, cpu_topology, environment, parse_cpu_list,
    source_hashes, validate_axioms,
)

PROBE = ProbeModule("HexRCF.ProofProbe.Profiling",
                    ("propext", "Classical.choice", "Quot.sound"),
                    "Hex.RCF.ProofProbe.Profiling")
# The record supplies the import closure to the common provenance walker.
# No pair sweep runs: this collector executes exactly one attribution sample.
SOURCES = SweepSpec(__doc__, (ProbePair("attribution", PROBE, PROBE, {}),),
                    "HexRCFProofProbe", "hex-rcf-phase-profile-v1",
                    "single-exclusive-profile", "hex-rcf-phase-profile",
                    extra_sources=(Path("scripts/bench/cpu_lease.py"),))


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    if args.output.exists():
        raise RuntimeError("output already exists; completed samples are immutable")
    args.output.mkdir(parents=True)
    cpu, lease = cpu_lease(args.cpu)
    try:
        configure_shared_host(argparse.Namespace(shared_host=True, cpu=cpu))
        initial = environment()
        if initial["git_dirty"]:
            raise RuntimeError("commit the measured source before profiling")
        before = source_hashes(SOURCES, Path(__file__))
        # Warm dependencies only; do not run the profiled theorem as warmup.
        warm = subprocess.run(["lake", "build", "HexRCFRealCoefficients"],
                              cwd=ROOT, text=True, capture_output=True,
                              timeout=args.timeout)
        (args.output / "warm.log").write_text(warm.stdout + warm.stderr)
        if warm.returncode:
            raise RuntimeError("dependency warm build failed")
        topology = cpu_topology(cpu)
        record = {
            "schema": "hex-rcf-phase-profile-v1", "state": "running",
            "scope": "one fresh ordinary-kernel proof; exclusive Lean profiler categories",
            "environment": initial, "cpu": cpu, "topology": topology,
            "source_hashes": before, "module": PROBE.module,
        }
        write(args.output / "audit.json", record)

        def retain(module, sample):
            record["sample"] = sample
            record["state"] = sample.get("state", "sample-retained")
            (args.output / "compiler.log").write_text(sample.get("compiler_output", ""))
            write(args.output / "audit.json", record)

        sample = build_sample(PROBE.module, args.timeout, cpu,
                              parse_cpu_list(topology["thread_siblings_list"]),
                              retain, True, PROBE.axiom_namespace)
        validate_axioms("attribution", "sample", PROBE, sample)
        after = source_hashes(SOURCES, Path(__file__))
        record["source_hashes_after"] = after
        record["environment_after"] = environment()
        record["artifacts"] = artifact_sizes(PROBE.module, Path("bench"))
        record["state"] = "complete" if before == after else "source-changed"
        write(args.output / "audit.json", record)
        if before != after:
            raise RuntimeError("source changed while profiling; sample retained")
        print(args.output)
    finally:
        lease.close()


if __name__ == "__main__":
    main()
