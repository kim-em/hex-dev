#!/usr/bin/env python3
"""Six-round absolute proof evidence for inverse and solve, with 60-second ceilings."""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep  # noqa: E402
from scripts.bench.structural_tactic_sweep import acquire_cpu, write_summary  # noqa: E402

MANIFEST = ROOT / "scripts/bench/row_reduce_tactic_probes.json"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def specification(normalization=False):
    manifest = ROOT / "scripts/bench/row_reduce_normalization_probes.json" if normalization else MANIFEST
    cases = json.loads(manifest.read_text())
    baseline = "NormalizationBaseline" if normalization else "Baseline"
    return sweep.SweepSpec(
        description=__doc__,
        pairs=tuple(sweep.ProbePair(
            case["module"], sweep.ProbeModule("HexRowReduceMathlib.ProofProbe." + baseline),
            sweep.ProbeModule(case["module"], AXIOMS), case) for case in cases),
        probe_target="HexStructuralTacticProofProbe", schema="hex-row-reduce-tactic-probes-v1",
        measurement="paired-fresh-module-olean-wall-absolute-v1",
        output_stem="hex-row-reduce-tactic-probes", required_samples=6,
        absolute_only=True, retain_compiler_output=True,
        extra_sources=tuple(map(Path, (
            "scripts/bench/row_reduce_tactic_probes.py", "scripts/bench/row_reduce_tactic_probes.json",
            "scripts/bench/row_reduce_normalization_probes.json",
            "scripts/bench/structural_tactic_probes.py", "scripts/bench/structural_tactic_sweep.py",
            "HexRowReduce/SPEC/hex-row-reduce.md", "HexRowReduceMathlib/SPEC/hex-row-reduce-mathlib.md",
            "SPEC/matrix-tactics.md", "SPEC/benchmarking.md"))))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--normalization", action="store_true", help="measure the informational entrywise proofs")
    args, forwarded = parser.parse_known_args(argv)
    directory = (args.directory or Path(tempfile.mkdtemp(prefix="hex-row-reduce-tactics-"))).resolve()
    if directory.is_relative_to(ROOT):
        parser.error("evidence must be written outside the measured checkout")
    directory.mkdir(parents=True, exist_ok=True)
    journal = directory / "samples.jsonl"
    if journal.exists():
        parser.error("choose a new evidence directory; completed samples are retained")
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    spec = specification(args.normalization)
    journal.write_text(json.dumps({"header": {
        "environment": sweep.environment(), "source_sha256": sweep.source_hashes(spec, Path(__file__)),
        "samples": 6, "fresh_module_budget_ms": 60000}}) + "\n")

    def observe(module, sample):
        with journal.open("a") as stream:
            stream.write(json.dumps({"module": module, "sample": sample}) + "\n")

    try:
        output = directory / "sweep.json"
        status = sweep.run_cli(spec, Path(__file__), [
            "--shared-host", "--cpu", str(cpu), "--output", str(output), *forwarded],
            sample_observer=observe)
        if not args.normalization:
            write_summary(output)
        return status
    except Exception as exc:
        (directory / "failure.json").write_text(json.dumps({
            "error": str(exc), "exception": type(exc).__name__, "release_quality": False}, indent=2) + "\n")
        print(f"Incomplete sweep; retained evidence at {directory}: {exc}", file=sys.stderr)
        return 2
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
