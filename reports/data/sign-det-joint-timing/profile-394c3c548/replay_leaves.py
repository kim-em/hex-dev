"""Reconstruct direct sampled leaves into a fresh directory, preserving raw data."""
import argparse
import collections
import json
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("raw", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
args.output.mkdir(exist_ok=False)
sidecars = [json.loads(line) for p in args.raw.glob("regions-*.jsonl")
            for line in p.read_text().splitlines()]
pid = next(row["pid"] for row in sidecars if row["kind"] == "header")
regions = [(row["mono_t0_ns"], row["mono_t1_ns"]) for row in sidecars
           if row["kind"] == "region" and row["label"] == "kernel"]
counts = collections.Counter()
outside = foreign = 0
for line in (args.raw / "perf-ip-pids.txt").read_text().splitlines():
    match = re.fullmatch(r"(\d+)/(\d+)\s+(\d+)\.(\d+):\s+([0-9a-f]+)\s+(.*?)\s+\((.*)\)", line.strip())
    if not match:
        raise ValueError("unparsed event: " + line)
    process, thread, sec, frac, ip, symbol, dso = match.groups()
    ns = int(sec)*10**9 + int(frac.ljust(9, "0"))
    if not any(a <= ns <= b for a, b in regions):
        outside += 1
    elif int(process) != pid:
        foreign += 1
    else:
        counts[symbol] += 1
summary = {"operation_samples": sum(counts.values()),
           "outside_operation_samples": outside,
           "foreign_pid_samples_in_region": foreign,
           "leaf_counts": dict(counts.most_common())}
original = json.loads((args.raw / "ip-summary.json").read_text())
assert all(value == original[key] for key, value in summary.items())
(args.output / "leaf-reconstruction.json").write_text(json.dumps(summary, indent=2) + "\n")
print("Original direct-IP counts reconstructed without changing the raw directory")
