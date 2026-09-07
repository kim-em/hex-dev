#!/usr/bin/env python3
"""Run registered tower factorization comparisons through lean-bench.

This orchestrates saved executables and CPU telemetry; all benchmark timing,
warmup, batching, and result hashing remain in lean-bench. See the protocol in
reports/hex-number-field-tower-factor-protocol.md.
"""
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time

import idle_core

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "Hex.NumberTowerBench."
NAMES = [PREFIX + "runTowerFactorPair" + str(n) for n in (2, 3, 4, 6, 8, 12)]
NAMES += [PREFIX + "runTowerFactorLadder", PREFIX + "runTowerCheckFactorization"]
NAMES += [PREFIX + "runPariNfFactor" + str(n) for n in (2, 3, 4, 6, 8, 12)]
NAMES += [PREFIX + "runPariNfFactorOverhead"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("label")
    parser.add_argument("left")
    parser.add_argument("right")
    parser.add_argument("left_commit")
    parser.add_argument("right_commit")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if platform.node() != "chungus2":
        parser.error("this protocol is registered for chungus2")
    args.output.mkdir(parents=True, exist_ok=True)
    topology = idle_core.sibling_map()
    avoid = {cpu for cpu, group in topology.items() if min(group) < 24}
    accepted = 0
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    for attempt in range(1, 13):
        stem = args.output / f"issue-10074-{args.label}-{attempt}"
        meta = dict(label=args.label, attempt=attempt, runs=[], preflight_windows=[],
                    protocol_commit=commit, script_sha256=digest(__file__),
                    hostname=platform.node(), release_quality=False,
                    pari_python=os.environ.get("HEX_PARI_BENCH_PYTHON"))
        deadline = time.monotonic() + 900
        cpu = None
        while time.monotonic() < deadline:
            busy = idle_core.busy_by_cpu(2)
            candidates = [(max(busy[i] for i in group), c)
                          for c, group in topology.items() if c not in avoid]
            free = sorted((load, c) for load, c in candidates if load < 5)
            meta["preflight_windows"].append(busy)
            if free:
                cpu = free[0][1]
                break
            time.sleep(10)
        if cpu is None:
            meta.update(accepted=False, reason="preflight_timeout")
            Path(str(stem) + "-host.json").write_text(json.dumps(meta, indent=2) + "\n")
            return 1
        siblings = sorted(topology[cpu])
        avoid.update(siblings)
        meta.update(cpu=cpu, siblings=siblings)
        arms = [("left", args.left, args.left_commit), ("right", args.right, args.right_commit)]
        if accepted % 2:
            arms.reverse()
        for index, (arm, binary, source) in enumerate(arms):
            if index:
                busy = idle_core.busy_by_cpu(2)
            pre = {i: busy[i] for i in siblings}
            if max(pre.values()) >= 5:
                meta["rejected_preflight"] = dict(arm=arm, busy=pre)
                break
            export = str(stem) + f"-{arm}.json"
            command = ["taskset", "-c", str(cpu), binary, "run", *NAMES,
                       "--repeats", "5", "--min-total-seconds", "0.2", "--export-file", export]
            samples = []
            with open(str(stem) + f"-{arm}.log", "w") as output:
                child = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
                while child.poll() is None:
                    sample = idle_core.busy_by_cpu(2)
                    samples.append({i: sample[i] for i in siblings})
            post = {i: v for i, v in idle_core.busy_by_cpu(2).items() if i in siblings}
            means = {i: sum(s[i] for s in samples) / len(samples)
                     for i in siblings if i != cpu} if samples else {}
            ok = child.returncode == 0 and bool(samples) and max(post.values()) < 5 and max(means.values(), default=0) < 5
            meta["runs"].append(dict(arm=arm, source_commit=source, binary_sha256=digest(binary),
                                     command=command, export=export, preflight=pre, postflight=post,
                                     during=samples, sibling_mean=means, exit_code=child.returncode, accepted=ok))
            print(args.label, attempt, arm, ok, "post", post, "sibling", means, flush=True)
            if not ok:
                break
        meta["accepted"] = len(meta["runs"]) == 2 and all(r["accepted"] for r in meta["runs"])
        Path(str(stem) + "-host.json").write_text(json.dumps(meta, indent=2) + "\n")
        if meta["accepted"]:
            accepted += 1
        print("accepted pairs", accepted, flush=True)
        if accepted == 2:
            return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
