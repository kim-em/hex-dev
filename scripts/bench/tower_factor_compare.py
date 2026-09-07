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


BUSY_PERCENT = 5.0
PREFLIGHT_SECONDS = 900
MIN_CORE = 24
MAX_ATTEMPTS = 12
HEX_NAMES = NAMES[:8]


def select_core(busy, topology, avoid):
    """An absent/offline CPU makes its entire physical core unavailable."""
    free = sorted((max(busy.get(i, 100.0) for i in group), cpu)
                  for cpu, group in topology.items() if cpu not in avoid)
    return next((cpu for load, cpu in free if load < BUSY_PERCENT), None)


def read_export(path, names):
    """Validate complete fixed-case exports, including their raw repeat hashes."""
    rows = json.loads(Path(path).read_text())["results"]
    if len(rows) != len(names) or {r["function"] for r in rows} != set(names):
        raise ValueError("missing, duplicate, or unexpected benchmark names")
    result = {}
    for row in rows:
        if row["kind"] != "fixed" or row["budget_truncated"] or not row["hashes_agree"]:
            raise ValueError("incomplete fixed benchmark or disagreeing hashes")
        points = row["points"]
        if len(points) != 5 or {p["repeat_index"] for p in points} != set(range(5)):
            raise ValueError("missing or duplicate repeats")
        if any(p["status"] != "ok" or p["inner_repeats"] <= 0 or p["total_nanos"] <= 0
               or p["result_hash"] != row["observed_hash"] for p in points):
            raise ValueError("failed repeat, invalid batch, or inconsistent hash")
        times = sorted(p["total_nanos"] // p["inner_repeats"] for p in points)
        if [row["min_nanos"], row["median_nanos"], row["max_nanos"]] != [times[0], times[2], times[4]]:
            raise ValueError("summary does not match raw repeat timings")
        if row["median_nanos"] <= 0 or row["expected_hash_check"]["status"] not in ("match", "unset"):
            raise ValueError("invalid median or failed expected hash")
        if row["config"]["repeats"] != 5 or row["config"]["min_total_seconds"] != 0.2:
            raise ValueError("unexpected measurement configuration")
        config = row["config"]
        budget = 2 if row["function"] in HEX_NAMES[-2:] else 60
        if not config["warmup"] or not config["warmup_first_iter"] or config["max_seconds_per_call"] != budget:
            raise ValueError("unexpected warmup or fixed-case budget")
        result[row["function"]] = row
    for degree in (2, 3, 4, 6, 8, 12):
        pari_name = PREFIX + "runPariNfFactor" + str(degree)
        if pari_name in result and result[pari_name]["observed_hash"] != result[PREFIX + "runTowerFactorPair" + str(degree)]["observed_hash"]:
            raise ValueError("PARI/Hex degree-multiplicity mismatch")
    return result


def decision(pairs, names, *, require_separated_canonical=False):
    """Apply the registered retention rule; incomplete series have no verdict."""
    if len(pairs) > 2 or len({p["attempt"] for p in pairs}) != len(pairs):
        raise ValueError("expected at most two distinct accepted pairs")
    identities = {}
    orders = []
    for pair in pairs:
        runs = pair["runs"]
        if not pair["accepted"] or len(runs) != 2 or not all(r["accepted"] for r in runs):
            raise ValueError("rejected or incomplete host pair")
        order = tuple(r["arm"] for r in runs)
        if set(order) != {"left", "right"}:
            raise ValueError("missing or duplicate arm")
        orders.append(order)
        for run in runs:
            identity = (run["source_commit"], run["binary_sha256"])
            if identities.setdefault(run["arm"], identity) != identity:
                raise ValueError("binary or source changed between pairs")
    if len(pairs) == 2 and set(orders) != {("left", "right"), ("right", "left")}:
        raise ValueError("accepted pairs must use opposite arm orders")
    checks = []
    for pair in pairs:
        arms = {r["arm"]: read_export(r["export"], names) for r in pair["runs"]}
        for name in HEX_NAMES:
            left, right = arms["left"][name], arms["right"][name]
            checks.append(dict(pair=pair["attempt"], function=name,
                               hashes_match=left["observed_hash"] == right["observed_hash"],
                               faster=right["median_nanos"] < left["median_nanos"],
                               disjoint_regression=right["min_nanos"] > left["max_nanos"],
                               left_nanos=[left[k] for k in ("min_nanos", "median_nanos", "max_nanos")],
                               right_nanos=[right[k] for k in ("min_nanos", "median_nanos", "max_nanos")],
                               speedup=left["median_nanos"] / right["median_nanos"]))
    eligible = None
    if len(pairs) == 2:
        canonical = {PREFIX + "runTowerFactorLadder", PREFIX + "runTowerCheckFactorization"}
        eligible = all(c["hashes_match"] and not c["disjoint_regression"] for c in checks)
        eligible = eligible and all(c["faster"] for c in checks if c["function"] in canonical)
        if require_separated_canonical:
            eligible = eligible and all(any(
                c["right_nanos"][2] < c["left_nanos"][0]
                for c in checks if c["function"] == name) for name in canonical)
    return dict(complete=len(pairs) == 2, eligible=eligible, checks=checks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("label")
    parser.add_argument("left")
    parser.add_argument("right")
    parser.add_argument("left_commit")
    parser.add_argument("right_commit")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pari-python", default=os.environ.get("HEX_PARI_BENCH_PYTHON"))
    parser.add_argument("--hex-only", action="store_true")
    parser.add_argument("--require-separated-canonical", action="store_true",
                        help="require disjoint improvement for each canonical case in at least one pair")
    args = parser.parse_args()
    names = HEX_NAMES if args.hex_only else NAMES
    env = dict(os.environ)
    provider = None
    if not args.hex_only:
        if not args.pari_python:
            parser.error("set --pari-python or HEX_PARI_BENCH_PYTHON to the registered provider")
        provider_path = str(Path(args.pari_python).expanduser().absolute())
        if not os.path.isfile(provider_path) or not os.access(provider_path, os.X_OK):
            parser.error("PARI Python is not an executable file")
        env["HEX_PARI_BENCH_PYTHON"] = provider_path
        provider = json.loads(subprocess.check_output([provider_path, "-c",
            "import json,platform,importlib.metadata; from cypari2 import Pari; "
            "print(json.dumps(dict(python=platform.python_version(),pari=str(Pari().version()),cypari2=importlib.metadata.version('cypari2'))))"], text=True))
        provider["path"] = provider_path
    args.left = str(Path(args.left).resolve())
    args.right = str(Path(args.right).resolve())
    for binary in (args.left, args.right):
        if not os.path.isfile(binary) or not os.access(binary, os.X_OK):
            parser.error("both saved benchmark binaries must be executable files")
    if platform.node() != "chungus2":
        parser.error("this protocol is registered for chungus2")
    args.output.mkdir(parents=True, exist_ok=True)
    if list(args.output.glob(f"issue-10074-{args.label}-*-host.json")):
        parser.error("this series label already has artifacts; use a fresh label")
    topology = idle_core.sibling_map()
    avoid = {cpu for cpu, group in topology.items() if min(group) < MIN_CORE}
    accepted = 0
    pairs = []
    script_hash = digest(__file__)
    def summarize(status, attempts):
        summary = dict(label=args.label, status=status, attempts=attempts,
                       accepted_pairs=[p["attempt"] for p in pairs],
                       require_separated_canonical=args.require_separated_canonical,
                       **decision(pairs, names, require_separated_canonical=args.require_separated_canonical))
        (args.output / f"issue-10074-{args.label}-decision.json").write_text(json.dumps(summary, indent=2) + "\n")
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    for attempt in range(1, MAX_ATTEMPTS + 1):
        stem = args.output / f"issue-10074-{args.label}-{attempt}"
        meta = dict(label=args.label, attempt=attempt, runs=[], preflight_windows=[],
                    protocol_commit=commit, script_sha256=script_hash,
                    require_separated_canonical=args.require_separated_canonical,
                    hostname=platform.node(), release_quality=False,
                    pari_provider=provider, names=names,
                    git_status=subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
        deadline = time.monotonic() + PREFLIGHT_SECONDS
        cpu = None
        while time.monotonic() < deadline:
            busy = idle_core.busy_by_cpu(2)
            cpu = select_core(busy, topology, avoid)
            meta["preflight_windows"].append(busy)
            if cpu is not None:
                break
            time.sleep(10)
        if cpu is None:
            meta.update(accepted=False, reason="preflight_timeout")
            Path(str(stem) + "-host.json").write_text(json.dumps(meta, indent=2) + "\n")
            summarize("preflight_timeout", attempt)
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
            pre = {i: busy.get(i, 100.0) for i in siblings}
            if max(pre.values()) >= BUSY_PERCENT:
                meta["rejected_preflight"] = dict(arm=arm, busy=pre)
                break
            export = str(stem) + f"-{arm}.json"
            command = ["taskset", "-c", str(cpu), binary, "run", *names,
                       "--repeats", "5", "--min-total-seconds", "0.2", "--export-file", export]
            samples = []
            with open(str(stem) + f"-{arm}.log", "w") as output:
                child = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, env=env)
                while child.poll() is None:
                    sample = idle_core.busy_by_cpu(2)
                    samples.append({i: sample.get(i, 100.0) for i in siblings})
            post_sample = idle_core.busy_by_cpu(2)
            post = {i: post_sample.get(i, 100.0) for i in siblings}
            means = {i: sum(s[i] for s in samples) / len(samples)
                     for i in siblings if i != cpu} if samples else {}
            ok = child.returncode == 0 and bool(samples) and max(post.values()) < BUSY_PERCENT and max(means.values(), default=0) < BUSY_PERCENT
            export_error = None
            try:
                read_export(export, names)
            except (OSError, ValueError, KeyError, TypeError) as error:
                export_error = str(error)
                ok = False
            meta["runs"].append(dict(arm=arm, source_commit=source, binary_sha256=digest(binary),
                                     command=command, export=export, preflight=pre, postflight=post,
                                     during=samples, sibling_mean=means, exit_code=child.returncode, accepted=ok, export_error=export_error))
            print(args.label, attempt, arm, ok, "post", post, "sibling", means, flush=True)
            if not ok:
                break
        meta["accepted"] = len(meta["runs"]) == 2 and all(r["accepted"] for r in meta["runs"])
        if meta["accepted"]:
            arms = {r["arm"]: read_export(r["export"], names) for r in meta["runs"]}
            if any(arms["left"][n]["observed_hash"] != arms["right"][n]["observed_hash"] for n in names):
                meta.update(accepted=False, reason="cross_arm_hash_mismatch")
        Path(str(stem) + "-host.json").write_text(json.dumps(meta, indent=2) + "\n")
        if meta["accepted"]:
            pairs.append(meta)
            accepted += 1
        summarize("complete" if accepted == 2 else "running", attempt)
        if any(r.get("export_error") for r in meta["runs"]):
            summarize("invalid_export", attempt)
            return 1
        if meta.get("reason") == "cross_arm_hash_mismatch":
            summarize("cross_arm_hash_mismatch", attempt)
            return 1
        print("accepted pairs", accepted, flush=True)
        if accepted == 2:
            return 0
    summarize("attempt_limit", MAX_ATTEMPTS)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
