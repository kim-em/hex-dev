#!/usr/bin/env python3
"""Retain the unchanged sign ladder and adjacent before/after LeanBench samples.

Build and freeze both binaries and their source manifests before running. The
ordinary after ladder uses the registration unchanged. The paired samples use
LeanBench's child runner with the same parameters and tuning target; they are
speed comparisons, not independent complexity verdicts. No sample filtering,
quiet-host preflight, automatic rerun, or custom timing kernel is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
BENCH = "Hex.SturmBench.runSigns"
PARAMETERS = (128, 256, 512, 1024)
TRIALS = 4
TARGET_NANOS = 100_000_000


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arm in ("before", "after"):
        parser.add_argument("--" + arm, type=Path, required=True)
        parser.add_argument("--" + arm + "-source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out == ROOT or ROOT in out.parents:
        parser.error("collect outside the frozen checkout, then archive the completed capture")
    out.mkdir(parents=True, exist_ok=False)
    binaries = {arm: getattr(args, arm).resolve() for arm in ("before", "after")}
    sources = {}
    for arm in binaries:
        path = getattr(args, arm + "_source").resolve()
        sources[arm] = json.loads(path.read_text())
        if digest(binaries[arm]) != sources[arm]["binary_sha256"]:
            raise RuntimeError("frozen binary does not match its source manifest")
        (out / (arm + "-source.json")).write_bytes(path.read_bytes())
    for path, expected in sources["after"]["sources"].items():
        if digest(ROOT / path) != expected:
            raise RuntimeError("after source changed: " + path)

    cpu, lease = cpu_lease()
    affinity = sorted(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    record = dict(status="running", benchmark=BENCH, parameters=PARAMETERS,
                  trials=TRIALS, target_nanos=TARGET_NANOS, cpu=cpu,
                  original_affinity=affinity, host=platform.node(),
                  platform=platform.platform(), load_start=os.getloadavg(),
                  protocol="ordinary registered after ladder; paired trial-major alternating AB/BA",
                  arms={arm: dict(binary=str(binary), binary_sha256=digest(binary),
                                  source_manifest=arm + "-source.json")
                        for arm, binary in binaries.items()}, commands=[], samples=[], reruns=0,
                  capture_script_sha256=digest(Path(__file__)))

    def save():
        (out / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(argv, name):
        command = dict(argv=list(map(str, argv)), stdout=name + ".stdout",
                       stderr=name + ".stderr", status="running", load_start=os.getloadavg())
        record["commands"].append(command)
        save()
        with (out / command["stdout"]).open("w") as stdout, (out / command["stderr"]).open("w") as stderr:
            result = subprocess.run(command["argv"], cwd=ROOT, stdout=stdout, stderr=stderr,
                                    env={**os.environ, "LEAN_ABORT_ON_PANIC": "1"})
        command.update(status="completed", exit_code=result.returncode, load_end=os.getloadavg())
        save()
        if result.returncode:
            raise RuntimeError("command failed; retained: " + name)
        return (out / command["stdout"]).read_text()

    try:
        save()
        for arm, binary in binaries.items():
            run([binary, "verify", BENCH], arm + "-verify")
        run([binaries["after"], "run", BENCH, "--export-file", out / "after-ladder.json"],
            "after-ladder")
        ladder = json.loads((out / "after-ladder.json").read_text())["results"][0]
        if ladder["budget_truncated"] or len(ladder["points"]) != TRIALS * len(PARAMETERS):
            raise RuntimeError("registered ladder incomplete; retain its results")
        if any(p["status"] != "ok" or p["result_hash"] is None for p in ladder["points"]):
            raise RuntimeError("registered ladder has failed measurements")
        expected_hashes = {p["param"]: p["result_hash"] for p in ladder["points"]}
        with (out / "paired.jsonl").open("w") as stream:
            for trial in range(TRIALS):
                for n in PARAMETERS:
                    for position, arm in enumerate(("before", "after") if trial % 2 == 0 else ("after", "before")):
                        name = f"pair-{trial}-{n}-{arm}"
                        text = run([binaries[arm], "_child", "--bench", BENCH, "--param", n,
                                    "--target-nanos", TARGET_NANOS, "--cache-mode", "warm"], name)
                        rows = [json.loads(line) for line in text.splitlines() if line.startswith("{")]
                        if len(rows) != 1:
                            raise RuntimeError("expected one LeanBench child row: " + name)
                        row = dict(trial=trial, param=n, arm=arm, position=position, measurement=rows[0])
                        stream.write(json.dumps(row) + "\n")
                        stream.flush()
                        record["samples"].append(row)
                        save()
                        measured = rows[0]
                        if (measured["status"] != "ok" or measured["param"] != n or
                                measured["function"] != BENCH or measured["inner_repeats"] < 1 or
                                measured.get("profile_kernel", False)):
                            raise RuntimeError("invalid scientific child row; retained: " + name)
                        if measured["result_hash"] != expected_hashes[n]:
                            raise RuntimeError("before/after result hashes disagree")
        summary = []
        for n in PARAMETERS:
            times = {arm: {s["trial"]: s["measurement"]["per_call_nanos"]
                           for s in record["samples"] if s["param"] == n and s["arm"] == arm}
                     for arm in binaries}
            summary.append(dict(param=n, median_nanos={arm: statistics.median(times[arm].values())
                                                       for arm in binaries},
                                paired_speedups=[times["before"][t] / times["after"][t]
                                                 for t in range(TRIALS)]))
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        record["status"] = "completed"
        print(json.dumps(summary), flush=True)
    except BaseException as error:
        record.update(status="incomplete", error=str(error))
        raise
    finally:
        record["load_end"] = os.getloadavg()
        save()
        lease.close()


if __name__ == "__main__":
    main()
