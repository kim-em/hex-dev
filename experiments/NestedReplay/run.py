#!/usr/bin/env python3
"""Check the native prototype and retain adjacent, alternating replay timings."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "bench"))
from cpu_lease import cpu_lease

ARM = re.compile(r"arm=(cached|ordinary|plain) repetitions=(\d+) nanos=(\d+)")
COUNTS = re.compile(
    r"level=(\d+) facts=(\d+) used=(\d+) \{ calls := (\d+), signs := (\d+), "
    r"nonconstantSigns := (\d+), hits := (\d+), inverses := (\d+) \}"
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_arms(output: str) -> list[dict]:
    arms = []
    for line in output.splitlines():
        if match := ARM.fullmatch(line):
            arms.append(dict(arm=match[1], repetitions=int(match[2]), nanos=int(match[3]), levels=[]))
        elif arms and (match := COUNTS.fullmatch(line)):
            names = ["level", "facts", "used", "calls", "signs", "nonconstantSigns", "hits", "inverses"]
            arms[-1]["levels"].append(dict(zip(names, map(int, match.groups()))))
    assert len(arms) == 3, "expected all three timed arms"
    for arm in arms:
        assert [c["level"] for c in arm["levels"]] == [1, 2]
        assert arm["repetitions"] == 200 and arm["nanos"] > 0
        for c in arm["levels"]:
            if arm["arm"] == "plain":
                assert c["calls"] == c["signs"] == c["hits"] == c["inverses"] == 0
                continue
            assert c["calls"] >= arm["repetitions"], "native checker was shared/eliminated"
            if arm["arm"] == "cached":
                assert c["signs"] == c["nonconstantSigns"] == 0
                assert c["hits"] == c["calls"]
            else:
                assert c["signs"] == c["calls"] and c["nonconstantSigns"] > 0
                assert c["hits"] == 0
    return arms


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--pairs", type=int, default=1)
    args = parser.parse_args()
    if args.pairs < 1:
        parser.error("--pairs must be positive")
    args.output.mkdir(parents=True, exist_ok=False)
    binary = ROOT / "experiments/NestedReplay/.lake/build/bin/nestedReplay"
    cpu, lease = cpu_lease()
    # Holding this descriptor leases the same CPU for every adjacent pair.
    with lease:
        metadata = dict(
            revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            treeDirty=bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
            cpu=cpu, platform=platform.platform(), affinity=sorted(os.sched_getaffinity(0)),
            initialLoadAverage=os.getloadavg(), binarySha256=digest(binary),
            mainSha256=digest(ROOT / "experiments/NestedReplay/Main.lean"),
            toolchain=(ROOT / "lean-toolchain").read_text().strip(),
            repetitionsPerArm=200, pairs=args.pairs, unchangedReruns=0,
            buildCommand="lake -d experiments/NestedReplay build",
        )
        (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")

        def run(name: str, flags: list[str]) -> subprocess.CompletedProcess:
            command = ["taskset", "-c", str(cpu), str(binary), *flags]
            result = subprocess.run(command, capture_output=True, text=True, cwd=ROOT,
                                    env={**os.environ, "LEAN_ABORT_ON_PANIC": "1"})
            (args.output / f"{name}.stdout").write_text(result.stdout)
            (args.output / f"{name}.stderr").write_text(result.stderr)
            (args.output / f"{name}.json").write_text(json.dumps(dict(command=command, exit=result.returncode)) + "\n")
            return result

        keys = run("exact-keys", ["--keys-only"])
        assert keys.returncode == 0
        assert "noncanonicalAliasRejected=true conjugateLiteralRejected=true" in keys.stdout
        omitted = run("omitted", ["--omit"])
        assert omitted.returncode == 17, "missing actually-used fact did not reject"
        assert "MISSING level=2; no replacement sign evaluation" in omitted.stderr
        assert "signs := 0, nonconstantSigns := 0" in omitted.stderr
        assert "removed one actually used nonconstant" in omitted.stdout
        lower_omitted = run("omitted-level-one", ["--omit-level-one"])
        assert lower_omitted.returncode == 17
        assert "MISSING level=1; no replacement sign evaluation" in lower_omitted.stderr
        assert "signs := 0, nonconstantSigns := 0" in lower_omitted.stderr
        literal_omitted = run("omitted-literal", ["--omit-literal"])
        assert literal_omitted.returncode == 17
        assert "LITERAL_REJECTED level=2" in literal_omitted.stderr
        collection = run("collection-pass", ["--collect-replay"])
        assert collection.returncode == 0
        parse_arms(collection.stdout)
        collection_counts = [tuple(map(int, match.groups()))
                             for line in collection.stdout.splitlines()
                             if (match := COUNTS.fullmatch(line))]
        assert [c[1] for c in collection_counts[:2]] == [c[1] for c in collection_counts[2:4]], \
            "collection replay discovered additional keys"
        samples = []
        for pair in range(args.pairs):
            order = ["cached", "ordinary", "plain"] if pair % 2 == 0 else ["plain", "ordinary", "cached"]
            started = time.monotonic_ns()
            result = run(f"pair-{pair}", [] if pair % 2 == 0 else ["--ordinary-first"])
            duration = time.monotonic_ns() - started
            assert result.returncode == 0, result.stderr
            assert "graphNodes=2 selectedSigns=[1, 1]" in result.stdout
            arms = parse_arms(result.stdout)
            assert [arm["arm"] for arm in arms] == order
            sample = dict(pair=pair, order=order, arms=arms, processNanos=duration,
                          endLoadAverage=os.getloadavg())
            samples.append(sample)
            with (args.output / "samples.jsonl").open("a") as stream:
                stream.write(json.dumps(sample) + "\n")
        ratios = [next(a["nanos"] for a in s["arms"] if a["arm"] == "ordinary") /
                  next(a["nanos"] for a in s["arms"] if a["arm"] == "cached") for s in samples]
        summary = dict(
            producerOnlyAccepted=True, omissionExits={"arithmeticLevel2": omitted.returncode,
                "arithmeticLevel1": lower_omitted.returncode, "literalLevel2": literal_omitted.returncode},
            pairRatiosOrdinaryOverCached=ratios, pairedMedian=statistics.median(ratios),
            medianNanosPerReplay={arm: statistics.median(
                a["nanos"] / a["repetitions"] for s in samples for a in s["arms"] if a["arm"] == arm
            ) for arm in ["cached", "ordinary", "plain"]},
        )
        (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
