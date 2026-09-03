#!/usr/bin/env python3
"""Monitor a pinned command and grade interference in LeanBench timed regions."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import time
from typing import Iterable


def sibling_set(cpu: int) -> set[int]:
    path = Path(
        f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list"
    )
    siblings: set[int] = set()
    for part in path.read_text().strip().split(","):
        if "-" in part:
            lo, hi = map(int, part.split("-", 1))
            siblings.update(range(lo, hi + 1))
        else:
            siblings.add(int(part))
    return siblings or {cpu}


def cpu_counters() -> dict[int, tuple[int, int]]:
    counters: dict[int, tuple[int, int]] = {}
    for line in Path("/proc/stat").read_text().splitlines():
        if not line.startswith("cpu") or line.startswith("cpu "):
            continue
        name, *fields_text = line.split()
        fields = [int(value) for value in fields_text]
        cpu = int(name[3:])
        total = sum(fields)
        idle = fields[3] + (fields[4] if len(fields) > 4 else 0)
        counters[cpu] = (total - idle, total)
    return counters


def busy_percent(
    before: tuple[int, int], after: tuple[int, int]
) -> float:
    busy_before, total_before = before
    busy_after, total_after = after
    elapsed = total_after - total_before
    if elapsed <= 0:
        return 0.0
    return 100.0 * (busy_after - busy_before) / elapsed


def busy_seconds(
    before: tuple[int, int], after: tuple[int, int], tick_hz: int
) -> float:
    return (after[0] - before[0]) / tick_hz


def process_snapshot() -> dict[int, tuple[int, str, int, str]]:
    result: dict[int, tuple[int, str, int, str]] = {}
    for stat_path in Path("/proc").glob("[0-9]*/stat"):
        try:
            text = stat_path.read_text()
            close = text.rfind(")")
            pid = int(text[: text.find(" ")])
            comm = text[text.find("(") + 1 : close]
            fields = text[close + 2 :].split()
            # After the closing parenthesis: state, ppid, ..., processor.
            result[pid] = (int(fields[1]), fields[0], int(fields[36]), comm)
        except (FileNotFoundError, IndexError, PermissionError, ValueError):
            continue
    return result


def descendants(
    root: int, snapshot: dict[int, tuple[int, str, int, str]]
) -> set[int]:
    found = {root}
    changed = True
    while changed:
        changed = False
        for pid, (ppid, _state, _cpu, _comm) in snapshot.items():
            if ppid in found and pid not in found:
                found.add(pid)
                changed = True
    return found


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def merge_regions(regions: Iterable[tuple[int, int]]) -> list[tuple[int, int]]:
    """Return the union of monotonic-clock intervals."""
    merged: list[tuple[int, int]] = []
    for start, end in sorted(regions):
        if end < start:
            raise ValueError(f"timed region ends before it starts: {start}..{end}")
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return merged


def overlap_ns(
    start: int, end: int, regions: Iterable[tuple[int, int]]
) -> int:
    """Measure how much of [start, end] lies in the region union."""
    return sum(
        max(0, min(end, region_end) - max(start, region_start))
        for region_start, region_end in regions
    )


def load_timed_regions(paths: Iterable[Path]) -> tuple[list[tuple[int, int]], int]:
    """Load and union all LeanBench timed-loop sidecar regions."""
    regions: list[tuple[int, int]] = []
    path_count = 0
    for path in paths:
        path_count += 1
        saw_header = False
        for line in path.read_text().splitlines():
            record = json.loads(line)
            if record.get("kind") == "header":
                saw_header = True
            elif record.get("kind") == "region":
                regions.append(
                    (int(record["mono_t0_ns"]), int(record["mono_t1_ns"]))
                )
        if not saw_header:
            raise ValueError(f"timed-region sidecar has no header: {path}")
    return merge_regions(regions), path_count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--interval", type=float, default=0.25)
    parser.add_argument("--max-core-interference-ratio", type=float, default=0.002)
    parser.add_argument("--fail-on-contamination", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        parser.error("a command is required after --")
    if args.interval <= 0:
        parser.error("--interval must be positive")

    siblings = sibling_set(args.cpu)
    monitored = sorted(siblings | {args.cpu})
    monitor_affinity = os.sched_getaffinity(0) - set(monitored)
    if monitor_affinity:
        os.sched_setaffinity(0, monitor_affinity)

    started = utc_now()
    started_mono_ns = time.monotonic_ns()
    previous = cpu_counters()
    previous_mono_ns = started_mono_ns
    tick_hz = os.sysconf("SC_CLK_TCK")
    samples: list[dict[str, object]] = []

    def pin_child() -> None:
        os.sched_setaffinity(0, {args.cpu})

    sidecar_stem = f"{args.output}.timed-{os.getpid()}-{started_mono_ns}"
    sidecar_template = f"{sidecar_stem}-%p.jsonl"
    child_env = os.environ.copy()
    child_env["LEAN_BENCH_TIMED_REGIONS_SIDECAR"] = sidecar_template
    process = subprocess.Popen(command, preexec_fn=pin_child, env=child_env)
    while process.poll() is None:
        time.sleep(args.interval)
        current = cpu_counters()
        current_mono_ns = time.monotonic_ns()
        snapshot = process_snapshot()
        owned = descendants(process.pid, snapshot)
        foreign = [
            {"pid": pid, "cpu": cpu, "comm": comm}
            for pid, (_ppid, state, cpu, comm) in snapshot.items()
            if state == "R" and cpu in monitored and pid not in owned
        ]
        samples.append(
            {
                "mono_t0_ns": previous_mono_ns,
                "mono_t1_ns": current_mono_ns,
                "elapsed_seconds": round(
                    (current_mono_ns - started_mono_ns) / 1_000_000_000, 3
                ),
                "busy_percent": {
                    str(cpu): round(
                        busy_percent(previous[cpu], current[cpu]), 3
                    )
                    for cpu in monitored
                },
                "busy_seconds": {
                    str(cpu): round(
                        busy_seconds(previous[cpu], current[cpu], tick_hz), 6
                    )
                    for cpu in monitored
                },
                "interval_wall_seconds": round(
                    (current_mono_ns - previous_mono_ns) / 1_000_000_000, 6
                ),
                "foreign_runnable": foreign,
                "load_average": [round(value, 3) for value in os.getloadavg()],
            }
        )
        previous = current
        previous_mono_ns = current_mono_ns

    return_code = process.wait()
    sidecar_paths = sorted(
        args.output.parent.glob(Path(sidecar_stem).name + "-*.jsonl")
    )
    timed_regions, sidecar_count = load_timed_regions(sidecar_paths)
    for sample in samples:
        sample_start = int(sample["mono_t0_ns"])
        sample_end = int(sample["mono_t1_ns"])
        duration_ns = sample_end - sample_start
        timed_ns = overlap_ns(sample_start, sample_end, timed_regions)
        sample["timed_overlap_seconds"] = round(timed_ns / 1_000_000_000, 6)
        sample["timed_fraction"] = round(
            timed_ns / duration_ns if duration_ns > 0 else 0.0, 6
        )

    sibling_cpus = sorted(set(monitored) - {args.cpu})
    sibling_busy_seconds = sum(
        float(sample["busy_seconds"][str(cpu)]) * float(sample["timed_fraction"])
        for sample in samples
        for cpu in sibling_cpus
    )
    foreign_measurement_seconds = sum(
        float(sample["timed_overlap_seconds"])
        for sample in samples
        if any(
            int(process["cpu"]) == args.cpu
            for process in sample["foreign_runnable"]
        )
    )
    elapsed = (time.monotonic_ns() - started_mono_ns) / 1_000_000_000
    timed_wall_seconds = sum(
        float(sample["timed_overlap_seconds"]) for sample in samples
    )
    aggregate_interference_seconds = (
        sibling_busy_seconds + foreign_measurement_seconds
    )
    aggregate_interference_ratio: float | None = (
        aggregate_interference_seconds / timed_wall_seconds
        if timed_wall_seconds > 0
        else None
    )
    foreign_samples = sum(
        bool(sample["foreign_runnable"])
        and float(sample["timed_overlap_seconds"]) > 0
        for sample in samples
    )
    timed_regions_complete = sidecar_count > 0 and bool(timed_regions)
    contaminated = (
        not timed_regions_complete
        or aggregate_interference_ratio is None
        or aggregate_interference_ratio > args.max_core_interference_ratio
    )
    document = {
        "schema": 1,
        "command": command,
        "cpu": args.cpu,
        "smt_siblings": sibling_cpus,
        "interval_seconds": args.interval,
        "started_utc": started,
        "ended_utc": utc_now(),
        "elapsed_seconds": round(elapsed, 3),
        "timed_region_sidecars": [str(path) for path in sidecar_paths],
        "command_return_code": return_code,
        "thresholds": {
            "max_core_interference_ratio": args.max_core_interference_ratio,
        },
        "summary": {
            "sample_count": len(samples),
            "timed_region_sidecar_count": sidecar_count,
            "timed_region_count_after_union": len(timed_regions),
            "timed_regions_complete": timed_regions_complete,
            "timed_wall_seconds": round(timed_wall_seconds, 6),
            "foreign_runnable_samples": foreign_samples,
            "measurement_cpu_foreign_seconds_estimate": round(
                foreign_measurement_seconds, 6
            ),
            "smt_sibling_busy_seconds": round(sibling_busy_seconds, 6),
            "aggregate_core_interference_seconds": round(
                aggregate_interference_seconds, 6
            ),
            "aggregate_core_interference_ratio": (
                round(aggregate_interference_ratio, 6)
                if aggregate_interference_ratio is not None
                else None
            ),
            "contaminated": contaminated,
        },
        "samples": samples,
    }
    args.output.write_text(json.dumps(document, indent=2) + "\n")
    if return_code != 0:
        return return_code
    if contaminated and args.fail_on_contamination:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
