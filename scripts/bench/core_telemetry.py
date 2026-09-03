#!/usr/bin/env python3
"""Run a command on one CPU while monitoring it and its SMT siblings."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import time


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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--interval", type=float, default=0.25)
    parser.add_argument("--max-sibling-busy-percent", type=float, default=5.0)
    parser.add_argument("--max-foreign-runnable-samples", type=int, default=0)
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
    started_mono = time.monotonic()
    previous = cpu_counters()
    samples: list[dict[str, object]] = []

    def pin_child() -> None:
        os.sched_setaffinity(0, {args.cpu})

    process = subprocess.Popen(command, preexec_fn=pin_child)
    while process.poll() is None:
        time.sleep(args.interval)
        current = cpu_counters()
        snapshot = process_snapshot()
        owned = descendants(process.pid, snapshot)
        foreign = [
            {"pid": pid, "cpu": cpu, "comm": comm}
            for pid, (_ppid, state, cpu, comm) in snapshot.items()
            if state == "R" and cpu in monitored and pid not in owned
        ]
        samples.append(
            {
                "elapsed_seconds": round(time.monotonic() - started_mono, 3),
                "busy_percent": {
                    str(cpu): round(
                        busy_percent(previous[cpu], current[cpu]), 3
                    )
                    for cpu in monitored
                },
                "foreign_runnable": foreign,
                "load_average": [round(value, 3) for value in os.getloadavg()],
            }
        )
        previous = current

    return_code = process.wait()
    sibling_cpus = sorted(set(monitored) - {args.cpu})
    sibling_busy = [
        float(sample["busy_percent"][str(cpu)])
        for sample in samples
        for cpu in sibling_cpus
    ]
    foreign_samples = sum(bool(sample["foreign_runnable"]) for sample in samples)
    mean_sibling_busy = (
        sum(sibling_busy) / len(sibling_busy) if sibling_busy else 0.0
    )
    contaminated = (
        mean_sibling_busy > args.max_sibling_busy_percent
        or foreign_samples > args.max_foreign_runnable_samples
    )
    document = {
        "schema": 1,
        "command": command,
        "cpu": args.cpu,
        "smt_siblings": sibling_cpus,
        "interval_seconds": args.interval,
        "started_utc": started,
        "ended_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started_mono, 3),
        "command_return_code": return_code,
        "thresholds": {
            "max_sibling_busy_percent": args.max_sibling_busy_percent,
            "max_foreign_runnable_samples": args.max_foreign_runnable_samples,
        },
        "summary": {
            "sample_count": len(samples),
            "mean_sibling_busy_percent": round(mean_sibling_busy, 3),
            "foreign_runnable_samples": foreign_samples,
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
