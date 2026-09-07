#!/usr/bin/env python3
"""Monitor a pinned command and grade interference in LeanBench timed regions.

The monitor and command form a cancellation group in a dedicated session.
Standalone callers that are already process-group leaders must use setsid --wait.
For standalone use, send
SIGINT/SIGTERM to the monitor PID or signal that group; the caller's original
process group is not the cancellation boundary. On failure the monitor writes
partial evidence. Descendants are stopped on every exit using PID handles; if
that cleanup fails, SIGKILL of the entire group is the final fallback.
The collector already launches the monitor in a dedicated session.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
import signal
import select
import sys
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


def cpu_counter(fields: list[int]) -> tuple[int, int]:
    """Return busy and total ticks without double-counting Linux guest time."""
    # Linux reports guest and guest_nice inside user and nice as well as in
    # their own columns.  Sum only through steal to avoid double counting.
    total = sum(fields[:8])
    idle = fields[3] + (fields[4] if len(fields) > 4 else 0)
    return total - idle, total


def cpu_counters() -> dict[int, tuple[int, int]]:
    counters: dict[int, tuple[int, int]] = {}
    for line in Path("/proc/stat").read_text().splitlines():
        if not line.startswith("cpu") or line.startswith("cpu "):
            continue
        name, *fields_text = line.split()
        fields = [int(value) for value in fields_text]
        counters[int(name[3:])] = cpu_counter(fields)
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


def parse_task(tgid: int, text: str) -> dict[str, object]:
    """Read identity and group ownership from the same Linux task stat record."""
    close = text.rfind(")")
    fields = text[close + 2 :].split()
    return {
        "tgid": tgid, "tid": int(text[: text.find(" ")]),
        "state": fields[0], "pgrp": int(fields[2]),
        "cpu": int(fields[36]), "comm": text[text.find("(") + 1 : close],
    }


def task_snapshot() -> list[dict[str, object]]:
    """Return each visible task, including its atomically observed process group."""
    result: list[dict[str, object]] = []
    for stat_path in Path("/proc").glob("[0-9]*/task/[0-9]*/stat"):
        try:
            result.append(parse_task(int(stat_path.parts[-4]), stat_path.read_text()))
        except (OSError, IndexError, ValueError):
            continue
    return result


def foreign_tasks(tasks: Iterable[dict[str, object]], monitored: Iterable[int],
                  owned_group: int) -> list[dict[str, object]]:
    # The monitor creates a dedicated process group before spawning the runner.
    # Children inherit it at fork, so even a child born during this scan is
    # classified correctly without a racy, earlier process ancestry snapshot.
    # The benchmark does not daemonize or change process groups.
    monitored = set(monitored)
    return [task for task in tasks if task["state"] == "R"
            and task["cpu"] in monitored and task["pgrp"] != owned_group]


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
            elif (
                record.get("kind") == "region"
                and record.get("label") in {"warm-loop", "cold-loop"}
            ):
                regions.append(
                    (int(record["mono_t0_ns"]), int(record["mono_t1_ns"]))
                )
        if not saw_header:
            raise ValueError(f"timed-region sidecar has no header: {path}")
    return merge_regions(regions), path_count


def interference_summary(
    samples: Iterable[dict[str, object]],
    measurement_cpu: int,
    sibling_cpus: Iterable[int],
    timed_regions_complete: bool,
    threshold: float,
) -> dict[str, object]:
    """Compute the timed-region interference quantities and verdict."""
    sample_list = list(samples)
    sibling_busy_seconds = sum(
        float(sample["busy_seconds"][str(cpu)]) * float(sample["timed_fraction"])
        for sample in sample_list
        for cpu in sibling_cpus
    )
    foreign_measurement_seconds = sum(
        float(sample["timed_overlap_seconds"])
        for sample in sample_list
        if any(
            int(task["cpu"]) == measurement_cpu
            for task in sample["foreign_runnable"]
        )
    )
    timed_wall_seconds = sum(
        float(sample["timed_overlap_seconds"]) for sample in sample_list
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
        for sample in sample_list
    )
    contaminated = (
        not timed_regions_complete
        or aggregate_interference_ratio is None
        or aggregate_interference_ratio > threshold
    )
    return {
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
    }


def write_telemetry(path: Path, document: dict[str, object]) -> None:
    temporary = path.with_name(path.name + f".tmp-{os.getpid()}")
    with temporary.open("w") as stream:
        stream.write(json.dumps(document, indent=2) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def stop_descendants(group: int, process: subprocess.Popen | None) -> None:
    """Drain our dedicated group without killing the monitor or reusing a PID.

    Keeping the monitor in the group preserves the collector's killpg timeout
    boundary. PID handles let ordinary cleanup retain the runner's exit code.
    Rescan to catch descendants forked while the previous scan was in flight.
    """
    deadline = time.monotonic() + 5
    while True:
        live = False
        for path in Path("/proc").glob("[0-9]*/stat"):
            descriptor = None
            try:
                pid = int(path.parent.name)
                if pid == os.getpid():
                    continue
                task = parse_task(pid, path.read_text())
                if task["pgrp"] != group:
                    continue
                descriptor = os.pidfd_open(pid)
                # The PID might have exited/recycled before pidfd_open. Confirm
                # the current process still belongs to our dedicated group;
                # the signal then targets only the process held by the handle.
                task = parse_task(pid, path.read_text())
                poller = select.poll()
                poller.register(descriptor, select.POLLIN)
                # A zombie leader can still have live worker threads. A process
                # pidfd becomes readable only after its last thread exits:
                # https://man7.org/linux/man-pages/man2/pidfd_open.2.html
                exited = any(mask & (select.POLLIN | select.POLLHUP)
                             for _, mask in poller.poll(0))
                if task["pgrp"] == group and not exited:
                    live = True
                    signal.pidfd_send_signal(descriptor, signal.SIGKILL)
            except (FileNotFoundError, ProcessLookupError):
                continue
            finally:
                if descriptor is not None:
                    os.close(descriptor)
        if not live:
            if process is not None:
                process.wait(timeout=1)
            return
        if time.monotonic() >= deadline:
            raise TimeoutError("owned process group did not drain in five seconds")
        time.sleep(0.01)


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
    if not monitor_affinity:
        parser.error("no CPU remains on which to run the telemetry monitor")
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
    # A session boundary prevents unrelated pipeline members from joining the
    # group we will kill on failure. Reuse the collector's fresh session; make
    # one for standalone use when POSIX permits it. A process-group leader
    # cannot setsid, so reject that launch before creating a measured child.
    if os.getsid(0) != os.getpid():
        if os.getpgrp() == os.getpid():
            parser.error("launch a process-group leader with setsid --wait")
        os.setsid()
    owned_group = os.getpgrp()
    # A dedicated group is also the cancellation boundary for standalone use:
    # signal the monitor PID (handled below) or its group, not the caller's group.
    interrupted_signal = None

    def interrupted(signum: int, _frame: object) -> None:
        nonlocal interrupted_signal
        interrupted_signal = signum
        raise InterruptedError(f"telemetry interrupted by signal {signum}")

    document = None
    process = None
    previous_handlers = {sig: signal.signal(sig, interrupted)
                         for sig in (signal.SIGTERM, signal.SIGINT)}
    try:
        process = subprocess.Popen(command, preexec_fn=pin_child, env=child_env)
        while True:
            time.sleep(args.interval)
            current = cpu_counters()
            current_mono_ns = time.monotonic_ns()
            tasks = task_snapshot()
            foreign = foreign_tasks(tasks, monitored, owned_group)
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
                    "owned_runnable": [task for task in tasks if task["state"] == "R"
                                       and task["pgrp"] == owned_group
                                       and task["tgid"] != os.getpid()],
                    "load_average": [round(value, 3) for value in os.getloadavg()],
                }
            )
            previous = current
            previous_mono_ns = current_mono_ns
            # Always take the sample that observes process completion. Otherwise a
            # short final timed region can fall between the last sample and the
            # next loop-condition poll and disappear from the graded interval set.
            if process.poll() is not None:
                break

        return_code = process.wait()
        sidecar_paths = sorted(
            args.output.parent.glob(Path(sidecar_stem).name + "-*.jsonl")
        )
        timed_regions_error: str | None = None
        try:
            timed_regions, sidecar_count = load_timed_regions(sidecar_paths)
        except (OSError, ValueError) as error:
            # Preserve a fail-closed telemetry document even when a sidecar was
            # truncated or malformed, so a long run leaves reviewable evidence.
            timed_regions = []
            sidecar_count = len(sidecar_paths)
            timed_regions_error = str(error)
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
        elapsed = (time.monotonic_ns() - started_mono_ns) / 1_000_000_000
        timed_regions_complete = (
            timed_regions_error is None and sidecar_count > 0 and bool(timed_regions)
        )
        verdict = interference_summary(
            samples,
            args.cpu,
            sibling_cpus,
            timed_regions_complete,
            args.max_core_interference_ratio,
        )
        document = {
            "schema": 3,
            "ownership": "dedicated-process-group",
            "owned_process_group": owned_group,
            "session_id": os.getsid(0),
            "child_pid": process.pid,
            "command": command,
            "cpu": args.cpu,
            "smt_siblings": sibling_cpus,
            "interval_seconds": args.interval,
            "started_utc": started,
            "ended_utc": utc_now(),
            "elapsed_seconds": round(elapsed, 3),
            "timed_region_sidecars": [str(path) for path in sidecar_paths],
            "timed_region_sidecars_retained": True,
            "timed_regions_error": timed_regions_error,
            "command_return_code": return_code,
            "thresholds": {
                "max_core_interference_ratio": args.max_core_interference_ratio,
            },
            "summary": {
                "sample_count": len(samples),
                "timed_region_sidecar_count": sidecar_count,
                "timed_region_count_after_union": len(timed_regions),
                "timed_regions_complete": timed_regions_complete,
                **verdict,
            },
            "samples": samples,
        }
        write_telemetry(args.output, document)
        if return_code != 0:
            return return_code
        if verdict["contaminated"] and args.fail_on_contamination:
            return 2
        return 0
    except BaseException as error:
        # Ignore repeated interruption while preserving the first failure.
        for sig in previous_handlers:
            signal.signal(sig, signal.SIG_IGN)
        document = {
            "schema": 3, "status": "rejected", "command": command,
            "cpu": args.cpu, "smt_siblings": sorted(siblings - {args.cpu}),
            "ownership": "dedicated-process-group",
            "owned_process_group": owned_group,
            "session_id": os.getsid(0),
            "child_pid": process.pid if process is not None else None,
            "started_utc": started, "ended_utc": utc_now(),
            "monitor_error": {"type": type(error).__name__, "message": str(error)},
            "timed_region_sidecars": [str(path) for path in sorted(
                args.output.parent.glob(Path(sidecar_stem).name + "-*.jsonl"))],
            "samples": samples, "summary": {"contaminated": True},
        }
        write_telemetry(args.output, document)
        print(f"telemetry monitor failed: {error}", file=sys.stderr, flush=True)
        if interrupted_signal is not None:
            return 128 + interrupted_signal
        raise
    finally:
        for sig in previous_handlers:
            signal.signal(sig, signal.SIG_IGN)
        try:
            stop_descendants(owned_group, process)
        except BaseException as cleanup_error:
            # Preserve any original error as well as the cleanup failure before
            # the last-resort group kill, which deliberately includes us.
            document = document or {"schema": 3, "command": command, "samples": samples}
            document.update(status="rejected", cleanup_error=str(cleanup_error))
            document.setdefault("summary", {})["contaminated"] = True
            try:
                write_telemetry(args.output, document)
            finally:
                os.killpg(owned_group, signal.SIGKILL)
        for sig, handler in previous_handlers.items():
            signal.signal(sig, handler)


if __name__ == "__main__":
    raise SystemExit(main())
