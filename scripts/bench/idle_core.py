#!/usr/bin/env python3
"""Choose a logical CPU that is idle, and idle on all of its SMT siblings.

The factorization measurement recipes pin the measured service to one core so
its timings are not perturbed by the scheduler. Pinning to a *fixed* core --
historically `taskset -c 0` -- is only correct when one measurement runs at a
time. When several do, they land on the same core and each one measures the
others.

That failure is invisible in the usual place to look. On a 96-core host, three
measurement processes sharing core 0 leave the load average at 2 to 5 while
inflating roughly a quarter of a sweep's rows by about 1.9x, with the affected
rows differing from run to run because they depend on when the siblings
happened to be busy. `ps -eo pid,psr` shows it immediately; nothing else does.

This module picks a core that is currently free, so concurrent measurements on
the same host do not collide. It is a heuristic about *scheduling*, not about
correctness: a caller that needs a preregistered CPU for a release-quality
verdict (see SPEC/benchmarking.md, designated-shared-host protocol) should
still name one explicitly and record it.

Run::

    python3 scripts/bench/idle_core.py            # prints one core id
    taskset -c "$(python3 scripts/bench/idle_core.py)" some-measurement

or import `pick()`.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import sys
import time

# A core busy for less than this fraction of the sampling window counts as
# free. Timer ticks and kernel bookkeeping never leave a core at exactly zero.
BUSY_PERCENT = 5.0

# Core 0 additionally services interrupts and is the historical default of
# every recipe here, so it is the one core most likely to be contended.
AVOID = frozenset({0})


def sibling_map() -> dict[int, set[int]]:
    """Logical CPU -> the set of logical CPUs sharing its physical core."""
    siblings: dict[int, set[int]] = {}
    root = Path("/sys/devices/system/cpu")
    for path in sorted(root.glob("cpu[0-9]*/topology/thread_siblings_list")):
        try:
            cpu = int(path.parts[-3][3:])
            group = set()
            for part in path.read_text().strip().split(","):
                if "-" in part:
                    lo, hi = part.split("-")
                    group.update(range(int(lo), int(hi) + 1))
                else:
                    group.add(int(part))
            siblings[cpu] = group
        except (OSError, ValueError):
            continue
    return siblings


def _stat_jiffies() -> dict[int, tuple[int, int]]:
    """Per-CPU `(busy, total)` jiffy counters from /proc/stat."""
    counters: dict[int, tuple[int, int]] = {}
    for line in Path("/proc/stat").read_text().splitlines():
        if not line.startswith("cpu") or line.startswith("cpu "):
            continue
        name, _, rest = line.partition(" ")
        try:
            cpu = int(name[3:])
            fields = [int(v) for v in rest.split()]
        except ValueError:
            continue
        # user nice system idle iowait irq softirq steal ...
        total = sum(fields)
        idle = fields[3] + (fields[4] if len(fields) > 4 else 0)
        counters[cpu] = (total - idle, total)
    return counters


def busy_by_cpu(window: float = 0.3) -> dict[int, float]:
    """Percentage of `window` each logical CPU spent doing anything.

    Sampled from /proc/stat rather than from `ps`, whose `%CPU` is a
    lifetime average: a process that burned a core an hour ago and is idle now
    would read as busy, and one that started a moment ago would read as idle.
    The question here is only whether the core is busy *now*.
    """
    before = _stat_jiffies()
    time.sleep(window)
    after = _stat_jiffies()
    busy: dict[int, float] = {}
    for cpu, (busy_after, total_after) in after.items():
        busy_before, total_before = before.get(cpu, (0, 0))
        elapsed = total_after - total_before
        busy[cpu] = 100.0 * (busy_after - busy_before) / elapsed if elapsed else 0.0
    return busy


def pick(avoid: frozenset[int] = AVOID,
         busy_percent: float = BUSY_PERCENT) -> int:
    """Return a logical CPU that is free, and whose SMT siblings are free.

    Among the free candidates this returns the quietest, so a core sitting
    just under the threshold is not preferred to an entirely empty one and a
    transient blip cannot flip the choice to a worse core.

    Raises `RuntimeError` when the host has no such CPU, which is the honest
    outcome: on a saturated host there is no placement that avoids the
    interference this function exists to avoid.
    """
    busy = busy_by_cpu()
    siblings = sibling_map()
    candidates = sorted(siblings) or {cpu: {cpu} for cpu in sorted(busy)}
    free = []
    for cpu in candidates:
        if cpu in avoid:
            continue
        group = siblings.get(cpu, {cpu})
        load = max(busy.get(other, 0.0) for other in group)
        if load < busy_percent:
            free.append((load, cpu))
    if not free:
        raise RuntimeError(
            "no idle core: every logical CPU or one of its SMT siblings is busy")
    return min(free)[1]


def pin_self(cpu: int) -> None:
    """Pin this process, so every descendant inherits the affinity."""
    os.sched_setaffinity(0, {cpu})


def resolve(spec: str | int | None) -> int:
    """Interpret a `--cpu` argument: `auto` (or None) picks, else an id."""
    if spec is None or spec == "auto":
        return pick()
    return int(spec)


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--busy-percent", type=float, default=BUSY_PERCENT,
                   help=f"treat a core below this %%CPU as free "
                        f"(default {BUSY_PERCENT})")
    p.add_argument("--allow-cpu0", action="store_true",
                   help="consider core 0, which recipes historically default "
                        "to and which also services interrupts")
    args = p.parse_args()
    try:
        print(pick(avoid=frozenset() if args.allow_cpu0 else AVOID,
                   busy_percent=args.busy_percent))
    except RuntimeError as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
