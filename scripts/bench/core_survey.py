#!/usr/bin/env python3
"""Retain an untimed physical-core survey; never certify operation timings."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import sys
import time

try:
    import core_telemetry
    import idle_core
except ModuleNotFoundError:
    from scripts.bench import core_telemetry, idle_core


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=30)
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('--seconds must be positive')
    if args.output.exists():
        parser.error('output already exists')
    topology = idle_core.sibling_map()
    observer = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {observer})
    excluded = topology[observer]
    tick_hz = os.sysconf('SC_CLK_TCK')
    document = dict(status='observational', host=socket.gethostname(),
        command=sys.argv, requested_seconds=args.seconds, tick_hz=tick_hz,
        observer_cpu=observer, excluded_cpus=sorted(excluded),
        source_sha256={str(p): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (Path(__file__), Path(core_telemetry.__file__), Path(idle_core.__file__))})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    core_telemetry.write_telemetry(args.output, document)
    try:
        document['started_utc'] = core_telemetry.utc_now()
        before = core_telemetry.cpu_counters()
        start = time.monotonic_ns()
        time.sleep(args.seconds)
        end = time.monotonic_ns()
        after = core_telemetry.cpu_counters()
        duration = (end - start) / 1e9
        document.update(ended_utc=core_telemetry.utc_now(), mono_t0_ns=start,
            mono_t1_ns=end, before=before, after=after, cores=[])
        for cpu, siblings in sorted(topology.items()):
            if cpu != min(siblings) or siblings & excluded:
                continue
            busy = {str(c): core_telemetry.busy_seconds(before[c], after[c], tick_hz)
                    for c in sorted(siblings)}
            document['cores'].append(dict(cpus=sorted(siblings), busy_seconds=busy,
                max_busy_fraction=max(busy.values()) / duration))
        core_telemetry.write_telemetry(args.output, document)
        for row in sorted(document['cores'], key=lambda r: (r['max_busy_fraction'], r['cpus']))[:8]:
            print(json.dumps(row))
    except BaseException as error:
        document.update(status='failed', error_type=type(error).__name__, error=str(error))
        core_telemetry.write_telemetry(args.output, document)
        raise


if __name__ == '__main__':
    main()
