"""Lease one CPU for serial shared-host measurements."""
from __future__ import annotations

import fcntl
import os


def cpu_lease():
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return cpu, lease
        except BlockingIOError:
            lease.close()
    raise RuntimeError('all measurement CPU leases are held')
