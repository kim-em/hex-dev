"""Lease one CPU for serial shared-host measurements."""
from __future__ import annotations

import fcntl
import os


def cpu_lease(requested=None):
    cpus = sorted(os.sched_getaffinity(0))
    if requested is not None:
        if requested not in cpus:
            raise RuntimeError("requested CPU is outside the process affinity")
        cpus = [requested]
    else:
        offset = os.getpid() % len(cpus)
        cpus = cpus[offset:] + cpus[:offset]
    for cpu in cpus:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return cpu, lease
        except BlockingIOError:
            lease.close()
    raise RuntimeError('all measurement CPU leases are held')
