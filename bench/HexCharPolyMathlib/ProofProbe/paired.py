#!/usr/bin/env python3
"""Reproduce the dense16 diagnostic comparison, retaining every sample.

Run generate.py and build the imported modules before starting this runner.
It uses six fresh-module pairs with alternating orientation, then one
adjacent pair with the Lean profiler enabled. This is diagnostic evidence,
not the SPEC's release-quality comparison against Mathlib simp.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new directory for raw logs and measurements')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            lease.close()
    else:
        raise RuntimeError('all CPU leases held')
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    report = {'cpu': cpu, 'host': os.uname().nodename,
              'initial_load': os.getloadavg(), 'samples': []}
    print(json.dumps(report), flush=True)
    artifacts = Path('.lake/build/lib/lean/HexCharPolyMathlib/ProofProbe')
    for i in range(7):
        order = ['Candidate', 'Reference'] if i % 2 == 0 else ['Reference', 'Candidate']
        for arm in order:
            if i == 6:
                name = 'Dense16Quoted' if arm == 'Candidate' else 'Dense16Rank'
            else:
                name = 'Dense16' + arm
            for path in artifacts.glob(name + '.*'):
                path.unlink()
            start = time.monotonic()
            proc = subprocess.run(
                ['lake', 'build', f'HexCharPolyMathlib.ProofProbe.{name}:olean'],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = args.output / f'{i}-{arm}.log'
            log.write_text(proc.stdout)
            row = {'sample': i, 'arm': arm, 'profile': i == 6,
                   'wall_s': time.monotonic() - start, 'exit': proc.returncode,
                   'load': os.getloadavg(), 'log': log.name,
                   'kernel': re.findall(r'type checking ([0-9.]+[mu]?s)', proc.stdout)}
            report['samples'].append(row)
            print(json.dumps(row), flush=True)
            (args.output / 'paired.json').write_text(json.dumps(report, indent=2) + '\n')
            if proc.returncode:
                return proc.returncode
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
