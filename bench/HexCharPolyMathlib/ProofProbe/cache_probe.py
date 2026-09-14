#!/usr/bin/env python3
"""Two adjacent AB/BA pairs testing removal of literal packed-column caches."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time
from compare import kernel_seconds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--cached-root', type=Path, required=True)
    parser.add_argument('--uncached-root', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    roots = {'Cached': args.cached_root.resolve(), 'Uncached': args.uncached_root.resolve()}
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
    report = {'cpu': cpu, 'host': os.uname().nodename, 'load': os.getloadavg(),
              'plan': {'paired_trials': 2, 'dimensions': [16, 32], 'timeout_s': 300,
                       'schedule': 'trial-major adjacent AB/BA',
                       'timeout_policy': 'retain timeout and stop'},
              'source_sha256': {}, 'samples': []}
    for arm, checkout in roots.items():
        report['source_sha256'][arm] = {}
        for name in ['HexCharPoly/Kernel.lean', 'HexCharPoly/CharPolyElab.lean',
                     'HexCharPolyMathlib/Kernel.lean', 'HexCharPolyMathlib/CharPolyElab.lean']:
            data = (checkout / name).read_bytes()
            report['source_sha256'][arm][name] = hashlib.sha256(data).hexdigest()
            (args.output / (arm + '-' + name.replace('/', '-') + '.txt')).write_bytes(data)
    for trial in range(2):
        for n in [16, 32]:
            name = f'Dense{n}Packed'
            probe = Path('bench/HexCharPolyMathlib/ProofProbe') / (name + '.lean')
            source = (root / probe).read_bytes()
            for checkout in roots.values():
                (checkout / probe).write_bytes(source)
            for arm in (['Cached', 'Uncached'] if trial == 0 else ['Uncached', 'Cached']):
                checkout = roots[arm]
                artifacts = checkout / '.lake/build/lib/lean/HexCharPolyMathlib/ProofProbe'
                for p in artifacts.glob(name + '.*'):
                    p.unlink()
                log_path = args.output / f'{trial}-{n}-{arm}.log'
                start = time.monotonic()
                with log_path.open('w') as log:
                    proc = subprocess.Popen(['lake', 'build', f'HexCharPolyMathlib.ProofProbe.{name}:olean'],
                        cwd=checkout, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                    try:
                        code = proc.wait(timeout=300)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                        code = 'timeout'
                row = {'trial': trial, 'n': n, 'arm': arm, 'exit': code,
                       'wall_s': time.monotonic() - start, 'load': os.getloadavg(),
                       'kernel_s': kernel_seconds(log_path.read_text()), 'log': log_path.name,
                       'artifacts_bytes': {p.suffix: p.stat().st_size for p in artifacts.glob(name + '.*')}}
                report['samples'].append(row)
                (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
                print(json.dumps(row), flush=True)
                if code != 0:
                    return


if __name__ == '__main__':
    main()
