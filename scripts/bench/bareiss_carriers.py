#!/usr/bin/env python3
"""Collect the registered Bareiss carrier comparisons with lean-bench.

Run after `lake build hexbareiss_bench`, with HEX_CARRIER_BENCH_PYTHON pointing
to a Python containing python-flint and SymPy. This schedules the existing
fixed registrations without overriding their sampling settings. Adjacent
Hex/oracle pairs alternate AB/BA order across sweep points. A nonblocking CPU
lease chooses placement without measuring or waiting for low host activity.
Every completed export is retained, including failures.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--pilot', type=Path, help='retain an existing functional-check export')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = root / 'bench/HexBareiss/Bench.lean'
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    cpus = cpus[offset:] + cpus[:offset]
    for cpu in cpus:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            lease.close()
    else:
        raise RuntimeError('all measurement CPU leases are held')
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    names = re.findall(
        r'setup_fixed_benchmark (runBareiss(?:Rat|Mod|DenseRat|DenseMod|ZPoly|MvInt|MvRat)N\w+)',
        source.read_text())
    python = os.environ.get('HEX_CARRIER_BENCH_PYTHON', 'python3')
    packages = subprocess.check_output([python, '-c',
        'import json, platform, flint, sympy; print(json.dumps(dict(python=platform.python_version(), '
        'python_flint=flint.__version__, sympy=sympy.__version__)))'], text=True)
    sources = ['bench/HexBareiss/Bench.lean', 'Hex/BenchOracle/Carriers.lean',
               'scripts/oracle/matrix_carriers.py', 'scripts/oracle/common.py',
               'scripts/bench/bareiss_carriers.py']
    data = {
        'python_packages': json.loads(packages),
        'source_sha256': {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                          for name in sources},
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
        'bench_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'cpu': cpu, 'load_before': Path('/proc/loadavg').read_text().strip(),
        'sampling': 'lean-bench fixed default five repeats; adjacent pairs alternate AB/BA by sweep point',
        'runs': [],
    }
    if args.pilot:
        data['pilot'] = json.loads(args.pilot.read_text())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='bareiss-carriers-') as temporary:
        for index, name in enumerate(['runCarrierOverhead'] + names):
            arms = ['Hex.BareissBench.' + name]
            if index:
                arms.append(arms[0].replace('runBareiss', 'runOracle'))
                if index % 2 == 0:
                    arms.reverse()
            export = Path(temporary) / f'{index}.json'
            command = [str(root / '.lake/build/bin/hexbareiss_bench'),
                       'compare' if index else 'run', *arms, '--export-file', str(export)]
            start = time.monotonic()
            result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            run = {'command': command, 'exit_code': result.returncode,
                   'wall_seconds': time.monotonic() - start,
                   'load': Path('/proc/loadavg').read_text().strip(), 'log': result.stdout}
            if export.exists():
                run['export'] = json.loads(export.read_text())
            data['runs'].append(run)
            data['load_after'] = Path('/proc/loadavg').read_text().strip()
            args.output.write_text(json.dumps(data, indent=2) + '\n')
            print(f'{index}: {name}: exit {result.returncode}', flush=True)
            if result.returncode:
                raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
