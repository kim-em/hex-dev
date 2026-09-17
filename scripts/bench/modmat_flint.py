#!/usr/bin/env python3
"""Collect modular determinant and Dixon solve comparator measurements.

Uses the registered fixed sampling settings, alternates the adjacent arm order,
and retains every export, including capped calls. A nonblocking CPU lease picks
placement without waiting for an idle core. Set HEX_FLINT_BENCH_PYTHON to a
Python containing python-flint. Run after lake build hexmodularmatrix_bench.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--mode', choices=['baseline', 'divisor', 'solve', 'repeated'], default='baseline')
    parser.add_argument('--start-at', help='start at this exact registration')
    parser.add_argument('--max-seconds-per-call', type=float, help='operational cap override')
    parser.add_argument('--limit', type=int, help='collect only this many comparison points')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
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
        raise RuntimeError('all measurement CPU leases are held')
    os.sched_setaffinity(0, {cpu})
    # The parent needs separate workers for stderr.readToEnd and the cap timer.
    # The whole process tree remains pinned to this one CPU.
    os.environ['LEAN_NUM_THREADS'] = '2'
    # Trusted local exact-integer fixtures can produce determinants with
    # substantially more than Python's default 4300 decimal digits.
    os.environ['PYTHONINTMAXSTRDIGITS'] = '0'
    source = root / 'bench/HexModularMatrix/Bench.lean'
    prefix = dict(baseline='runModular', divisor='runDivisor', solve='run(?:Decomp|Solve)',
                  repeated='runRepeated')[args.mode]
    names = re.findall(r'setup_fixed_benchmark (' + prefix + r'\w+)', source.read_text())
    if args.start_at:
        names = names[names.index(args.start_at):]
    if args.limit is not None:
        if args.limit < 1:
            parser.error('--limit must be positive')
        names = names[:args.limit]
    python = os.environ.get('HEX_FLINT_BENCH_PYTHON', 'python3')
    versions = subprocess.check_output([python, '-c',
        'import json, platform, flint; print(json.dumps(dict('
        'python=platform.python_version(), python_flint=flint.__version__)))'], text=True)
    sources = ['bench/HexModularMatrix/Bench.lean',
               'conformance/HexModularMatrix/Fixtures.lean',
               'HexModularMatrix/Image.lean', 'HexModularMatrix/Bound.lean',
               'HexModularMatrix/Det.lean', 'HexModularMatrix/Decomp.lean',
               'HexModularMatrix/Lift.lean', 'HexModularMatrix/Solve.lean',
               'HexModularMatrix/Row.lean', 'HexModularMatrix/Product.lean',
               'HexModularMatrix/FlatImage.lean', 'HexModularMatrix/Numerator.lean',
               'HexModularMatrix/Normalise.lean', 'HexModularMatrix/Reconstruction.lean',
               'HexModularMatrix/SolveMat.lean', 'HexModularMatrix/Divisor.lean',
               'Hex/BenchOracle/Flint.lean',
               'scripts/oracle/flint_bench_driver.py', 'scripts/bench/modmat_flint.py']
    data = {
        'versions': json.loads(versions), 'cpu': cpu, 'lean_num_threads': 2,
        'python_int_max_str_digits': 0,
        'load_before': Path('/proc/loadavg').read_text().strip(),
        'source_commit': subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
        'source_sha256': {p: hashlib.sha256((root / p).read_bytes()).hexdigest()
                          for p in sources},
        'sampling': 'five fixed repeats, 0.2 s floor, discarded outer and inner '
                    'warmups; adjacent comparison arms reverse on alternate rungs',
        'mode': args.mode, 'runs': [],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='modmat-flint-') as temporary:
        executable = Path(temporary) / 'hexmodularmatrix_bench'
        shutil.copy2(root / '.lake/build/bin/hexmodularmatrix_bench', executable)
        data['executable_sha256'] = hashlib.sha256(executable.read_bytes()).hexdigest()
        for index, name in enumerate(['runFlintOverhead'] + names):
            arms = ['Hex.ModularMatrixBench.' + name]
            if index:
                if args.mode == 'baseline':
                    arms += [arms[0].replace('runModular', 'runBareiss'),
                             arms[0].replace('runModular', 'runFlint')]
                elif args.mode == 'divisor':
                    arms += [arms[0].replace('runDivisor', other)
                             for other in ['runModular', 'runBareiss', 'runFlint']]
                elif args.mode == 'solve' and 'runSolve' in name:
                    arms += [arms[0].replace('runSolve', 'runFlintSolve')]
                elif args.mode == 'repeated':
                    arms += [arms[0].replace('runRepeated', 'runIndependent')]
                if index % 2 == 0:
                    arms.reverse()
            run = {'commands': [], 'exit_code': 0, 'wall_seconds': 0, 'log': ''}
            data['runs'].append(run)
            for arm_index, arm in enumerate(arms):
                export = Path(temporary) / f'{index}-{arm_index}.json'
                command = [str(executable), 'run', arm, '--export-file', str(export)]
                if args.max_seconds_per_call is not None:
                    command += ['--max-seconds-per-call', str(args.max_seconds_per_call)]
                start = time.monotonic()
                result = subprocess.run(command, cwd=root, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                run['commands'].append(command)
                run['exit_code'] |= result.returncode
                run['wall_seconds'] += time.monotonic() - start
                run['load'] = Path('/proc/loadavg').read_text().strip()
                run['log'] += result.stdout
                if export.exists():
                    arm_export = json.loads(export.read_text())
                    if 'export' not in run:
                        run['export'] = arm_export
                    else:
                        run['export']['results'].extend(arm_export['results'])
                # Checkpoint each completed arm, even if a later arm is interrupted.
                data['load_after'] = run['load']
                checkpoint = args.output.with_suffix(args.output.suffix + '.partial')
                checkpoint.write_text(json.dumps(data, indent=2) + '\n')
                checkpoint.replace(args.output)
                print(f'{index}: {arm}: exit {result.returncode}', flush=True)


if __name__ == '__main__':
    main()
