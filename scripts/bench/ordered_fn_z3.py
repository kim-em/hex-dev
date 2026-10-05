#!/usr/bin/env python3
"""Orientation Z3 RCF comparison of prepared infinitesimal operations.

Hex uses the existing lean-bench child; Z3 uses its pinned Python/FFI API in
this process. Preparation and process startup are outside both operation timers.
All samples are retained in adjacent, alternating, trial-major order.
Only subtraction-based comparisons are timed: Z3 has no separate operation
that computes an uncached sign of a prepared value. The rational n=0 controls
include dispatch, ctypes, allocation/deletion, a small subtraction and the
same sign branches; they are a conservative estimate of the FFI overhead.
"""
import argparse
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease as acquire_cpu

NAMES = ['comparison', 'denominators', 'compareHeight']
PARAMS = [128, 256, 512, 1024, 2048, 4096, 8192, 16384]


def parameters(name):
    if name == 'denominators':
        return [16, 32, 64, 128, 256, 512, 1024, 2048]
    if name == 'compareHeight':
        return [65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608]
    return PARAMS


def prepare(name, n):
    import z3
    from z3 import z3rcf as rcf
    ctx = z3.Context()
    zero, one = rcf.RCFNum(0, ctx), rcf.RCFNum(1, ctx)
    x = rcf.MkInfinitesimal('epsilon1', ctx)
    if name == 'scan':
        a, b, expected = -(x**n), None, -1
    elif name == 'degree':
        a, b, expected = (x**(n+1)-one).__div__(x-one), None, 1
    elif name == 'height':
        power = rcf.RCFNum(2, ctx)**n
        a, b, expected = (power+one).__div__(power+3), None, 1
    elif name == 'second':
        y = rcf.MkInfinitesimal('epsilon2', ctx)
        a, b, expected = x*y**n, None, 1
    elif name == 'third':
        y = rcf.MkInfinitesimal('epsilon2', ctx)
        z = rcf.MkInfinitesimal('epsilon3', ctx)
        a, b, expected = (x+y)*z**n, None, 1
    elif name == 'comparison':
        a = x**n
        b, expected = -a, 1
    elif name == 'denominators':
        p = (x**(n+1)-one).__div__(x-one)
        a, b, expected = one.__div__(p), one.__div__(p+one), 1
    elif name == 'compareHeight':
        power = rcf.RCFNum(2, ctx)**n
        a, b, expected = power+one, power+2, -1
    else:
        raise ValueError(name)
    # Like Hex comparison, execute subtraction before sign. Keep preparation
    # values alive in the closure; each temporary difference is released in-loop.
    def operation():
        value = a if b is None else a-b
        return -1 if value < zero else 0 if value == zero else 1
    if operation() != expected:
        raise AssertionError((name, n, expected))
    return operation, expected


def batch(operation, count):
    start = time.perf_counter_ns()
    result = 0
    for _ in range(count):
        result = operation()
    return time.perf_counter_ns()-start, result


def measure(operation, target):
    count = 1
    while True:
        elapsed, result = batch(operation, count)
        if elapsed >= target:
            return {'inner_repeats': count, 'total_nanos': elapsed,
                    'per_call_nanos': elapsed/count, 'result': result}
        count *= 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--first-trial', type=int, choices=range(3), default=0,
                        help='first trial to collect when completing an interrupted schedule')
    parser.add_argument('--overhead-only', action='store_true',
                        help='measure the same subtraction/sign FFI calls at rational inputs (n=0)')
    args = parser.parse_args()
    import z3
    if version('z3-solver') != '4.15.4.0' or z3.get_version() != (4, 15, 4, 0):
        raise RuntimeError('requires z3-solver 4.15.4.0')
    if args.check:
        for name in NAMES:
            for n in [0, 1, 4]:
                prepare(name, n)
        print('Z3 comparator: 9 preparation/sign checks passed')
        return
    os.chdir(ROOT)
    if subprocess.check_output(['git', 'status', '--porcelain'], text=True):
        raise RuntimeError('commit source changes before measurement')
    exe = ROOT / '.lake/build/bin/hexorderedfn_bench'
    hashes = json.loads(subprocess.check_output([str(exe), 'sign-hashes'], text=True))
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cpu, lease = acquire_cpu()
    try:
        os.sched_setaffinity(0, {cpu})
        os.environ['LEAN_NUM_THREADS'] = '4'
        sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
        context = {'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                   'command': sys.argv, 'cpu': cpu, 'host': platform.node(),
                   'platform': platform.platform(), 'python': sys.version,
                   'z3': version('z3-solver'), 'load_before': os.getloadavg(),
                   'python_executable': sys.executable, 'started_unix_ns': time.time_ns(),
                   'overhead_only': args.overhead_only,
                   'executable_sha256': sha(exe), 'driver_sha256': sha(__file__)}
        libs = {line.split()[-1] for line in Path('/proc/self/maps').read_text().splitlines()
                if 'libz3.so' in line}
        if len(libs) != 1:
            raise RuntimeError('cannot identify the loaded Z3 library')
        lib = Path(libs.pop()).resolve()
        context.update(libz3_path=str(lib), libz3_sha256=sha(lib))
        params = lambda name: [0] if args.overhead_only else parameters(name)
        schedule = {'names': NAMES, 'parameters': {n: params(n) for n in NAMES},
                    'trials': 3, 'first_trial': args.first_trial, 'target_nanos': 1000000000,
                    'order': ('trial-major Z3 rational controls' if args.overhead_only else
                              'trial-major; adjacent Hex/Z3 on even trials, Z3/Hex on odd trials')}
        (output/'context.json').write_text(json.dumps(context, indent=2)+'\n')
        (output/'schedule.json').write_text(json.dumps(schedule, indent=2)+'\n')
        with (output/'paired.jsonl').open('w') as rows:
            for trial in range(args.first_trial, 3):
                for name in NAMES:
                    for n in params(name):
                        operation, expected = prepare(name, n)
                        arms = ['z3'] if args.overhead_only else (['hex', 'z3'] if trial % 2 == 0 else ['z3', 'hex'])
                        for arm in arms:
                            if arm == 'hex':
                                command = [str(exe), '_child', '--bench', 'Hex.OrderedFnBench.'+name,
                                           '--param', str(n), '--target-nanos', '1000000000']
                                stem = output/f'{trial}-{name}-{n}'
                                with stem.with_suffix('.stdout').open('w') as out, stem.with_suffix('.stderr').open('w') as err:
                                    subprocess.run(command, stdout=out, stderr=err, check=True, timeout=60)
                                row = json.loads(stem.with_suffix('.stdout').read_text())
                                if (row['function'] != 'Hex.OrderedFnBench.'+name or row['param'] != n
                                        or row['env']['git_dirty']
                                        or not context['commit'].startswith(row['env']['git_commit'])
                                        or row['status'] != 'ok'
                                        or int(row['result_hash'], 16) != hashes[str(expected)]):
                                    raise AssertionError(row)
                            else:
                                row = measure(operation, 1000000000)
                                row['completed_unix_ns'] = time.time_ns()
                                if row['result'] != expected:
                                    raise AssertionError(row)
                            row.update(arm=arm, case=name, param=n, trial=trial)
                            rows.write(json.dumps(row)+'\n')
                            rows.flush()
                        del operation
        context.update(load_after=os.getloadavg(), executable_sha256_after=sha(exe),
                       completed_unix_ns=time.time_ns())
        (output/'context.json').write_text(json.dumps(context, indent=2)+'\n')
    finally:
        lease.close()


if __name__ == '__main__':
    main()
