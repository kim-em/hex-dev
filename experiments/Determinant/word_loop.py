#!/usr/bin/env python3
"""Compare a C word-buffer diagnostic with FLINT on already measured prime images."""
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
from scripts.bench.det_bench_limits import supervise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path, help='retained value-flat/word batch')
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    code = Path(__file__).with_suffix('.c')
    library = args.output / 'word_loop.so'
    cmd = ['cc', '-O3', '-std=c11', '-Wall', '-Wextra', '-Werror', '-shared', '-fPIC',
           str(code), '-o', str(library)]
    compiled = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    (args.output / 'build.json').write_text(json.dumps(dict(command=cmd,
        exit_status=compiled.returncode, stdout=compiled.stdout, stderr=compiled.stderr,
        compiler=subprocess.check_output(['cc', '--version'], text=True)), indent=2))
    assert compiled.returncode == 0
    for p in [code, Path(__file__)]:
        (args.output / (p.name + '.txt')).write_bytes(p.read_bytes())
    entries = json.loads((args.source / 'input.json').read_text())
    samples = json.loads((args.source / 'results.json').read_text())['samples']
    primes = samples[0]['moduli_used']
    assert all(s['moduli_used'] == primes for s in samples)
    (args.output / 'input.json').write_text(json.dumps(entries))
    (args.output / 'moduli.json').write_text(json.dumps(primes))
    (args.output / 'sources.json').write_text(json.dumps({str(p):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in [code, Path(__file__), library]}, indent=2))

    def run(deadline):
        import flint
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
        lib = ctypes.CDLL(str(library.resolve()))
        det = lib.determinant
        det.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.c_size_t, ctypes.c_uint64]
        det.restype = ctypes.c_uint64
        n = len(entries)
        assert n <= 128 and all(len(row) == n for row in entries)
        assert all(2 < p < 2**31 and flint.fmpz(p).is_prime() for p in primes)
        matrices = [flint.nmod_mat(entries, p) for p in primes]
        buffers = [(ctypes.c_uint64 * (n*n))(*(x % p for row in entries for x in row))
                   for p in primes]
        expected = int(flint.fmpz_mat(entries).det())
        data = dict(cpu=cpu, topology=sweep.cpu_topology(cpu), environment=sweep.environment(),
                    flint_version=flint.__version__, samples=[])
        def expired(_sig, _frame):
            raise TimeoutError('image comparison exceeded 60 seconds')
        signal.signal(signal.SIGALRM, expired)
        try:
            for pair in range(2):
                for arm in (['C', 'FLINT'] if pair == 0 else ['FLINT', 'C']):
                    signal.alarm(min(60, max(1, int(deadline-time.monotonic()))))
                    start = time.perf_counter_ns()
                    if arm == 'C':
                        answers = [det(buf, n, p) for buf, p in zip(buffers, primes)]
                    else:
                        answers = [int(m.det()) for m in matrices]
                    elapsed = time.perf_counter_ns() - start
                    signal.alarm(0)
                    valid = answers == [expected % p for p in primes]
                    data['samples'].append(dict(arm=arm, pair=pair, elapsed_ns=elapsed,
                                                valid=valid, answers=answers))
                    (args.output / 'results.json').write_text(json.dumps(data, indent=2))
                    assert valid
                    print(arm, pair, elapsed/1e6, 'ms', flush=True)
        finally:
            signal.alarm(0)
            lease.close()
    result = supervise(run, 60, args.output / 'status.json')
    library.unlink()  # Generated binary is reproducible; archive source and hash.
    return result


if __name__ == '__main__':
    raise SystemExit(main())
