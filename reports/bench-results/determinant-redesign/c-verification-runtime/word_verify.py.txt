#!/usr/bin/env python3
"""Bounded differential checks for the value-only C diagnostic."""
import ctypes
import json
from pathlib import Path
import random
import platform
import subprocess
import sys

from runtime import ROOT
from scripts.bench.det_bench_limits import supervise


def main():
    output = Path(sys.argv[1])
    output.mkdir(parents=True, exist_ok=False)
    source = ROOT / 'experiments/Determinant/word_loop.c'
    library = output / 'word_loop.so'
    cmd = ['cc', '-O2', '-shared', '-fPIC', '-fsanitize=undefined',
           '-fno-sanitize-recover=all', str(source), '-o', str(library)]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    (output / 'build.json').write_text(json.dumps(dict(command=cmd,
        exit_status=result.returncode, stdout=result.stdout, stderr=result.stderr), indent=2))
    assert result.returncode == 0
    for p in [source, Path(__file__)]:
        (output / (p.name + '.txt')).write_bytes(p.read_bytes())

    def run(_deadline):
        import flint
        for name in ['libubsan.so', f'libclang_rt.ubsan_standalone-{platform.machine()}.so']:
            runtime = subprocess.check_output(['cc', f'-print-file-name={name}'], text=True).strip()
            if Path(runtime).is_file():
                ctypes.CDLL(runtime, mode=ctypes.RTLD_GLOBAL)
                (output / 'sanitizer-runtime.txt').write_text(runtime + '\n')
                break
        lib = ctypes.CDLL(str(library.resolve()))
        det = lib.determinant
        det.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.c_size_t, ctypes.c_uint64]
        det.restype = ctypes.c_uint64
        records = []
        rng = random.Random(10320)
        for p in [3, 97, 2147483647]:
            for n, shape in [(0,'dense'), (1,'dense'), (2,'dense'), (5,'dense'),
                             (5,'swap'), (5,'singular'), (5,'boundary')]:
                a = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
                if shape == 'swap':
                    a[0][0] = 0
                    a[1][0] = 1
                if shape == 'singular':
                    a[1] = a[0][:]
                if shape == 'boundary':
                    a = [[p-1 if i != j else 1 for j in range(n)] for i in range(n)]
                buf = (ctypes.c_uint64 * (n*n))(*(x for row in a for x in row))
                expected = int(flint.fmpz_mat(a).det()) % p
                observed = det(buf, n, p)
                records.append(dict(modulus=p, dimension=n, shape=shape, input=a,
                                    observed=observed, expected=expected))
                (output / 'checks.json').write_text(json.dumps(records, indent=2))
                assert observed == expected
        print(f'{len(records)} C differential checks passed with undefined-behavior sanitizer')
    code = supervise(run, 60, output / 'status.json')
    library.unlink()
    return code


if __name__ == '__main__':
    raise SystemExit(main())
