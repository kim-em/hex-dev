#!/usr/bin/env python3
"""Record successful compilation and expected assertion failures for row guards."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[2]
MUTATIONS = [
    ('column-bound', ' || (uint64_t)last>=column_count', '', '==0'),
    ('gather-headroom', '< 4/width', '< (4/width-1)', '==(accepted?16:0)'),
    ('previous-column', 'if(previous>=(uint32_t)first) return 0;', '(void)previous;', '==0'),
    ('zero-coefficient', ' & _mm512_cmpgt_epi32_mask(b,_mm512_setzero_si512())', '', '==0'),
    ('high-bit-coefficient', '_mm512_cmpgt_epi32_mask(b,_mm512_setzero_si512())',
     '_mm512_cmpneq_epi32_mask(b,_mm512_setzero_si512())', '==0'),
    ('mode-guard', '    if(mersenne && (width!=4 || p!=INT32_MAX)) return 0;\n', '', '==0'),
]


def no_core():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('output', type=Path)
    p.add_argument('--cc', default=os.environ.get('CC', 'cc'))
    args = p.parse_args()
    args.output.mkdir(exist_ok=False)
    header = (ROOT/'HexGroebner/ffi/matrix_avx512.h').read_text()
    test = (ROOT/'HexGroebner/ffi/matrix_avx512_selftest.c').read_bytes()
    records = []
    for name, old, new, expected in [('control', '', '', ''), *MUTATIONS]:
        if name != 'control':
            if header.count(old) != 1 or new == old:
                raise ValueError('mutation must change one exact guard: '+name)
            changed = header.replace(old, new)
        else:
            changed = header
        directory = args.output/name
        directory.mkdir()
        (directory/'matrix_avx512.h').write_text(changed)
        (directory/'matrix_avx512_selftest.c').write_bytes(test)
        shutil.copy2(ROOT/'HexGroebner/ffi/matrix_simd.h', directory/'matrix_simd.h')
        binary = directory/'test'
        command = [args.cc, '-O2', '-std=c11', '-Wall', '-Wextra', '-Werror',
                   str(directory/'matrix_avx512_selftest.c'), '-o', str(binary)]
        with (directory/'compile.log').open('w') as log:
            compiled = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        record = dict(name=name, old=old, new=new, expected_assertion=expected,
                      compile=command, compile_exit_code=compiled.returncode,
                      run_exit_code=None, source_header_sha256=hashlib.sha256(header.encode()).hexdigest(),
                      test_sha256=hashlib.sha256(test).hexdigest())
        records.append(record)
        status = args.output/'status.json'
        status.write_text(json.dumps(records, indent=2)+'\n')
        if compiled.returncode:
            raise RuntimeError('mutant did not compile: '+name)
        with (directory/'stdout').open('w') as stdout, (directory/'stderr').open('w') as stderr:
            run = subprocess.run([str(binary)], stdout=stdout, stderr=stderr, preexec_fn=no_core,
                                 env=dict(os.environ, HEX_GROEBNER_REQUIRE_AVX512='1'))
        record['run_exit_code'] = run.returncode
        status.write_text(json.dumps(records, indent=2)+'\n')
        if name == 'control':
            if run.returncode or 'AVX-512 exact packets:' not in (directory/'stdout').read_text():
                raise RuntimeError('control did not execute the AVX-512 checks')
        else:
            error = (directory/'stderr').read_text()
            if run.returncode != -signal.SIGABRT or not all(
                    part in error for part in ['Assertion', 'hex_scan16_mode', expected, 'failed']):
                raise RuntimeError('mutant missed its expected assertion: '+name)
        print(name, record['compile_exit_code'], record['run_exit_code'], flush=True)
    shutil.copy2(__file__, args.output/'collector.py')


if __name__ == '__main__':
    main()
