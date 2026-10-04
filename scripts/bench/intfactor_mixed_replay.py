#!/usr/bin/env python3
"""Fresh ordinary kernel replay of every frozen mixed output, with no production."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import time
from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('use a fresh output file')
    scratch = ROOT / 'HexIntFactor/Mixed/FreshReplayScratch'
    if scratch.exists():
        raise RuntimeError('scratch exists')
    scratch.mkdir()
    cpu, lease = cpu_lease()
    record = dict(cpu=cpu, host=platform.node(), platform=platform.platform(),
                  loadavg=list(os.getloadavg()), samples=[])
    try:
        for trial in range(2):
            for case in ('CaseA', 'CaseB', 'Partial'):
                source = (ROOT / f'HexIntFactor/Mixed/Frozen/{case}.lean').read_text()
                assert 'public import HexIntFactor.Mixed.Replay' in source
                assert 'Mathlib' not in source and 'Search' not in source and 'Export' not in source
                tag = f'Trial{trial}{case}'
                (scratch / f'{tag}.lean').write_text(source)
                start = time.monotonic_ns()
                result = subprocess.run(['taskset', '-c', str(cpu), 'lake', 'build',
                                         f'+HexIntFactor.Mixed.FreshReplayScratch.{tag}:olean'],
                                        cwd=ROOT, capture_output=True, text=True,
                                        env=dict(os.environ, HEX_INT_FACTOR_GP='/no-generation-on-replay'))
                record['samples'].append(dict(case=case, trial=trial, returncode=result.returncode,
                    wall_ns=time.monotonic_ns()-start, source_bytes=len(source.encode()),
                    source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                    stdout=result.stdout, stderr=result.stderr))
                args.output.write_text(json.dumps(record, indent=2)+'\n')
                print(tag, result.returncode, flush=True)
                if result.returncode:
                    raise RuntimeError(result.stdout + result.stderr)
    finally:
        args.output.write_text(json.dumps(record, indent=2)+'\n')
        lease.close()
        shutil.rmtree(scratch)
        for base in (ROOT / '.lake/build/lib/lean', ROOT / '.lake/build/ir'):
            shutil.rmtree(base / 'HexIntFactor/Mixed/FreshReplayScratch', ignore_errors=True)


if __name__ == '__main__':
    main()
