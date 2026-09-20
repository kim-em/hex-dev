#!/usr/bin/env python3
"""Four fixed trial-major rounds of focused kernel-check profiling.

Retains every completed build. This is a different instrument from the original
paired whole-process observations, not a retry of that experiment.
"""
import argparse
import datetime
import json
import os
import platform
import re
from pathlib import Path

from run import HERE, ROOT, PROOFS, capture, clean, digest, host, lease_cpu, timed, validate_axioms


def parse_profile(text):
    checks = re.findall(r'^\s*type checking ([\d.e+-]+)(ms|s)$', text, re.M)
    beats = re.findall(r'Used (\d+) heartbeats,', text)
    if len(checks) != 1 or len(beats) != 1:
        raise ValueError(f'expected one cumulative checker time and heartbeat count: {checks}, {beats}')
    value, unit = checks[0]
    return {'kernel_ms': float(value) * (1000 if unit == 's' else 1), 'heartbeats': int(beats[0])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    if capture(['git', 'diff', '--name-only']) or capture(['git', 'diff', '--cached', '--name-only']):
        raise RuntimeError('commit experimental sources before measuring')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    checked = validate_axioms(output)
    (output/'kernel-inputs.json').write_bytes((HERE/'kernel-inputs.json').read_bytes())
    cpu, lease = lease_cpu()
    os.environ['LEAN_NUM_THREADS'] = '1'
    meta = {'commit': capture(['git', 'rev-parse', 'HEAD']),
            'collected_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'checked_theorems': checked, 'cpu': cpu, 'rounds': 4, 'schedule': 'trial-major',
            'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
            'platform': platform.uname()._asdict(),
            'cpuinfo': Path('/proc/cpuinfo').read_text().split('\n\n')[0],
            'sources': {str(p.relative_to(ROOT)): digest(p) for p in HERE.rglob('*')
                        if p.is_file() and p.suffix in {'.lean', '.py', '.smt2', '.patch', '.json'}
                        and '__pycache__' not in p.parts}, 'host_before': host()}
    (output/'meta.json').write_text(json.dumps(meta, indent=2)+'\n')
    with (output/'runs.jsonl').open('x') as stream:
        for trial in range(4):
            for name, case in PROOFS:
                module = f'CadSampleCosts.{case}.Kernel'
                clean(module)
                row, text = timed(['lake', 'build', f'+{module}:olean'], 120, ROOT,
                                  output/f'kernel-{trial}-{name}.log')
                row.update(kind='kernel', round=trial, example=name)
                try:
                    row.update(parse_profile(text))
                except ValueError as error:
                    row['parse_error'] = str(error)
                stream.write(json.dumps(row)+'\n')
                stream.flush()
                print(trial, name, row.get('kernel_ms'), row.get('heartbeats'), row['exit_code'], flush=True)
    meta['host_after'] = host()
    (output/'meta.json').write_text(json.dumps(meta, indent=2)+'\n')
    lease.close()


if __name__ == '__main__':
    main()
