#!/usr/bin/env python3
"""Run the frozen mixed-completion schedule, retaining all completed outcomes."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/bench'))
from cpu_lease import cpu_lease


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('use a fresh output directory; completed samples are never overwritten')
    args.output.mkdir(parents=True)
    output = args.output.resolve()
    plan = json.loads((ROOT / 'reports/intfactor/mixed/acceptance-v1.json').read_text())
    template = (ROOT / 'scripts/bench/intfactor_mixed.lean.in').read_text()
    cpu, lease = cpu_lease()
    record = dict(cpu=cpu, host=platform.node(), platform=platform.platform(),
                  loadavg=list(os.getloadavg()), plan=plan, samples=[],
                  sources={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in [ROOT / 'HexIntFactor/Mixed/Import.lean', ROOT / 'HexIntFactor/Mixed/Export.lean',
                                     ROOT / 'HexECPP/Search.lean', ROOT / 'scripts/bench/intfactor_mixed.lean.in']})
    scratch = ROOT / 'HexIntFactor/Mixed/MeasurementScratch'
    if scratch.exists():
        raise RuntimeError('measurement scratch exists')
    scratch.mkdir()
    try:
        for trial in range(2):
            for index, case in enumerate(plan['cases']):
                tag = f"Trial{trial}{case['id'].capitalize()}"
                order = ['legacy', 'ecpp'] if (trial + index) % 2 == 0 else ['ecpp', 'legacy']
                fields = dict(SUBJECT=case['subject'], BASE=case['base'], SMALL=case['small_base'],
                              EXPONENT=case['small_exponent'], LEGACY_SEED=case['legacy_seed'],
                              NATIVE_SEED=case['native_seed'], ORDER=json.dumps(order),
                              COMPLETE=str(case['expected'] == 'complete').lower(),
                              DECL={'a':'caseA', 'b':'caseB', 'partial':'partial'}[case['id']],
                              SOURCE_FILE=str(output / f'{tag}.lean'), REPORT_FILE=str(output / f'{tag}.json'))
                source = template
                for key, value in fields.items():
                    source = source.replace('@' + key + '@', str(value))
                (scratch / f'{tag}.lean').write_text(source)
                start = time.monotonic_ns()
                result = subprocess.run(['taskset', '-c', str(cpu), 'lake', 'build',
                                         f'+HexIntFactor.Mixed.MeasurementScratch.{tag}'],
                                        cwd=ROOT, capture_output=True, text=True)
                log = result.stdout + result.stderr
                (output / f'{tag}.log').write_text(log)
                sample = dict(case=case['id'], trial=trial, order=order,
                              wall_ns=time.monotonic_ns()-start, returncode=result.returncode,
                              log=f'{tag}.log')
                if (output / f'{tag}.json').exists():
                    sample['phases'] = json.loads((output / f'{tag}.json').read_text())
                    sample['source_sha256'] = hashlib.sha256((output / f'{tag}.lean').read_bytes()).hexdigest()
                record['samples'].append(sample)
                (output / 'measurements.json').write_text(json.dumps(record, indent=2)+'\n')
                print(tag, result.returncode, sample.get('phases', {}).get('source_bytes'), flush=True)
                if result.returncode:
                    raise RuntimeError(log)
    finally:
        (output / 'measurements.json').write_text(json.dumps(record, indent=2)+'\n')
        lease.close()
        shutil.rmtree(scratch)
        for base in (ROOT / '.lake/build/lib/lean', ROOT / '.lake/build/ir'):
            shutil.rmtree(base / 'HexIntFactor/Mixed/MeasurementScratch', ignore_errors=True)


if __name__ == '__main__':
    main()
