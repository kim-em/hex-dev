#!/usr/bin/env python3
"""Measure the adopted construction on retained ECPP cases and an exhausted search."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
FAILURE = 325201940467712409581766354955805106229098916130042842589140035735389409205180013414465418744822299840352633258734186556814478386800626664214444960969771


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cases():
    selected = []
    for name in ['campaign-updated', 'validation']:
        source = f'reports/ecpp/native/{name}.json'
        for case in json.loads((ROOT / source).read_text())['cases']:
            if (case['bits'] == 256 and case['native']['verdict'] == 'success'
                    and case['construction']['construction']['verdict'].endswith('exhausted')):
                selected.append(dict(id=case['id'], subject=case['subject'], bits=256,
                                     native_verdict='success', source=source))
    source = 'reports/ecpp/native512/comparison-holdout-v2.json'
    for case in json.loads((ROOT / source).read_text())['cases']:
        if case['trial'] == 0:
            selected.append(dict(id=case['id'], subject=case['subject'], bits=512,
                                 native_verdict=case['arms']['native']['result']['verdict'],
                                 source=source))
    return selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=180)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('output already exists; preserve completed observations')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cpu, lease = cpu_lease()
    executable = ROOT / '.lake/build/bin/hexprimality_factor_experiment'
    sources = ['HexIntFactor/Construction.lean', 'HexPrimality/Construction.lean',
               'bench/HexPrimality/FactorExperiment.lean']
    selected = cases()
    report = dict(complete=False, host=os.uname().nodename, cpu=cpu,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  sources={p: digest(ROOT / p) for p in sources},
                  toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                  executable_sha256=digest(executable), timeout_seconds=args.timeout,
                  cases=selected, samples=[])
    def save():
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    save()
    schedule = [(dict(id='exhausted-507', subject=FAILURE, bits=507), trial, profile)
                for trial in range(4)
                for profile in (['baseline', 'interleaved'] if trial % 2 == 0
                                else ['interleaved', 'baseline'])]
    schedule += [(case, 0, 'interleaved') for case in selected]
    with tempfile.TemporaryDirectory(prefix='hex-primality-adoption-') as folder:
        snapshot = Path(folder) / executable.name
        shutil.copy2(executable, snapshot)
        for case, trial, profile in schedule:
            assert digest(snapshot) == report['executable_sha256']
            command = ['taskset', '-c', str(cpu), str(snapshot), 'construct', profile, str(case['subject'])]
            row = dict(case=case['id'], subject=case['subject'], bits=case['bits'], trial=trial,
                       profile=profile, command=command, load_before=os.getloadavg())
            start = time.monotonic_ns()
            try:
                run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
                row.update(state='completed', returncode=run.returncode, stdout=run.stdout, stderr=run.stderr)
                if run.returncode == 0:
                    row['result'] = json.loads(run.stdout)
            except subprocess.TimeoutExpired as exc:
                row.update(state='timeout', stdout=(exc.stdout or b'').decode(),
                           stderr=(exc.stderr or b'').decode())
            row.update(wall_ns=time.monotonic_ns() - start, load_after=os.getloadavg())
            report['samples'].append(row)
            save()
            print(case['id'], trial, profile, row.get('result', {}).get('status', row['state']), flush=True)
    lease.close()
    report['complete'] = True
    save()


if __name__ == '__main__':
    main()
