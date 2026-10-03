#!/usr/bin/env python3
"""Retain tuning-only measurements of the explicit 512-bit allocation or instrumented baseline."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--profiles', choices=['native', 'diagnosis'], default='native')
    args = parser.parse_args()
    if args.output.exists():
        parser.error('output exists; retain completed diagnoses')
    source = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    producer = subprocess.check_output(['git', 'hash-object', 'HexECPP/Search.lean'], cwd=ROOT, text=True).strip()
    corpus_path = ROOT / 'reports/ecpp/native512/corpus-v1.json'
    allocation_path = ROOT / 'reports/ecpp/native512/allocations-v2.json'
    corpus = json.loads(corpus_path.read_text())
    subjects = [c for c in corpus['cases'] if c['split'] == 'tuning']
    exe = ROOT / '.lake/build/bin/hexecpp_native'
    cpu, lease = cpu_lease()
    report = dict(allocation_profile='native512_v2' if args.profiles == 'native' else 'diagnosis', source=source, producer_blob=producer, executable_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),
                  corpus_sha256=hashlib.sha256(corpus_path.read_bytes()).hexdigest(),
                  allocation_sha256=hashlib.sha256(allocation_path.read_bytes()).hexdigest(),
                  host=os.uname().nodename, platform=platform.platform(), cpu=cpu, loadavg=list(os.getloadavg()),
                  protocol='two trial-major tuning trials; adjacent core/public arms alternate AB/BA; controls once per arm',
                  cases=[], controls=[])
    def run(case, trial, index, control=False):
        prefix = 'native512' if args.profiles == 'native' else 'diagnose512'
        order = [prefix, prefix+'-public']
        if (trial + index) % 2:
            order.reverse()
        row = dict(id=case['id'], subject=case['subject'], seed=case['seed'], trial=trial, order=order, arms={})
        for arm in order:
            start = time.monotonic_ns()
            completed = subprocess.run(['taskset', '-c', str(cpu), str(exe), str(case['subject']), str(case['seed']), arm],
                                       cwd=ROOT, capture_output=True, text=True)
            elapsed = time.monotonic_ns() - start
            result = dict(returncode=completed.returncode, elapsed_ns=elapsed, stdout=completed.stdout, stderr=completed.stderr)
            if completed.returncode == 0:
                result['result'] = json.loads(completed.stdout)
            row['arms'][arm] = result
            print(case['id'], trial, arm, result.get('result', {}).get('verdict', 'process-error'), flush=True)
            report['controls' if control else 'cases'].append(row) if len(row['arms']) == 1 else None
            args.output.write_text(json.dumps(report, indent=2) + '\n')
        if control:
            for arm in row['arms'].values():
                data = arm.get('result', {})
                assert data.get('verdict') != 'success', (case['id'], data)
                if case['bits'] > 512:
                    assert data.get('resource') == 'Hex.ECPP.Resource.inputBits', data
    try:
        for trial in range(2):
            for index, case in enumerate(subjects):
                run(case, trial, index)
        for index, case in enumerate(corpus['controls']):
            run(case, 0, index, True)
    finally:
        lease.close()


if __name__ == '__main__':
    main()
