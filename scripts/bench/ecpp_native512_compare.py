#!/usr/bin/env python3
"""Run frozen public native/full-construction arms with adjacent trial-major AB/BA scheduling."""
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

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--split', choices=['tuning','holdout'], required=True)
    parser.add_argument('--freeze', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('retain every completed comparison')
    freeze = json.loads(args.freeze.read_text())
    for path, digest in freeze['files'].items():
        if sha(ROOT/path) != digest:
            parser.error('frozen file changed: '+path)
    for name, digest in freeze['executables'].items():
        if sha(ROOT/'.lake/build/bin'/name) != digest:
            parser.error('frozen executable changed: '+name)
    corpus_path = ROOT/'reports/ecpp/native512/corpus-v1.json'
    corpus = json.loads(corpus_path.read_text())
    cases = [c for c in corpus['cases'] if c['split'] == args.split]
    cpu, lease = cpu_lease()
    report = dict(source=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        freeze_sha256=sha(args.freeze), corpus_sha256=sha(corpus_path), split=args.split,
        cpu=cpu,host=os.uname().nodename,platform=platform.platform(),loadavg=list(os.getloadavg()),
        protocol='two trial-major trials; adjacent native/construction arms; NC if trial+case index is even, CN otherwise; tuning controls once',
        cases=[],controls=[])
    def retain():
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    def run(case, trial, index, control=False):
        order = ['native','construction']
        if (trial+index)%2:
            order.reverse()
        row = dict(id=case['id'],subject=case['subject'],seed=case['seed'],trial=trial,order=order,arms={})
        report['controls' if control else 'cases'].append(row)
        for arm in order:
            arguments = ['hexecpp_native',str(case['subject']),str(case['seed']),'native512-public'] if arm == 'native' else ['hexecpp_compare',str(case['subject'])]
            command = ['taskset','-c',str(cpu),str(ROOT/'.lake/build/bin'/arguments[0]),*arguments[1:]]
            start = time.monotonic_ns()
            result = subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
            sample = dict(returncode=result.returncode,elapsed_ns=time.monotonic_ns()-start,stdout=result.stdout,stderr=result.stderr)
            row['arms'][arm] = sample
            retain()
            assert result.returncode == 0, result.stderr
            sample['result'] = json.loads(result.stdout)
            retain()
            if control:
                data = sample['result'] if arm == 'native' else sample['result']['construction']
                assert data['verdict'] != 'success', case['id']
            print(case['id'],trial,arm,sample['result'].get('verdict',sample['result'].get('construction',{}).get('verdict')),flush=True)
    try:
        for trial in range(2):
            for index,case in enumerate(cases):
                run(case,trial,index)
        if args.split == 'tuning':
            for index,case in enumerate(corpus['controls']):
                run(case,0,index,True)
    finally:
        retain()
        lease.close()

if __name__ == '__main__':
    main()
