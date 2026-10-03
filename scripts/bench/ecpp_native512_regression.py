#!/usr/bin/env python3
"""Compare all established 128/256-bit subjects with adjacent before/after trials."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('preserve every completed regression sample')
    baseline = args.baseline.resolve()
    expected = json.loads((ROOT/'reports/ecpp/native512/diagnosis-baseline-v1.json').read_text())['executable_sha256']
    assert sha(baseline) == expected, 'use the retained repaired-GMP baseline'
    executable = ROOT/'.lake/build/bin/hexecpp_native'
    corpora = [ROOT/'reports/ecpp/native'/name for name in ('corpus.json','validation-corpus.json')]
    cases = [dict(case,corpus=str(path.relative_to(ROOT))) for path in corpora for case in json.loads(path.read_text())['cases']]
    cpu, lease = cpu_lease()
    report = dict(source=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        baseline_source='0708462d844a9f11962b80bf707dd79ee9358bf4; baseline diagnostic driver ef08b6bf3',
        baseline_executable_sha256=sha(baseline),executable_sha256=sha(executable),
        corpus_hashes={str(path.relative_to(ROOT)):sha(path) for path in corpora},
        cpu=cpu,host=os.uname().nodename,loadavg=list(os.getloadavg()),
        protocol='four trial-major trials; adjacent before/after arms alternate AB/BA',samples=[],outputs={})
    def retain():
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    try:
        for trial in range(4):
            order = [('before',baseline),('after',executable)]
            if trial % 2:
                order.reverse()
            for case in cases:
                pair = {}
                for arm,exe in order:
                    command = ['taskset','-c',str(cpu),str(exe),str(case['subject']),str(case['seed'])]
                    start = time.monotonic_ns()
                    result = subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
                    sample = dict(id=case['id'],corpus=case['corpus'],subject=case['subject'],seed=case['seed'],
                        trial=trial,arm=arm,returncode=result.returncode,elapsed_ns=time.monotonic_ns()-start,
                        stderr=result.stderr,loadavg=list(os.getloadavg()))
                    report['samples'].append(sample)
                    retain()
                    assert result.returncode == 0, result.stderr
                    data = json.loads(result.stdout)
                    timings = {key:data.pop(key) for key in list(data) if key.endswith('_ns')}
                    # Retain identical raw outputs once; every sample references
                    # the full non-timing payload plus its original timing fields.
                    digest = hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest()
                    report['outputs'][digest] = data
                    sample.update(output_sha256=digest,timings=timings)
                    pair[arm] = data
                    retain()
                old,new = pair['before'],pair['after']
                for key in ('verdict','resource','unresolved','rand','rows','leaf','expanded','steps','checked','converted','data_bits'):
                    assert old.get(key) == new.get(key), (case['id'],key)
                for key,value in old['stats'].items():
                    assert new['stats'][key] == value, (case['id'],key)
                print(trial,case['id'],'exact verdict, certificate and original counters preserved',flush=True)
    finally:
        retain()
        lease.close()

if __name__ == '__main__':
    main()
