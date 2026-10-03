#!/usr/bin/env python3
"""Independently check every retained success and prove its raw checker in a fresh module."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'scripts/oracle'))
from ecpp_pari import check_step, pari_group_check, pari_isprime

STEP = re.compile(r'Hex\.ECPP\.Cert\.step\s+' + r'\s+'.join([r'(\d+)']*6) + r'\s+\[([\d,\s]*)\]')
PRIME = re.compile(r'Hex\.Nat\.PrimeCert\.(?:small|pock3Sieve|pock3|pock)\s+(\d+)')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('preserve previous validation observations')
    campaign = json.loads(args.campaign.read_text())
    cpu, lease = cpu_lease()
    report = dict(source=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        campaign_sha256=hashlib.sha256(args.campaign.read_bytes()).hexdigest(),
        cpu=cpu, host=os.uname().nodename, loadavg=list(os.getloadavg()),
        kernel_import='HexECPP.Cert', kernel_options=dict(maxRecDepth=200000,maxHeartbeats=0),
        successes=[], certificates=[])
    def retain():
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    known, primes = {}, {}
    try:
        for case in campaign['cases']:
            for arm, sample in case['arms'].items():
                r = sample.get('result',{})
                if r.get('verdict') != 'success':
                    continue
                expanded = r['expanded']
                digest = hashlib.sha256(expanded.encode()).hexdigest()
                report['successes'].append(dict(id=case['id'],trial=case['trial'],arm=arm,certificate_sha256=digest))
                if digest in known:
                    retain()
                    continue
                subjects = list(map(int, PRIME.findall(r['leaf'])))
                assert subjects, 'missing terminal subjects'
                matches = list(STEP.finditer(expanded))
                assert len(matches) == expanded.count('Hex.ECPP.Cert.step') == r['steps']
                rows = []
                for i, match in enumerate(matches):
                    fields = dict(zip('n a b x y d'.split(),map(int,match.groups()[:6])))
                    fields.update(kind='step',q=int(matches[i+1].group(1)) if i+1 < len(matches) else subjects[0],
                        witnesses=json.loads('['+match.group(7)+']'),accepted=True)
                    assert check_step(fields), (case['id'],i)
                    rows.append(fields)
                all_subjects = sorted(set(subjects+[row['n'] for row in rows]+[r['subject']]))
                for n in all_subjects:
                    if n not in primes:
                        primes[n] = pari_isprime(n)
                    assert primes[n], n
                pari_group_check(rows)
                record = dict(certificate_sha256=digest,id=case['id'],arm=arm,steps=len(rows),
                    subjects=all_subjects,independent_inverse_and_group_checks=True,pari_primality=True)
                report['certificates'].append(record)
                retain()
                with tempfile.TemporaryDirectory(prefix='Native512Scratch',dir=ROOT/'HexECPP') as folder:
                    path = Path(folder)
                    source = 'import HexECPP.Cert\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\n'
                    source += f'def certificate : Hex.ECPP.Cert := {expanded}\n\n'
                    source += f'example : Hex.ECPP.checkAt {r["subject"]} certificate = true := by decide\n'
                    (path/'Checked.lean').write_text(source)
                    start = time.monotonic_ns()
                    command = ['taskset','-c',str(cpu),'lake','build',f'+HexECPP.{path.name}.Checked:olean']
                    result = subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
                    record.update(fresh_kernel_ns=time.monotonic_ns()-start,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                        returncode=result.returncode,stdout=result.stdout,stderr=result.stderr,
                        proof_source_bytes=len(source.encode()))
                    retain()
                    for outputs in ('lib/lean','ir'):
                        shutil.rmtree(ROOT/'.lake/build'/outputs/'HexECPP'/path.name,ignore_errors=True)
                    assert result.returncode == 0, result.stdout+result.stderr
                known[digest] = record
                print(case['id'],arm,'independent checks and fresh kernel proof passed',flush=True)
    finally:
        retain()
        lease.close()

if __name__ == '__main__':
    main()
