#!/usr/bin/env python3
"""Reconcile the frozen native corpora after accounting/diagnostic changes.

The existing emitter also records timings. They are retained, but this audit
checks verdicts, raw certificates and conversion; it does not retime the
unchanged full-construction comparator or replace its capability campaign.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('preserve completed runs; choose a new output')
    cpu, lease = cpu_lease()
    exe = ROOT / '.lake/build/bin/hexecpp_native'
    references = [ROOT / 'reports/ecpp/native' / p
                  for p in ('campaign-updated.json', 'validation.json')]
    report = dict(source=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  sources={str(p.relative_to(ROOT)): sha(p)
                           for p in sorted((ROOT / 'HexECPP').glob('*.lean'))},
                  executable_sha256=sha(exe), cpu=cpu, host=os.uname().nodename,
                  lean=subprocess.check_output(['lake', '--version'], text=True).strip(),
                  references={str(p.relative_to(ROOT)): sha(p) for p in references}, cases=[])
    try:
        for reference in references:
            for old in json.loads(reference.read_text())['cases']:
                command = ['taskset', '-c', str(cpu), str(exe), str(old['subject']), str(old['seed'])]
                result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
                row = dict(id=old['id'], subject=old['subject'], seed=old['seed'],
                           reference=str(reference.relative_to(ROOT)), command=command,
                           returncode=result.returncode, stderr=result.stderr,
                           loadavg=list(os.getloadavg()))
                if result.returncode:
                    row['stdout'] = result.stdout
                else:
                    current = json.loads(result.stdout)
                    row['native'] = current
                    row['same_verdict'] = current['verdict'] == old['native']['verdict']
                    if current['verdict'] == 'success':
                        row['same_certificate'] = all(current[key] == old['native'][key]
                                                      for key in ('rows', 'leaf', 'expanded'))
                        row['accepted'] = current['checked'] and current['converted']
                    else:
                        row['prior_diagnostic'] = {key: old['native'][key]
                                                   for key in ('resource', 'unresolved')}
                report['cases'].append(row)
                args.output.write_text(json.dumps(report, indent=2) + '\n')
                if result.returncode or not row['same_verdict'] or (
                    'same_certificate' in row and not (row['same_certificate'] and row['accepted'])):
                    raise RuntimeError(f"native contract changed: {old['id']}")
                print(old['id'], 'reconciled', flush=True)
    finally:
        lease.close()


if __name__ == '__main__':
    main()
