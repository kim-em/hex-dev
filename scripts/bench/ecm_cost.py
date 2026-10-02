#!/usr/bin/env python3
"""Four fixed trial-major paired ECM construction measurements in two checkouts.

Checkouts differ only in the implementation/configuration under study. Each
fresh-module sample removes its own probe artifact; the caller must build its dependencies first.
No sample is retried or discarded. Failed builds are retained and do not stop the
schedule. The caller supplies the same finite resource settings in both arms.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import corpus

MODULE = 'HexPrimality.EcmDiagnostics.EcmCost'
SOURCE = Path('bench') / (MODULE.replace('.', '/') + '.lean')
# A separate observer process reports resource.getrusage for its single child.
# This is measurement isolation, never a route around an elaborator's budget.
OBSERVER = '''import json,resource,subprocess,sys,time
start=time.monotonic()
r=subprocess.run(sys.argv[2:])
with open(sys.argv[1],'w') as f: json.dump(dict(seconds=time.monotonic()-start,returncode=r.returncode,maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss),f)
sys.exit(r.returncode)
'''

def parse_result(stdout, phase, subject, case):
    """Require one complete result; CI smoke output cannot become a sample."""
    lines = ([line for line in stdout.splitlines() if line.startswith('{')]
             if phase == 'native' else
             [line.split('ECM_COST ', 1)[1] for line in stdout.splitlines() if 'ECM_COST ' in line])
    if len(lines) != 1:
        raise ValueError(f'expected one measurement record, got {len(lines)}')
    result = json.loads(lines[0])
    required = {'nanos', 'heartbeats_raw', 'attempts', 'result' if phase == 'residual' else 'status'}
    if not isinstance(result, dict) or not required <= result.keys():
        raise ValueError('incomplete measurement record')
    if 'subject' in result and str(result['subject']) != str(subject):
        raise ValueError('measurement subject changed')
    if 'case' in result and result['case'] != case:
        raise ValueError('measurement case changed')
    if 'certificate' in result:
        match = re.search(r'PrimeCert\.\w+\s+(\d+)', result['certificate'])
        if match is None or match[1] != str(subject):
            raise ValueError('certificate subject changed')
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--a', type=Path, required=True)
    p.add_argument('--b', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--module', default=MODULE,
                   help='construction module name; allows replay of archived layouts')
    p.add_argument('--phase', choices=['construction', 'native', 'residual', 'loading'], default='construction')
    args = p.parse_args()
    if args.output.exists():
        p.error('output already exists')
    paths = dict(A=args.a.resolve(), B=args.b.resolve())
    module = args.module
    if args.phase in ['residual', 'loading']:
        module = args.module.replace('EcmCost', 'Ecm' + args.phase.capitalize())
    measured = Path('bench') / (module.replace('.', '/') + '.lean')
    record = dict(host=platform.node(), platform=platform.platform(), cpu=pick(), phase=args.phase,
        toolchain=(ROOT/'lean-toolchain').read_text().strip(),
        driver_source=Path(__file__).read_text(),
        commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        protocol='four fixed trial-major blocks, adjacent AB/BA; retain all completed calls',
        settings=dict(maxHeartbeats=4000000 if args.phase in ['construction','residual'] else None,
            maxRecDepth=1024 if args.phase in ['construction','residual'] else None,
            options_note='null means no explicit elaborator option; native executable observes counters only',
            construction_defaults=dict(bounds=[32768,524288], curves=64)),
        arms={}, samples=[], complete=False)
    for arm, path in paths.items():
        files = [measured, Path('bench/HexPrimality/FieldProbe.lean'), Path('lakefile.lean'), Path('HexIntFactor/EcmStage2.lean'),
                 Path('HexIntFactor/Construction.lean'), Path('HexPrimality/Construction.lean')]
        record['arms'][arm] = dict(path=str(path), sources={str(f): (path/f).read_text() for f in files},
            source_sha256={str(f): hashlib.sha256((path/f).read_bytes()).hexdigest() for f in files})
        if args.phase == 'native':
            exe = path/'.lake/build/bin/hexprimality_field_probe'
            record['arms'][arm]['executable_sha256'] = hashlib.sha256(exe.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    def save():
        args.output.write_text(json.dumps(record, indent=2)+'\n')
    cases = [c for c in corpus() if c['name'] in ['secp256k1','P-384','Curve448','P-521']]
    if args.phase == 'residual':
        cases = [dict(name=n,n='0') for n in ['stage1','stage2','failure','recovery']]
    if args.phase == 'loading':
        cases = [dict(name='imports',n='7')]
    for block in range(4):
        for case in cases:
            for arm in ('AB' if block % 2 == 0 else 'BA'):
                path = paths[arm]
                if args.phase != 'native':
                    artifact = path/'.lake/build/lib/lean'/Path(module.replace('.','/')+'.olean')
                    artifact.unlink(missing_ok=True)
                    command = ['lake','build',module]
                else:
                    command = [str(path/'.lake/build/bin/hexprimality_field_probe'),
                               'construction2',case['n'],'32768','524288','64']
                env = dict(os.environ, ECM_SUBJECT=case['n'], ECM_DISPATCH='expression', ECM_CASE=case['name'], LEAN_NUM_THREADS='1')
                before = os.getloadavg()
                with tempfile.NamedTemporaryFile() as stats:
                    start = time.monotonic()
                    result = subprocess.run(['taskset','-c',str(record['cpu']),sys.executable,
                        '-c',OBSERVER,stats.name,*command], cwd=path, env=env, text=True, capture_output=True)
                    try:
                        row = json.loads(Path(stats.name).read_text())
                    except (ValueError, OSError):
                        # Preserve observer failures too (e.g. an OOM kill).
                        row = dict(seconds=time.monotonic()-start, returncode=result.returncode,
                                   maxrss_kib=None, parse_error='observer statistics unavailable')
                row.update(block=block,case=case['name'],arm=arm,command=command,
                    stdout=result.stdout,stderr=result.stderr,load_before=before,load_after=os.getloadavg())
                record['samples'].append(row)
                save()
                if result.returncode == 0 and args.phase != 'loading':
                    try:
                        row['result'] = parse_result(result.stdout, args.phase, case['n'], case['name'])
                    except (ValueError, TypeError) as error:
                        previous = row.get('parse_error')
                        row['parse_error'] = f'{previous}; {error}' if previous else str(error)
                save()
                print(block,case['name'],arm,row['returncode'],round(row['seconds'],3),flush=True)
    record['complete'] = True
    record['failed_samples'] = [i for i,r in enumerate(record['samples']) if r['returncode'] or 'parse_error' in r]
    # Compare semantic outputs independently of timing, allocation and host data.
    references = {}
    mismatches = []
    for i,row in enumerate(record['samples']):
        if 'result' not in row:
            continue
        semantic = {k:v for k,v in row['result'].items()
                    if 'nanos' not in k and k != 'heartbeats_raw'}
        if references.setdefault(row['case'], semantic) != semantic:
            mismatches.append(i)
    record['semantic_mismatches'] = mismatches
    save()
    if mismatches or record['failed_samples']:
        raise SystemExit('failed or inconsistent measurements; see retained samples')

if __name__ == '__main__':
    main()
