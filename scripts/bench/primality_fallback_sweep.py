#!/usr/bin/env python3
"""Four fixed adjacent AB/BA blocks for the complete-construction retry prototype."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_field_sweep import FAILURE, proof_source

MODULE = 'HexPrimality.ProofProbe.Curve25519.FallbackSample'
SOURCE = ROOT / 'bench' / (MODULE.replace('.', '/') + '.lean')
FIELDS = [('secp256k1', 2**256-2**32-977, '2 ^ 256 - 2 ^ 32 - 977'),
          ('P-384', 2**384-2**128-2**96+2**32-1, '2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1'),
          ('Curve448', 2**448-2**224-1, '2 ^ 448 - 2 ^ 224 - 1')]
CASES = FIELDS + [('P-521', 2**521-1, '2 ^ 521 - 1'),
                  ('Curve25519', 2**255-19, '2 ^ 255 - 19'),
                  ('507-bit', int(FAILURE['n']), FAILURE['n']), ('7', 7, '7'), ('15', 15, '15')]

def source(n, arm, options='set_option maxHeartbeats 4000000\n'):
    return ('module\nimport HexPrimality.ProofProbe.Curve25519.Fallback\n' + options +
            f'example : Hex.Nat.Prime ({n}) := by prototype_primality "{arm}"\n')

def main():
    global MODULE, SOURCE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--phase', choices=['all', 'native', 'options', 'elaboration', 'replay'], default='all')
    parser.add_argument('--certificates', type=Path)
    args = parser.parse_args()
    if args.phase != 'all':
        MODULE += args.phase.capitalize()
        SOURCE = ROOT / 'bench' / (MODULE.replace('.', '/') + '.lean')
    if args.phase == 'replay' and args.certificates is None:
        parser.error('replay requires --certificates from a native record')
    if args.output.exists() or (args.phase != 'native' and SOURCE.exists()):
        parser.error('output and temporary module must be absent')
    subprocess.run(['lake', 'build', 'hexprimality_field_probe',
                    'HexPrimality.ProofProbe.Curve25519.Fallback'], cwd=ROOT, check=True)
    cpu = pick()
    certificates = {}
    if args.certificates:
        for row in json.loads(args.certificates.read_text())['samples']:
            result = row.get('result', {})
            if result.get('status') == 'ok':
                certificates[row['case'], row['arm']] = result['certificate']
    paths = ['bench/HexPrimality/FieldProbe.lean',
             'bench/HexPrimality/ProofProbe/Curve25519/Fallback.lean',
             'HexPrimality/Construction.lean', 'HexIntFactor/Construction.lean',
             'HexIntFactor/EcmStage2.lean', 'lakefile.lean', 'scripts/bench/primality_fallback_sweep.py']
    record = dict(host=platform.node(), cpu=cpu, toolchain=(ROOT/'lean-toolchain').read_text(),
                  commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                  sources={p:(ROOT/p).read_text() for p in paths},
                  source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                  executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/hexprimality_field_probe').read_bytes()).hexdigest(),
                  protocol='four fixed trial-major blocks; adjacent AB/BA arms; retain every completed sample',
                  heartbeat_unit='raw IO.getNumHeartbeats delta; 1000 raw allocations per user heartbeat',
                  samples=[], completion='running', phase=args.phase)
    def save():
        args.output.write_text(json.dumps(record,indent=2)+'\n')
    def run(cmd, **fields):
        row=dict(command=cmd,load_before=os.getloadavg(),**fields)
        start=time.monotonic_ns()
        p=subprocess.run(['taskset','-c',str(cpu),*cmd],cwd=ROOT,capture_output=True,text=True,
                         env=dict(os.environ,LEAN_NUM_THREADS='1'))
        row.update(stdout=p.stdout,stderr=p.stderr,returncode=p.returncode,
                   elapsed_ns=time.monotonic_ns()-start,load_after=os.getloadavg())
        record['samples'].append(row)
        save()
        print({k:v for k,v in fields.items() if k != 'source'}, 'exit', p.returncode, flush=True)
        return row
    def build(text, **fields):
        SOURCE.write_text(text)
        artifact=ROOT/'.lake/build/lib/lean'/Path(MODULE.replace('.','/')+'.olean')
        artifact.unlink(missing_ok=True)
        return run(['lake','build',MODULE],source=text,**fields)
    try:
        # Reduced options are separate observations, never a search for a minimum.
        for name,n,power in (FIELDS if args.phase in ['all', 'options'] else []):
            for form,goal in [('numeral',str(n)),('power',power)]:
                for opts,label in [('', 'defaults'),('set_option maxHeartbeats 4000000\n','heartbeats-only')]:
                    build(source(goal,'auto',opts),phase='options',case=name,form=form,options=label)
        for block in (range(4) if args.phase != 'options' else []):
            for pair,cases in [(('explicit','auto'),FIELDS),(('core','auto'),CASES)]:
                order=pair if block%2==0 else pair[::-1]
                for name,n,_ in cases:
                    certs={arm: certificates[name, arm] for arm in order if (name, arm) in certificates}
                    for arm in (order if args.phase in ['all', 'native'] else []):
                        row=run(['.lake/build/bin/hexprimality_field_probe','measure-fallback',arm,str(n)],
                                phase='native',block=block,pair=pair,arm=arm,case=name)
                        if row['returncode']:
                            raise RuntimeError('native probe failed; result retained')
                        result=json.loads(row['stdout'])
                        row['result']=result
                        if result['status']=='ok': certs[arm]=result['certificate']
                        save()
                    if len(certs)==2 and len(set(certs.values()))!=1:
                        raise RuntimeError('successful certificate changed')
                    for arm in (order if args.phase in ['all', 'elaboration'] else []):
                        row=build(source(str(n),arm),phase='fresh-elaboration',block=block,pair=pair,arm=arm,case=name)
                        expected = name not in ['507-bit', '15'] and not (
                            arm == 'core' and name in [case[0] for case in FIELDS])
                        if (row['returncode'] == 0) != expected:
                            raise RuntimeError('unexpected elaboration outcome; sample retained')
                        if not expected and 'EXHAUSTED' not in row['stdout']:
                            raise RuntimeError('unexpected failure diagnostic; sample retained')
                    for arm in (order if args.phase in ['all', 'replay'] else []):
                        if arm not in certs:
                            expected = name not in ['507-bit', '15'] and not (
                                arm == 'core' and name in [case[0] for case in FIELDS])
                            if expected:
                                raise RuntimeError(f'missing successful certificate: {name}/{arm}')
                            continue
                        text=proof_source(str(n),certs[arm])
                        # Counter deltas observe each stage without changing any baseline.
                        text=text.replace('let start ← IO.monoNanosNow','let hb ← IO.getNumHeartbeats\n  let start ← IO.monoNanosNow')
                        text=text.replace('let stop ← IO.monoNanosNow','let stop ← IO.monoNanosNow\n  let used ← IO.getNumHeartbeats\n  Lean.logInfo m!"PHASE_HEARTBEATS_RAW {used - hb}"')
                        row=build(text,phase='render-replay',block=block,pair=pair,arm=arm,case=name)
                        if row['returncode']: raise RuntimeError('replay failed; result retained')
        record['completion']='complete'
    except BaseException as exc:
        record['completion']=str(exc)
        raise
    finally:
        if args.phase != 'native':
            SOURCE.unlink(missing_ok=True)
        save()

if __name__=='__main__': main()
