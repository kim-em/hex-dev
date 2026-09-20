#!/usr/bin/env python3
"""Retain stage-2 phase and adjacent-policy measurements from existing benches.

This is a manual diagnostic/comparison driver, not a scaling harness. Scaling
uses pminusone_stage2_sweep.py and lean-bench's fixed trial-major schedule.
Native timing uses lean-bench fixed child runners, excluding subprocess startup and serialization. Every completed
sample is appended immediately; an interrupted file remains useful evidence.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import tempfile
import subprocess
import time
import idle_core
import pminusone_stage2_fixtures as fixtures

ROOT = fixtures.ROOT
PRIMALITY = ROOT / '.lake/build/bin/hexprimality_bench'
FACTOR = ROOT / '.lake/build/bin/hexintfactor_bench'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['phases', 'preparation', 'trace', 'endpoint', 'factor', 'construction', 'parents'])
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--resume-from', action='append', type=Path, help='retain complete pairs from an interrupted collection')
    parser.add_argument('--seed', type=int, choices=range(5), help='one independent factor seed')
    parser.add_argument('--case', help='one independent consumer fixture')
    parser.add_argument('--controls', action='store_true', help='factor table/balanced/smooth controls only')
    parser.add_argument('--partition', default='0/1', help='independent consumer fixture group INDEX/COUNT')
    args = parser.parse_args()
    if args.output.exists() or Path(str(args.output)+'.gz').exists():
        parser.error('output already exists, possibly compressed; choose a fresh path')
    if args.resume_from and args.mode not in ('factor',):
        parser.error('--resume-from applies to policy comparisons')
    part, parts = map(int,args.partition.split('/'))
    if not 0 <= part < parts or (parts != 1 and args.mode not in ('factor', 'parents')):
        parser.error('invalid factor partition')
    if args.case and args.mode not in ('factor', 'parents'):
        parser.error('--case applies only to factor or parent comparisons')
    if (args.controls or args.seed is not None) and args.mode != 'factor':
        parser.error('--controls and --seed apply only to factor comparisons')
    def assigned(name):
        if args.case:
            return name==args.case
        if args.controls:
            return not name.startswith('extra-')
        return int.from_bytes(hashlib.sha256(name.encode()).digest()[:8], 'big') % parts == part
    rows = [json.loads(line) for line in fixtures.FIXTURES.read_text().splitlines()]
    fixtures.verify(rows)
    cpu = idle_core.pick()
    if cpu not in os.sched_getaffinity(0):
        cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as out, tempfile.TemporaryDirectory(prefix='hex-stage2-') as temp:
        frozen = Path(temp)
        for exe in (PRIMALITY, FACTOR):
            shutil.copy2(exe, frozen / exe.name)
        def emit(row):
            out.write(json.dumps(row, separators=(',', ':')) + '\n')
            out.flush()
        sources = ['HexPrimality/PMinusOne.lean', 'HexPrimality/Construction.lean',
                   'HexPrimality/Search.lean', 'HexIntFactor/Factor.lean',
                   'bench/HexPrimality/Bench.lean', 'bench/HexIntFactor/Bench.lean',
                   'bench/HexPrimality/PMinusOneMeasure.lean',
                   'scripts/bench/pminusone_stage2_measure.py',
                   'conformance-fixtures/HexPrimality/pminusone-stage2.jsonl',
                   'lean-toolchain', 'lake-manifest.json']
        budget = json.loads(subprocess.check_output(
            [str(frozen / PRIMALITY.name), 'construction-budget'], text=True))
        metadata = {'type': 'metadata', 'mode': args.mode, 'partition':args.partition, 'case':args.case, 'controls':args.controls, 'seed':args.seed, 'cpu': cpu, 'host': platform.node(),
              'load': os.getloadavg(), 'platform': platform.platform(),
              'source_sha256': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
              'executable_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (PRIMALITY, FACTOR)},
              'policy': 'retain all completed samples; no activity rejection or quiet-host preflight',
              'phase_schedule': 'five fixed trial-major passes',
              'pair_schedule': 'eight adjacent blocks, alternating disabled/enabled and enabled/disabled',
              'timing_provider': 'lean-bench fixed child',
              'ordinary_budget': 'identical rho/ECM and worklist caps; eight base smooth attempts plus at most one counted continuation from spare fuel',
              'construction_budget': budget,
              'stage1_backend': 'existing powMod word-Montgomery dispatch; per-power context construction included in stage1',
              'prepared_stage1_backend': 'identical powers and conversions with one word context prepared per modulus; Nat fallback unchanged',
              'stage2_backend': 'direct Nat multiplication and remainder',
              'working_residue_bound': 252}
        emit(metadata)
        completed_pairs = set()
        if args.resume_from:
            samples=[]
            for source in args.resume_from:
                raw = source.read_bytes()
                data = gzip.decompress(raw) if source.suffix=='.gz' else raw
                prior = [json.loads(line) for line in data.splitlines()]
                assert prior[0]['mode'] == args.mode
                assert prior[0]['source_sha256'] == metadata['source_sha256'], 'resume source mismatch'
                assert prior[0]['executable_sha256'] == metadata['executable_sha256'], 'resume executable mismatch'
                if args.mode=='factor':
                    assert prior[0].get('timing_provider')=='lean-bench fixed child'
                emit({'type':'resume', 'path':str(source),
                      'sha256':hashlib.sha256(data).hexdigest(),
                      'metadata':prior[0]})
                samples.extend({**r,'resumed_from':str(source)} for r in prior
                               if r['type']=='sample' and r.get('exit_code')==0)
            pairs={}
            for row in samples:
                key=(row['block'],row['case'],row['seed'])
                assert row['enabled'] not in pairs.setdefault(key,{}), 'duplicate resumed arm'
                pairs[key][row['enabled']]=row
            for key,pair in pairs.items():
                if set(pair)=={False,True}:
                    completed_pairs.add(key)
            for row in samples:
                if ((row['block'],row['case'],row['seed']) in completed_pairs and assigned(row['case'])
                        and (args.seed is None or row['seed']==args.seed)):
                    emit(row)
        def run(exe, command, info):
            before = time.monotonic()
            completed = subprocess.run([str(frozen / exe.name), *map(str, command)], cwd=ROOT,
                                       capture_output=True, text=True)
            row = {'type': 'sample', **info, 'command': command,
                   'wall_seconds': time.monotonic()-before, 'load': os.getloadavg(),
                   'exit_code': completed.returncode, 'stderr': completed.stderr}
            try:
                outputs=[json.loads(line) for line in completed.stdout.splitlines()]
                timing=next(v for v in outputs if v.get('kind')=='fixed')
                result=next(v['result'] for v in outputs if v.get('type')=='result')
                assert timing['status']=='ok' and timing['inner_repeats']>0
                row.update(lean_bench=timing,result=result,elapsed_ns=timing['total_nanos'],
                           repeats=timing['inner_repeats'])
            except (json.JSONDecodeError,StopIteration,AssertionError):
                row['stdout'] = completed.stdout
            emit(row)
            if completed.returncode or 'lean_bench' not in row:
                raise RuntimeError(row)
            return row
        def primitive(row, bound, phase, trial, trace=True, minimum_ns=1000000, track='miss'):
            return run(PRIMALITY, ['stage2-probe', phase, row['n'], row['x'], row['b1'],
                                 bound, minimum_ns, str(trace).lower()],
                       {'trial': trial, 'family': row.get('family', 'control'),
                        'bits': row['bits'], 'q': row['q'], 'phase': phase,
                        'track': track, 'trace': trace, 'b1': row['b1'], 'b2': bound})
        small = [r for r in rows if r['family'] == 'primitive']
        if args.mode in ('phases','preparation'):
            controls = [{'n': n, 'x': x, 'b1': 5, 'bits': n.bit_length(), 'q': 13,
                         'family': name} for n, x, name in
                        [(1081,216,'factor'),(2047,32,'whole'),(1219,998,'recovery')]]
            for trial in range(5):
                for row in small + controls:
                    bounds = [('control',13)] if row in controls else (
                        [('miss',row['q']-1)] if args.mode=='preparation' else [
                        ('miss',row['q']-1),('endpoint',row['q']),('double',2*row['q'])])
                    for track, bound in bounds:
                        phases = ['preparation','prepared-stage1'] if args.mode=='preparation' else [
                            'setup','enumeration','stage1','prepared','continuation','total']
                        for phase in phases:
                            result = primitive(row,bound,phase,trial,track=track)
                            if phase=='prepared-stage1':
                                assert result['result']['value']==1
                            if phase in ('prepared','continuation','total'):
                                expected = 'noFactor' if track == 'miss' else (
                                    'whole' if row.get('family') == 'whole' else 'factor')
                                assert result['result']['outcome'] == expected, result
                print(f'phase trial {trial} retained', flush=True)
        elif args.mode == 'trace':
            for block in range(8):
                for row in small:
                    pair = []
                    for trace in ([False,True] if block%2 == 0 else [True,False]):
                        pair.append(primitive(row,row['q']-1,'prepared',block,trace=trace,minimum_ns=10000000))
                    for result in pair:
                        for event in result['result']['events']:
                            event.pop('batches', None)
                    assert pair[0]['result'] == pair[1]['result']
                print(f'trace block {block} retained', flush=True)
        elif args.mode == 'endpoint':
            row = {'n': 2**521-1, 'x': 2, 'b1': 524288, 'bits': 521, 'q': 4194304}
            for trial in range(5):
                for phase in ['enumeration','prepared','continuation']:
                    result = primitive(row,4194304,phase,trial,minimum_ns=0,track='cap')
                    if phase != 'enumeration':
                        assert result['result']['outcome'] == 'noFactor'
        elif args.mode == 'factor':
            cases = [(f"extra-{r['bits']}-{r['q']}",r['n'],r['q']) for r in rows
                     if r['family']=='integration']
            cases += [(f'balanced-{bits}',p*r,0) for bits,p,r in [
                (32,64553,66553),(40,1047587,1049599),(48,16776217,16778227),
                (56,268434461,268436507),(64,4294966297,4294968317),
                (72,68719475767,68719477789),(80,1099511626781,1099511628781)]]
            cases += [(f'smooth-{i}',65537*r,0) for i,r in enumerate([
                65521,8400967,2147496017,549755826233,140737488367699,
                36028797018976327,576460752303435851,9223372036854788173])]
            cases += [(f'table-{i}',n,0) for i,n in enumerate([
                5999953,11999921,17999983,23999947,30000013,35999987,41999597,47999209,
                53999863,59999501,66000017,71999951,77999983,84000193,89999939,95999257])]
            for block in range(8):
                for name,n,q in cases:
                    if not assigned(name):
                        continue
                    for seed in ([args.seed] if args.seed is not None else range(5)):
                        if (block,name,seed) in completed_pairs:
                            continue
                        for enabled in ([False,True] if block%2==0 else [True,False]):
                            result = run(FACTOR,['stage2-factor',n,seed,str(enabled).lower()],
                                         {'block':block,'case':name,'n':n,'q':q,
                                          'seed':seed,'enabled':enabled})
                        print(f'factor block {block} {name} seed {seed} retained',flush=True)
        else:
            cases = [('secp256k1',2**256-2**32-977),
                     ('P384',2**384-2**128-2**96+2**32-1),
                     ('Curve448',2**448-2**224-1),('P521',2**521-1)]
            if args.mode in ('parents'):
                import pminusone_stage2_parents as parents
                parent_rows = [json.loads(l) for l in parents.PATH.read_text().splitlines()]
                parents.verify(parent_rows, small)
                cases += [(f"parent-{r['bits']}-{r['q']}",r['n']) for r in parent_rows]
                source = (ROOT/'bench/HexPrimalityBench/Inputs.lean').read_text()
                cases += [(f'smooth-{bits}',int(n)) for bits,n in re.findall(
                    r'`\(primalityInput(\d+)\) => `\(\s*(\d+)\)',source)]
                cases += [(f'table-{n}',n) for n in (2,3,7,23,97,997,65521)]
                # Existing balanced composites exercise rejection, not a certificate success.
                cases += [(f'balanced-{i}',n) for i,n in enumerate(
                    (64553*66553,1047587*1049599,16776217*16778227))]
            for block in range(8):
                for name,n in cases:
                    if not assigned(name):
                        continue
                    if (block,name,0) in completed_pairs:
                        continue
                    for enabled in ([False,True] if block%2==0 else [True,False]):
                        info = {'block':block,'case':name,'n':n,'seed':0,'enabled':enabled,
                                'maxBits':budget['maxBits']}
                        run(PRIMALITY,['stage2-construct',n,0,str(enabled).lower()],info)
                    print(f'construction block {block} {name} retained',flush=True)
        emit({'type':'complete','load':os.getloadavg()})

if __name__ == '__main__':
    main()
