#!/usr/bin/env python3
"""Collect exact scalar operations on fixed size ladders in adjacent AB/BA arms.

Input preparation and warmup are excluded from kernel times. External arms
include JSON, result guards and cleanup; their framing controls are separate.
All completed samples, failures and inconclusive outputs are retained. No
model fitting, load filtering, automatic reruns or quiet-host checks are used.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
FAMILIES={'Add':[2,4,8],'Sqrt':[2,4,8],'Compare':[4,16,64,256],
          'Floor':[4,16,64,256],'Ceil':[4,16,64,256],'Rational':[16,64,256,1024]}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--operations',nargs='+',choices=list(FAMILIES),default=list(FAMILIES))
    p.add_argument('--native-only',action='store_true',help='Refresh selected native observations without rerunning external comparisons')
    args=p.parse_args();families={name:FAMILIES[name] for name in args.operations};out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
    original=ROOT/'.lake/build/bin/hexrealalgebraic_bench'
    exe=out/('hexrealalgebraic_bench-'+sha(original));shutil.copyfile(original,exe);exe.chmod(0o755)
    sources=['bench/HexRealAlgebraic/Bench.lean','scripts/oracle/real_algebraic_scaling_bench.py',
             'scripts/oracle/test_real_algebraic_scaling_bench.py','scripts/oracle/real_algebraic_qqbar.py',
             'scripts/bench/real_algebraic_scaling_comparison.py','Hex/BenchOracle/Flint.lean',
             'HexRealAlgebraic/Basic.lean','HexRealAlgebraic/Order.lean','HexRealAlgebraic/Roots.lean','HexNumberField/Lazy.lean','HexNumberField/Roots.lean',
             'HexNumberField/Basic.lean','HexNumberField/Convert.lean','HexArith/Nat/Sqrt.lean',
             'lean-toolchain','lake-manifest.json']
    cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu})
    meta=dict(source=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              status=subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True),
              start=datetime.datetime.now(datetime.timezone.utc).isoformat(),host=os.uname().nodename,
              cpu=cpu,load_start=os.getloadavg(),binary_sha256=sha(exe),families=families,native_only=args.native_only,
              sources={s:sha(ROOT/s) for s in sources},arms=[],
              boundary='Prepared operands, no expected algebraic root; native arithmetic checks the complete minimal-polynomial/sign identity. '+('Native-only refresh: four fixed trial-major observations per selected rung; no external arms or paired ratio. ' if args.native_only else 'External arithmetic checks exact annihilation/sign; JSON transport and temporary cleanup are included, with separate protocol controls. Four trial-major adjacent AB/BA blocks per comparator/rung. ')+'One fixed batch per arm, minimum batch 50 ms. No fitted model or admission claim.')
    for s in sources:shutil.copyfile(ROOT/s,out/(s.replace('/','-')+'.txt'))
    env=os.environ.copy();env['HEX_FLINT_BENCH_PYTHON']=sys.executable
    def save():(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
    save()
    try:
        for trial in range(4):
            for operation,sizes in families.items():
                for size in sizes:
                    for backend in (['NativeOnly'] if args.native_only else ['Flint'] if operation in ['Floor','Ceil'] else ['Flint','Z3']):
                        arms=[('Native',False)] if args.native_only else [('Native',False),(backend,False)]
                        if trial%2:arms.reverse()
                        if not args.native_only:arms.append((backend,True))
                        for arm,control in arms:
                            label=f'{operation}-{size}-{backend}-{trial}-{arm}'+('-protocol' if control else '')
                            function='Hex.RealAlgebraicScaling.run'+('' if arm=='Native' else arm)+operation+str(size)+('Protocol' if control else '')
                            cmd=[str(exe),'run',function,'--repeats','1','--min-total-seconds','0.05','--export-file',str(out/(label+'.json'))]
                            start=time.monotonic()
                            with (out/(label+'.log')).open('w') as log:
                                done=subprocess.run(cmd,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,check=False)
                            meta['arms'].append(dict(operation=operation,size=size,comparator=backend,trial=trial,
                                                     arm=arm,control=control,command=cmd,output=label+'.json',
                                                     exit_code=done.returncode,elapsed_seconds=time.monotonic()-start))
                            save();print(label,'exit',done.returncode,flush=True)
    finally:
        meta.update(load_end=os.getloadavg(),source_unchanged=all(sha(ROOT/s)==h for s,h in meta['sources'].items()),
                    binary_unchanged=sha(exe)==meta['binary_sha256'])
        meta['artifacts']={f.name:sha(f) for f in out.iterdir() if f.is_file() and f.name!='metadata.json'}
        save();lease.close()


if __name__=='__main__':main()
