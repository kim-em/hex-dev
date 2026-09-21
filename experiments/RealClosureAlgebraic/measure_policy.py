#!/usr/bin/env python3
"""Fixed AB/BA orchestration only; timing and repetition belong to lean-bench."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / 'results' / 'policy' / 'timing'
OUT.mkdir(exist_ok=False)
cpus = sorted(os.sched_getaffinity(0))
start = os.getpid() % len(cpus)
lease = None
for cpu in cpus[start:] + cpus[:start]:
    candidate = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
    try:
        fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
        lease = candidate
        break
    except BlockingIOError:
        candidate.close()
if lease is None:
    raise RuntimeError('all measurement CPU leases held')
os.sched_setaffinity(0,{cpu})

def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()

files = sorted(HERE.glob('*.lean')) + [HERE/'lakefile.toml',HERE/'POLICY-PROTOCOL.md',HERE/'measure_policy.py']
meta = dict(cpu=cpu,host=platform.uname()._asdict(),load_start=os.getloadavg(),
            base=git('rev-parse','HEAD'),
            lean_bench=git('-C','.lake/packages/lean-bench','rev-parse','HEAD'),
            toolchain=(HERE/'lean-toolchain').read_text().strip(),
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
            schedule='10 cases x 3 adjacent policy pairs x 6 AB/BA blocks; 1 repeat, 50ms floor')
(OUT/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
exe = HERE/'.lake/build/bin/policyBench'
with (OUT/'samples.jsonl').open('w') as samples, (OUT/'output.log').open('w') as log:
    for case in range(10):
        for pair in range(3):
            for block in range(6):
                arms = [f'policy_{pair}_{case}',f'policy_{pair+1}_{case}']
                if block%2: arms.reverse()
                export = OUT/'current.json'
                cmd = [str(exe),'compare',*arms,'--export-file',str(export)]
                result=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
                log.write(f'case={case} pair={pair} block={block}\n'+result.stdout)
                log.flush()
                if export.exists():
                    data=json.loads(export.read_text())
                    samples.write(json.dumps(dict(case=case,pair=pair,block=block,report=data))+'\n')
                    samples.flush()
                    export.unlink()
                if result.returncode:
                    raise RuntimeError('comparison failed; every completed sample and log retained')
        print(f'completed case {case}',flush=True)
meta['load_end']=os.getloadavg()
(OUT/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
