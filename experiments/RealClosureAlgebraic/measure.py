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
OUT = HERE / 'results' / 'timing'
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

files = sorted(HERE.glob('*.lean')) + [HERE/'lakefile.toml',HERE/'PROTOCOL.md',HERE/'measure.py']
meta = dict(cpu=cpu,host=platform.uname()._asdict(),load_start=os.getloadavg(),
            base=git('rev-parse','HEAD'),
            lean_bench=git('-C','.lake/packages/lean-bench','rev-parse','HEAD'),
            toolchain=(HERE/'lean-toolchain').read_text().strip(),
            hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
            schedule='case-major: 12 cases; 6 adjacent AB/BA blocks; 1 repeat, 50ms floor')
(OUT/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
exe = HERE/'.lake/build/bin/algebraicBench'
for case in range(12):
    for block in range(6):
        arms = [f'each{case}',f'batch{case}']
        if block%2: arms.reverse()
        stem = OUT/f'case{case:02}-block{block}'
        cmd = [str(exe),'compare',*arms,'--export-file',str(stem.with_suffix('.json'))]
        with stem.with_suffix('.log').open('w') as log:
            result=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f'{stem.name} failed; retained log and every previous sample')
    print(f'completed case {case}',flush=True)
meta['load_end']=os.getloadavg()
(OUT/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
