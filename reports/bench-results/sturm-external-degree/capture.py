#!/usr/bin/env python3
"""Collect every adjacent exact-count comparison in a fixed trial-major schedule."""
from pathlib import Path
import hashlib
import json
import os
import platform
import shutil
import socket
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.oracle.sturm_bench import coefficients

EXE = ROOT / '.lake/build/bin/hexsturm_bench'
DEGREES = [4, 8, 16, 32, 64]
SOURCES = ['bench/HexSturm/Bench.lean', 'scripts/oracle/sturm_bench.py',
           'scripts/oracle/test_sturm_bench.py', 'scripts/oracle/real_algebraic_qqbar.py',
           'Hex/BenchOracle/Flint.lean', 'HexSturm/Basic.lean',
           'HexRealRoots/Tarski.lean', 'HexRealRoots/SignedRemainderChain.lean']

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def registered(backend, degree, protocol=False):
    suffix = ('Protocol' if protocol else 'Count') if degree == 8 else ('Protocol' if protocol else '') + str(degree)
    return 'Hex.SturmExternalBench.run' + backend + suffix

if (HERE/'metadata.json').exists():
    raise SystemExit('Refusing to overwrite retained completed or partial measurements')
for source in SOURCES:
    if not (ROOT/source).is_file():
        raise SystemExit(f'Missing source fingerprint input: {source}')
cpu, lease = cpu_lease()
os.sched_setaffinity(0, {cpu})
archive = Path('/home/kim/.local/state/hex/issue-10577-measurements/sturm-external-degree')
archive.mkdir(parents=True, exist_ok=True)
exact_exe = archive / ('hexsturm_bench-' + digest(EXE))
shutil.copyfile(EXE, exact_exe); exact_exe.chmod(0o755)
env = os.environ.copy()
env['HEX_FLINT_BENCH_PYTHON'] = sys.executable
record = dict(source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              cpu=cpu, host=socket.gethostname(), platform=platform.platform(),
              load_start=os.getloadavg(), source_sha256={p:digest(ROOT/p) for p in SOURCES},
              executable_sha256=digest(EXE), exact_executable=str(exact_exe),
              interpreter=sys.executable, library_path=env.get('LD_LIBRARY_PATH',''),
              degrees=DEGREES, max_coefficient_bits={n:max(abs(c).bit_length() for c in coefficients(n)) for n in DEGREES},
              schedule='Four trial-major blocks, fixed ascending degree ladder; adjacent AB/BA arms alternate per block. A protocol control follows each pair. No load rejection or unchanged rerun.',
              boundary='Complete exact root count for T_n on (-2,2), result Option Int n. Inputs/context initialization and one warmup are excluded; native chain/domain checks and external root production/filtering/sign sum/JSON/cleanup are timed. No driver root cache. Backend internal caches may persist within a batch. Degree and coefficient height both grow in this family.',
              classification='Informational elapsed-time comparisons; no fitted model, complexity admission or absolute budget.',arms=[])

def save():
    (HERE/'metadata.json').write_text(json.dumps(record,indent=2)+'\n')
    shutil.copyfile(HERE/'metadata.json',archive/'metadata.json')

for p in SOURCES:
    q=HERE/(p.replace('/','-')+'.txt');shutil.copyfile(ROOT/p,q)
save()
try:
    for block in range(4):
        for degree in DEGREES:
            for comparator in ['Flint','Z3']:
                order=['Native',comparator] if block%2==0 else [comparator,'Native']
                for backend,protocol in [(b,False) for b in order]+[(comparator,True)]:
                    stem=f'{degree}-{comparator}-{block}-{backend}'+('-protocol' if protocol else '')
                    output=HERE/(stem+'.json')
                    command=[str(EXE),'run',registered(backend,degree,protocol),
                             '--repeats','1','--min-total-seconds','0.05','--export-file',str(output)]
                    started=time.monotonic()
                    with (HERE/(stem+'.log')).open('w') as log:
                        done=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,check=False)
                    arm=dict(degree=degree,comparator=comparator,block=block,order=order,backend=backend,
                             protocol=protocol,command=command,exit_code=done.returncode,
                             elapsed_seconds=time.monotonic()-started,output=output.name)
                    record['arms'].append(arm);save()
                    if output.exists():shutil.copyfile(output,archive/output.name)
                    shutil.copyfile(HERE/(stem+'.log'),archive/(stem+'.log'))
                    print(stem, 'exit',done.returncode,flush=True)
finally:
    record['load_end']=os.getloadavg()
    record['source_unchanged']=all(digest(ROOT/p)==h for p,h in record['source_sha256'].items())
    record['binary_unchanged']=digest(EXE)==record['executable_sha256']
    save()
