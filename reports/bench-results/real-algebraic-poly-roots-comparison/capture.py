#!/usr/bin/env python3
"""Collect every adjacent polynomial-root comparison in a fixed trial-major schedule."""
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

EXE = ROOT / '.lake/build/bin/hexrealalgebraic_bench'
FAMILIES = {'Rational': [2, 4, 8], 'Quadratic': [1, 2, 4]}
SOURCES = ['bench/HexRealAlgebraic/Bench.lean',
           'scripts/oracle/real_algebraic_roots_bench.py',
           'scripts/oracle/test_real_algebraic_roots_bench.py',
           'scripts/oracle/real_algebraic_qqbar.py', 'Hex/BenchOracle/Flint.lean',
           'HexRealAlgebraic/Roots.lean', 'HexRealAlgebraic/Order.lean',
           'HexNumberField/Roots.lean', 'HexNumberField/Convert.lean']

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def registered(backend, family, degree, protocol=False):
    prefix = '' if backend == 'Native' else backend
    return f'Hex.RealAlgebraicBench.run{prefix}{family}Roots{degree}' + ('Protocol' if protocol else '')

if (HERE/'metadata.json').exists():
    raise SystemExit('Refusing to overwrite retained completed or partial measurements')
status = subprocess.check_output(['git','status','--porcelain'], cwd=ROOT, text=True)
if status:
    raise SystemExit('Measurement requires a clean source checkout before creating output records')
for source in SOURCES:
    if not (ROOT/source).is_file():
        raise SystemExit(f'Missing source fingerprint input: {source}')
cpu, lease = cpu_lease()
os.sched_setaffinity(0, {cpu})
archive = Path('/home/kim/.local/state/hex/issue-10577-measurements/real-algebraic-poly-roots-comparison')
archive.mkdir(parents=True, exist_ok=True)
exact_exe = archive / ('hexrealalgebraic_bench-' + digest(EXE))
shutil.copyfile(EXE, exact_exe); exact_exe.chmod(0o755)
env = os.environ.copy()
env['HEX_FLINT_BENCH_PYTHON'] = sys.executable
record = dict(source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              cpu=cpu, host=socket.gethostname(), platform=platform.platform(),
              load_start=os.getloadavg(), source_sha256={p:digest(ROOT/p) for p in SOURCES},
              executable_sha256=digest(EXE), exact_executable=str(exact_exe),
              interpreter=sys.executable, library_path=env.get('LD_LIBRARY_PATH',''),
              families=FAMILIES, coefficient_height='2 for rational coefficients, fixed positive sqrt(2) for quadratic coefficients',
              schedule='Four trial-major blocks, fixed ascending degree ladder; adjacent AB/BA arms alternate per block. A protocol control follows each pair. No load rejection or unchanged rerun.',
              boundary='Actual RealAlgebraicPoly.roots on X^n-2 or X^n-sqrt(2). Complete increasing minimal-polynomial/sign/multiplicity fingerprint. External roots checked by exact annihilation; minimal polynomial inferred by Eisenstein on these fixtures, not extracted from backend representation. Inputs/context initialization and one warmup excluded; native solving/exactification/sorting and external solving/sorting/annihilation/JSON/cleanup timed. No driver root cache. Backend internal caches may persist within a batch. Quadratic degree one returns one root, all other rungs return two.',
              classification='Informational elapsed-time comparisons; no fitted model, complexity admission or absolute budget.',arms=[])

def save():
    (HERE/'metadata.json').write_text(json.dumps(record,indent=2)+'\n')
    shutil.copyfile(HERE/'metadata.json',archive/'metadata.json')

for p in SOURCES:
    q=HERE/(p.replace('/','-')+'.txt');shutil.copyfile(ROOT/p,q)
save()
try:
    for block in range(4):
        for family, degrees in FAMILIES.items():
            for degree in degrees:
                for comparator in ['Flint','Z3']:
                    order=['Native',comparator] if block%2==0 else [comparator,'Native']
                    for backend,protocol in [(b,False) for b in order]+[(comparator,True)]:
                        stem=f'{family}-{degree}-{comparator}-{block}-{backend}'+('-protocol' if protocol else '')
                        output=HERE/(stem+'.json')
                        command=[str(EXE),'run',registered(backend,family,degree,protocol),
                                 '--repeats','1','--min-total-seconds','0.05','--export-file',str(output)]
                        started=time.monotonic()
                        with (HERE/(stem+'.log')).open('w') as log:
                            done=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,check=False)
                        arm=dict(family=family,degree=degree,comparator=comparator,block=block,order=order,backend=backend,
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
