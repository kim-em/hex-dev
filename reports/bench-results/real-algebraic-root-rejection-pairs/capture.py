#!/usr/bin/env python3
"""Collect every adjacent before/after root-rejection comparison in a fixed trial-major schedule."""
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
BEFORE_META = json.loads((HERE.parent/'real-algebraic-poly-roots-comparison/metadata.json').read_text())
BEFORE = Path(BEFORE_META['exact_executable'])
FAMILIES = {'Rational': [8], 'Quadratic': [4]}
SOURCES = ['bench/HexRealAlgebraic/Bench.lean', 'HexRealAlgebraic/Basic.lean',
           'HexRealAlgebraic/Roots.lean', 'HexRealAlgebraicMathlib/Basic.lean',
           'HexRealAlgebraicMathlib/Roots.lean', 'HexNumberField/Roots.lean',
           'HexNumberField/Convert.lean']

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def registered(family, degree):
    return f'Hex.RealAlgebraicBench.run{family}Roots{degree}'

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
archive = Path('/home/kim/.local/state/hex/issue-10577-measurements/real-algebraic-root-rejection-pairs')
archive.mkdir(parents=True, exist_ok=True)
if digest(BEFORE) != BEFORE_META['executable_sha256']:
    raise SystemExit('Historical executable checksum mismatch')
exact_exe = archive / ('hexrealalgebraic_bench-' + digest(EXE))
shutil.copyfile(EXE, exact_exe); exact_exe.chmod(0o755)
env = os.environ.copy()
env['HEX_FLINT_BENCH_PYTHON'] = sys.executable
record = dict(source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              cpu=cpu, host=socket.gethostname(), platform=platform.platform(),
              load_start=os.getloadavg(), source_sha256={p:digest(ROOT/p) for p in SOURCES},
              executable_sha256=digest(EXE), exact_executable=str(exact_exe),
              interpreter=sys.executable, library_path=env.get('LD_LIBRARY_PATH',''),
              before_source_commit=BEFORE_META['source_commit'], before_executable=str(BEFORE), before_executable_sha256=digest(BEFORE),
              raw_git_environment='LeanBench reads the current checkout at invocation; this is not the historical executable source identity. The separately frozen source commits and executable hashes identify the arms.',
              families=FAMILIES, coefficient_height='2 for rational coefficients, fixed positive sqrt(2) for quadratic coefficients',
              schedule='Four trial-major blocks, fixed ascending degree ladder; adjacent AB/BA arms alternate per block. Before and after arms alternate AB/BA order. No load rejection or unchanged rerun.',
              boundary='Actual complete RealAlgebraicPoly.roots and ordered polynomial/sign/multiplicity fingerprint on X^8-2 and X^4-sqrt(2). Prepared inputs and separate warmup excluded; root solving, exactification, filtering, sorting and fingerprints included. The same benchmark body and expected fingerprints are used in both frozen executables.',
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
                order=['Before','After'] if block%2==0 else ['After','Before']
                for arm in order:
                    stem=f'{family}-{degree}-{block}-{arm}'
                    output=HERE/(stem+'.json')
                    executable=BEFORE if arm=='Before' else exact_exe
                    command=[str(executable),'run',registered(family,degree),
                             '--repeats','1','--min-total-seconds','0.05','--export-file',str(output)]
                    started=time.monotonic()
                    with (HERE/(stem+'.log')).open('w') as log:
                        done=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,check=False)
                    record['arms'].append(dict(family=family,degree=degree,block=block,order=order,arm=arm,
                        source_commit=BEFORE_META['source_commit'] if arm=='Before' else record['source_commit'],
                        executable_sha256=digest(executable),command=command,exit_code=done.returncode,
                        elapsed_seconds=time.monotonic()-started,output=output.name))
                    save()
                    if output.exists():shutil.copyfile(output,archive/output.name)
                    shutil.copyfile(HERE/(stem+'.log'),archive/(stem+'.log'))
                    print(stem, 'exit',done.returncode,flush=True)

finally:
    record['load_end']=os.getloadavg()
    record['source_unchanged']=all(digest(ROOT/p)==h for p,h in record['source_sha256'].items())
    record['binary_unchanged']=digest(EXE)==record['executable_sha256'] and digest(BEFORE)==record['before_executable_sha256']
    save()
