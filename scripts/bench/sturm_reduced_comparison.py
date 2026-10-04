#!/usr/bin/env python3
"""Retain adjacent AB/BA query arms, peak RSS, and the reduced query's declared ladder.

The paired ladder is a diagnostic comparison, not a complexity admission. Its
kernel samples exclude preparation; peak RSS covers the entire invocation.
The final scientific run uses the registration without setting overrides.
No completed samples are discarded and no automatic reruns are performed.
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

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    digest = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
    original = ROOT / '.lake/build/bin/hexsturm_bench'
    exe = out / ('hexsturm_bench-' + digest(original))
    shutil.copyfile(original, exe)
    exe.chmod(0o755)
    sources = ['HexSturm/Basic.lean', 'HexSturm/Reduced.lean',
               'HexPoly/Euclid/DivGcd.lean', 'bench/HexSturm/Bench.lean',
               'lean-toolchain', 'lake-manifest.json', 'scripts/bench/sturm_reduced_comparison.py']
    sources = [s for s in sources if (ROOT / s).is_file()]
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = dict(cpu=cpu, host=os.uname().nodename,
                    start=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    load_start=os.getloadavg(),
                    source=subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT,text=True).strip(),
                    status=subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True),
                    binary_sha256=digest(exe), sources={s: digest(ROOT/s) for s in sources}, runs=[],
                    boundary='Kernel timings exclude input preparation. Linux wait4 peak RSS is for each whole native invocation, including preparation and child execution.')
    for s in sources:
        shutil.copyfile(ROOT/s, out/(s.replace('/','-')+'.txt'))
    def save():
        (out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    def run(label, command):
        argv = [str(exe), *command, '--export-file', str(out/(label+'.json'))]
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            child = subprocess.Popen(argv,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(child.pid,0)
            child.returncode = os.waitstatus_to_exitcode(status)
        metadata['runs'].append(dict(label=label, command=argv, exit_code=child.returncode,
                                      elapsed_seconds=time.monotonic()-start, peak_rss_kib=usage.ru_maxrss))
        save()
        print(label, 'exit',child.returncode,'RSS KiB',usage.ru_maxrss,flush=True)
    save()
    try:
        for trial in range(4):
            for n in [32768,65536,131072,262144]:
                arms = [('original','runRationalValue'),('reduced','runReducedRational')]
                if trial%2:
                    arms.reverse()
                for arm, name in arms:
                    run(f'trial{trial}-{n}-{arm}', ['run','Hex.SturmBench.'+name,
                        '--param-floor',str(n),'--param-ceiling',str(n),'--param-schedule','doubling',
                        '--outer-trials','1','--target-inner-nanos','100000000'])
        run('reduced-declared-ladder',['run','Hex.SturmBench.runReducedRational'])
    finally:
        metadata.update(load_end=os.getloadavg(),
                        source_unchanged=all(digest(ROOT/s)==h for s,h in metadata['sources'].items()),
                        binary_unchanged=digest(exe)==metadata['binary_sha256'])
        metadata['artifacts']={f.name:digest(f) for f in out.iterdir() if f.is_file() and f.name!='metadata.json'}
        save()
        lease.close()


if __name__=='__main__':
    main()
