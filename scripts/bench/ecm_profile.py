#!/usr/bin/env python3
"""Retain whole-module profiles proving interpreter/native producer dispatch.

These profiles establish execution-path attribution, not a LeanBench timed-region
claim. Full-module wall times include imports, construction and output formatting.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.ecm_cost import MODULE

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--interpreted', type=Path, required=True)
p.add_argument('--native', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--module', default=MODULE)
a = p.parse_args()
if a.output.exists(): p.error('output exists')
a.output.mkdir(parents=True)
module_source = Path('bench') / (a.module.replace('.', '/') + '.lean')
record = dict(cpu=pick(), samples=[], scope='whole fresh module, including import and rendering')
for arm,path in [('interpreted',a.interpreted.resolve()),('native',a.native.resolve())]:
    source = (path/module_source).read_text() + '''\nopen Lean Elab in
run_cmd do
  let maps ← IO.FS.readFile "/proc/self/maps"
  for line in maps.splitOn "\\n" do
    if (line.splitOn "Hex_Hex").length > 1 then IO.println s!"LOADED {line}"
'''
    module = a.module.replace('EcmCost','EcmProfile')
    profile = path/module_source.with_name('EcmProfile.lean')
    previous = profile.read_bytes() if profile.exists() else None
    try:
        profile.write_text(source)
        artifact = path/'.lake/build/lib/lean'/Path(module.replace('.','/')+'.olean')
        artifact.unlink(missing_ok=True)
        data = Path('/tmp')/f'ecm-10374-{arm}.perf'
        command = ['perf','record','-F','99','-g','--call-graph','dwarf','-o',str(data),
                   '--','taskset','-c',str(record['cpu']),'lake','build',module]
        env=dict(os.environ,ECM_SUBJECT=str(2**256-2**32-977),ECM_DISPATCH='expression',LEAN_NUM_THREADS='1')
        r=subprocess.run(command,cwd=path,env=env,text=True,capture_output=True)
        row=dict(arm=arm,command=command,source=source,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr)
        record['samples'].append(row)
        (a.output/'record.json').write_text(json.dumps(record,indent=2)+'\n')
        if data.exists():
            report=subprocess.run(['perf','report','--stdio','--no-children','-g','none','-i',str(data)],text=True,capture_output=True)
            (a.output/f'{arm}.txt').write_text(report.stdout+report.stderr)
        libs = list((path/'.lake/build/lib/lean').glob('Hex_Hex*.so'))
        row['artifacts']={str(f.relative_to(path)):dict(bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in libs}
        (a.output/'record.json').write_text(json.dumps(record,indent=2)+'\n')
    finally:
        if previous is None:
            profile.unlink(missing_ok=True)
        else:
            profile.write_bytes(previous)
