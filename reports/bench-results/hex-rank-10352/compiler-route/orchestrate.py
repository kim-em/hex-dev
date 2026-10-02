import json, os, subprocess, hashlib, sys
from pathlib import Path
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10352')
sys.path.insert(0,str(root))
from scripts.bench.idle_core import pick
out=Path('/tmp/hexrank-route-results'); out.mkdir(exist_ok=True)
cpu=pick(); os.sched_setaffinity(0,{cpu})
roots={'before':root,'after':Path('/tmp/hexrank-route-10352')}
config={'cpu':cpu,'load':os.getloadavg(),'blocks':6,'case':'Hex.RankBench.runMvCert12','order':[],'roots':{k:str(v) for k,v in roots.items()},'binaries':{k:hashlib.sha256((v/'.lake/build/bin/hexrank_bench').read_bytes()).hexdigest() for k,v in roots.items()}}
for b in range(6):
 for arm in (['before','after'] if b%2==0 else ['after','before']):
  config['order'].append([b,arm])
(out/'config.json').write_text(json.dumps(config,indent=2)+'\n')
(out/'change.patch').write_bytes(subprocess.check_output(['git','diff'],cwd=roots['after']))
for block,arm in config['order']:
 base=out/f'{block}-{arm}'
 cmd=[str(roots[arm]/'.lake/build/bin/hexrank_bench'),'run',config['case'],'--repeats','1','--export-file',str(base.with_suffix('.json'))]
 with base.with_suffix('.log').open('w') as f:
  r=subprocess.run(cmd,cwd=roots[arm],stdout=f,stderr=subprocess.STDOUT)
 print(block,arm,r.returncode,flush=True)
 if r.returncode: raise SystemExit(r.returncode)
