from pathlib import Path
import sys,os,json,hashlib,subprocess,datetime
root=Path.cwd();sys.path.insert(0,str(root))
from scripts.bench.det_symbolic_sweep import cpu_lease
out=root/'reports/bench-results/sturm-replay-deferred-pairs';out.mkdir()
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu})
binaries={'A':Path('/tmp/hexsturm-replay-cap1800'),'B':root/'.lake/build/bin/hexsturm_bench'}
meta={'cpu':cpu,'host':os.uname().nodename,'start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'load_start':os.getloadavg(),'git_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'binary_sha256':{k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in binaries.items()},'protocol':'four adjacent AB/BA blocks, degree 1024, warm 100ms target, all children retained','commands':[]}
(out/'capture.py').write_bytes(Path(__file__).read_bytes())
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
try:
 for block in range(4):
  for arm in ('AB' if block%2==0 else 'BA'):
   cmd=[str(binaries[arm]),'_child','--bench','Hex.SturmBench.runReplay','--param','1024','--target-nanos','100000000','--cache-mode','warm']
   print(block,arm,flush=True)
   with (out/f'{block}-{arm}.jsonl').open('w') as f:
    r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
   meta['commands'].append({'block':block,'arm':arm,'argv':cmd,'exit_code':r.returncode})
   (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
   r.check_returncode()
finally:
 meta.update(end=datetime.datetime.now(datetime.timezone.utc).isoformat(),load_end=os.getloadavg())
 (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
 lease.close()
