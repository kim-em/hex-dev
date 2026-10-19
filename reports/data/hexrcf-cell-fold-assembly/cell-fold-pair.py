from pathlib import Path
import hashlib,json,os,random,subprocess,time
root=Path('/home/kim/.codex/tasks/hex-10358/boolean-worktree');out=Path('/home/kim/.codex/tasks/hex-10358')
source=Path('conformance/HexRCF/CellReplay/Algebraic/Check.lean');trace=root/'.lake/build/lib/lean/HexRCF/CellReplay/Algebraic/Check.trace'
first=subprocess.check_output(['git','show','c28de2d4db125e1e42b23084ecaee75b9531300a:'+str(source)],cwd=root)
second=(root/source).read_bytes()
assert first!=second
(out/'cell-fold-pair-A.lean.txt').write_bytes(first);(out/'cell-fold-pair-B.lean.txt').write_bytes(second)
cpu=random.SystemRandom().choice(sorted(os.sched_getaffinity(0)))
record={'implementation_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'base_commit':'c28de2d4db125e1e42b23084ecaee75b9531300a','source':str(source),'arms_sha256':{k:hashlib.sha256(v).hexdigest() for k,v in [('A',first),('B',second)]},'cpu':cpu,'schedule':[['A','B'],['B','A']],'target':'HexRCF.CellReplay.Algebraic.Check','memory_limit_bytes':34359738368,'swap_limit_bytes':0,'lean_threads':2,'samples':[],'scope':'Build-only matched-import fresh single-module proof elaboration and kernel acceptance. Fixed adjacent AB/BA schedule; retain every completed sample. No clean build-rate or general scaling claim.'}
try:
 for trial,order in enumerate(record['schedule']):
  for arm in order:
   (root/source).write_bytes(first if arm=='A' else second)
   trace.unlink(missing_ok=True)
   log=out/f'cell-fold-pair-{trial}-{arm}.log'
   entry={'trial':trial,'arm':arm,'load_before':os.getloadavg(),'time_start':time.time(),'log':str(log),'peak_bytes_observed':0}
   start=time.perf_counter()
   with log.open('w') as stream:
    p=subprocess.Popen([str(out/'bin/run-bounded'),'/run/current-system/sw/bin/env','LAKE_NO_CACHE=true','/run/current-system/sw/bin/taskset','-c',str(cpu),'/run/current-system/sw/bin/lake','build',record['target']],cwd=root,stdout=stream,stderr=subprocess.STDOUT)
    while p.poll() is None:
     cg=Path('/sys/fs/cgroup/user.slice/user-1003.slice/user@1003.service/app.slice/hex-10358-lean-build.service/memory.peak')
     try:entry['peak_bytes_observed']=max(entry['peak_bytes_observed'],int(cg.read_text().strip()))
     except (OSError,ValueError):pass
     time.sleep(0.2)
   entry.update(elapsed_seconds=time.perf_counter()-start,exit_code=p.returncode,load_after=os.getloadavg(),olean_bytes=(root/'.lake/build/lib/lean/HexRCF/CellReplay/Algebraic/Check.olean').stat().st_size)
   record['samples'].append(entry)
   (out/'cell-fold-pair.json').write_text(json.dumps(record,indent=2)+'\n')
   print(json.dumps(entry),flush=True)
   if p.returncode:raise RuntimeError(f'build failed: {log}')
finally:
 (root/source).write_bytes(second)
print('Fixed four-sample AB/BA comparison complete; source restored to B.',flush=True)
