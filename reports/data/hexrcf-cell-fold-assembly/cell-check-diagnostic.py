from pathlib import Path
import json,os,platform,random,subprocess,time
root=Path('/home/kim/.codex/tasks/hex-10358/boolean-worktree');out=Path('/home/kim/.codex/tasks/hex-10358')
target='HexRCF.CellReplay.Algebraic.Check'
trace=root/'.lake/build/lib/lean/HexRCF/CellReplay/Algebraic/Check.trace'
if trace.exists():
 (out/'cell-check-before-trace.json').write_bytes(trace.read_bytes());trace.unlink()
cpu=random.SystemRandom().choice(sorted(os.sched_getaffinity(0)))
record={'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'target':target,'cpu':cpu,'load_before':os.getloadavg(),'machine':platform.uname()._asdict(),'time_start':time.time(),'memory_limit_bytes':34359738368,'swap_limit_bytes':0,'lean_threads':2,'cache_restore':False}
env=dict(os.environ,LAKE_NO_CACHE='true')
with (out/'cell-check-diagnostic-1.log').open('w') as log:
 p=subprocess.run([str(out/'bin/run-bounded'),'/run/current-system/sw/bin/taskset','-c',str(cpu),'/run/current-system/sw/bin/lake','build',target],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
record.update(exit_code=p.returncode,elapsed_seconds=time.time()-record['time_start'],load_after=os.getloadavg())
(out/'cell-check-diagnostic-1.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
raise SystemExit(p.returncode)
