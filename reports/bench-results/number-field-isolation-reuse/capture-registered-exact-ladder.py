from pathlib import Path
import hashlib,json,os,subprocess,sys,time
ROOT=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10577');BASE=Path(__file__).parent;HERE=BASE/'registered-exact-ladder-pairs'
sys.path.insert(0,str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
if HERE.exists():raise SystemExit('Refusing to overwrite a retained capture')
HERE.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=json.loads((BASE/'numberfield-pairs/metadata.json').read_text());sources=parent['sources'];exes={a:Path(sources[a]['executable']) for a in ['Before','After']}
for a,p in exes.items():assert sha(p)==sources[a]['executable_sha256']
record={'sources':sources,'compiled_source_from':'Frozen executables and source metadata retained by numberfield-pairs. Exporter git metadata identifies the current collector working directory, not the compiled source.','registered_min_total_seconds':0.02,'schedule':'Four fixed trial-major blocks; adjacent Before/After arms alternate AB/BA. No unchanged rerun, load rejection or cap change.','collector_correction':'Retain both earlier collector configurations (0.05 and 0.001 floors); neither is the registered floor. This capture uses the actual 0.02-second registration. No phase admission is inferred from earlier captures.','cpu':None,'load_start':os.getloadavg(),'arms':[]}
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});record['cpu']=cpu
save=lambda:(HERE/'metadata.json').write_text(json.dumps(record,indent=2)+'\n');save()
for block in range(4):
 order=['Before','After'] if block%2==0 else ['After','Before']
 for arm in order:
  stem=f'ExactLadder-{block}-{arm}';output=HERE/(stem+'.json');cmd=[str(exes[arm]),'run','Hex.NumberFieldBench.runExactLadder','--repeats','1','--min-total-seconds','0.02','--export-file',str(output)]
  start=time.monotonic()
  with (HERE/(stem+'.log')).open('w') as log:done=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
  record['arms'].append({'case':'ExactLadder','block':block,'arm':arm,'order':order,'command':cmd,'exit_code':done.returncode,'whole_child_seconds':time.monotonic()-start,'output':output.name});save();print(stem,done.returncode,flush=True)
record['load_end']=os.getloadavg();record['retained_files']={p.name:sha(p) for p in HERE.iterdir() if p.name!='metadata.json'};save()
