"""Named adjacent-arm attribution for a meaningful compiler-annotation change."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
ROOT=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10575-review');out=Path('/home/kim/.codex/tasks/hex-10575/orderedfn-inline-probe-rerun');sys.path.insert(0,str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
p=out/'decision.json';decision=json.loads(p.read_text());decision['baseline_rebuild']='Unmodified integrated205cd source rebuild215Lake jobs reproduces6479b2306cb778b7f34ec681020322212607e518577ecae9912f06e0a1ab0fed exactly.'
decision['probe_rule']='Use each arms median of three native per-call observations at height2048, third1024 and approximation12288. Full source-change comparison is justified only if both inlined scan cases improve by more than the preexisting10% default; approximation is an unresolved required path, not a claimed unaffected or passing null control. The probe itself is not Phase6 acceptance.'
p.write_text(json.dumps(decision,indent=2)+'\n')
source=Path('/home/kim/.codex/tasks/hex-10575/orderedfn-api-regression/sources.json');sources=json.loads(source.read_text());arms={'baseline':Path(sources['candidate']['binary']),'inline':out/'hexorderedfn_bench-inline'};hashes={a:hashlib.sha256(x.read_bytes()).hexdigest() for a,x in arms.items()}
assert hashes['baseline']==sources['candidate']['binary_sha256'];assert hashes['inline']==decision['native_binary_sha256']
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});context=dict(cpu=cpu,load_before=os.getloadavg(),binaries=hashes,source_commit=decision['source_commit'],started_unix=time.time(),cases=[('height',2048),('third',1024),('approximation',12288)],trials=3,order='trial-major; adjacent AB/BA; AB on even trials, BA on odd trials')
try:
 with (out/'probe-observations.jsonl').open('x') as f:
  for trial in range(3):
   for name,param in context['cases']:
    for arm in (['baseline','inline'] if trial%2==0 else ['inline','baseline']):
     assert hashlib.sha256(arms[arm].read_bytes()).hexdigest()==hashes[arm]
     cmd=[str(arms[arm]),'_child','--bench','Hex.OrderedFnBench.'+name,'--param',str(param),'--target-nanos','1000000000'];row=dict(trial=trial,name=name,param=param,arm=arm,command=cmd,load_before=os.getloadavg());stem=out/f'probe-{trial}-{name}-{arm}'
     try:
      with stem.with_suffix('.stdout').open('w') as so,stem.with_suffix('.stderr').open('w') as se:r=subprocess.run(cmd,stdout=so,stderr=se,timeout=180)
      row.update(returncode=r.returncode,observation=json.loads(stem.with_suffix('.stdout').read_text()))
     except Exception as e:row['error']=str(e)
     row['load_after']=os.getloadavg();f.write(json.dumps(row)+'\n');f.flush()
   print('trial '+str(trial)+' finished',flush=True)
finally:
 context.update(finished_unix=time.time(),load_after=os.getloadavg());(out/'probe-context.json').write_text(json.dumps(context,indent=2)+'\n');lease.close()
