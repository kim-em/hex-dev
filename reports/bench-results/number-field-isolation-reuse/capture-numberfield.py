from pathlib import Path
import hashlib,json,os,platform,shutil,socket,subprocess,sys,time
ROOT=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10577')
AFTER_ROOT=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10577-isolation-proposal')
HERE=Path(__file__).parent/'numberfield-pairs'
sys.path.insert(0,str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
if HERE.exists(): raise SystemExit('Refusing to overwrite retained measurement')
HERE.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record={'host':socket.gethostname(),'platform':platform.platform(),'load_start':os.getloadavg(),'schedule':'Four fixed trial-major blocks; ExactFactorLadder, ExactSelection, then ExactLadder; adjacent Before/After arms alternate AB/BA by block. No sample rejection or unchanged rerun.','scope':'Informational controlled before/after observations of unchanged complete canonical exactification and expected hashes. Prepared fixed operands and separate warmup excluded. No scientific mode admission or portable timing budget.','arms':[],'sources':{}}
exes={}
for arm,root in [('Before',ROOT),('After',AFTER_ROOT)]:
 if subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True):raise SystemExit('Dirty checkout '+arm)
 ex=root/'.lake/build/bin/hexnumberfield_bench'; frozen=HERE/(arm+'-'+sha(ex));shutil.copyfile(ex,frozen);frozen.chmod(0o755);exes[arm]=frozen
 record['sources'][arm]={'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'executable_sha256':sha(frozen),'executable':str(frozen),'files':{}}
 for name in ['lake-manifest.json','lean-toolchain','bench/HexRealAlgebraic/Bench.lean','HexNumberField/Basic.lean','HexNumberField/Convert.lean','HexNumberField/Lazy.lean','HexNumberFieldMathlib/Exact.lean','HexRealAlgebraic/Basic.lean']:
  src=root/name;record['sources'][arm]['files'][name]=sha(src);shutil.copyfile(src,HERE/(arm+'-'+name.replace('/','-')+'.txt'))
assert record['sources']['Before']['files']['bench/HexRealAlgebraic/Bench.lean']==record['sources']['After']['files']['bench/HexRealAlgebraic/Bench.lean']
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});record['cpu']=cpu
save=lambda:(HERE/'metadata.json').write_text(json.dumps(record,indent=2)+'\n')
save()
for block in range(4):
 for case in ['ExactFactorLadder','ExactSelection','ExactLadder']:
  order=['Before','After'] if block%2==0 else ['After','Before']
  for arm in order:
   stem=f'{case}-{block}-{arm}';output=HERE/(stem+'.json');cmd=[str(exes[arm]),'run','Hex.NumberFieldBench.run'+case,'--repeats','1','--min-total-seconds','0.05','--export-file',str(output)]
   start=time.monotonic()
   with (HERE/(stem+'.log')).open('w') as log:
    result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=False)
   record['arms'].append({'block':block,'case':case,'arm':arm,'order':order,'command':cmd,'exit_code':result.returncode,'whole_child_seconds':time.monotonic()-start,'output':output.name})
   save();print(stem,'exit',result.returncode,flush=True)
record['load_end']=os.getloadavg();record['retained_files']={p.name:sha(p) for p in HERE.iterdir() if p.name!='metadata.json'};save()
