from pathlib import Path
import hashlib,json,os,platform,subprocess,sys,time
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10377-replay-collection')
sys.path.insert(0,str(root))
from scripts.bench.cpu_lease import cpu_lease
state=Path('/home/kim/.local/state/hex/issue-10377-session-progress')
out=state/'final-direct-conformance';out.mkdir(exist_ok=False)
python=str(state/'final-oracle-venv/bin/python')
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert not subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu})
m={'kind':'direct-library-conformance','scientific_samples':0,'revision':revision,'host':platform.node(),'cpu':cpu,'load_before':os.getloadavg(),'runs':[],'state':'running'}
def save(): (out/'metadata.json').write_text(json.dumps(m,indent=2)+'\n')
def run(label,args):
    command=[str(x) for x in args];record={'label':label,'command':command,'state':'running'};m['runs'].append(record);save()
    start=time.monotonic()
    with (out/(label+'.stdout')).open('w') as stdout,(out/(label+'.stderr')).open('w') as stderr:
        result=subprocess.run(command,cwd=root,stdout=stdout,stderr=stderr)
    record.update(state='complete',exit_code=result.returncode,elapsed_seconds=time.monotonic()-start,load_after=os.getloadavg());save()
    print(label,record['exit_code'],record['elapsed_seconds'],flush=True)
    if result.returncode: raise RuntimeError('failed '+label)
try:
    binaries=['hexsigndet_field_checks','hexsigndet_emit_field_signs','hexsigndet_emit_common_fields','hexsigndet_emit_nested_fields','hexsigndet_emit_fixtures','hexsigndet_json_bytes']
    m['binary_sha256']={n:hashlib.sha256((root/'.lake/build/bin'/n).read_bytes()).hexdigest() for n in binaries};save()
    run('field-checks',[root/'.lake/build/bin/hexsigndet_field_checks'])
    for label,name,arguments in [('rational','hexsigndet_emit_fixtures',[]),('scalars','hexsigndet_emit_field_signs',[]),('common','hexsigndet_emit_common_fields',[]),('nested','hexsigndet_emit_nested_fields',['--profile','local'])]:
        run(label,[root/'.lake/build/bin'/name,*arguments])
    for label,script,arguments in [('rational','sign_det_flint.py',[]),('scalars','sign_det_common_fields.py',['--scalars']),('common','sign_det_common_fields.py',[]),('nested','sign_det_nested_z3.py',['--profile','local'])]:
        run(label+'-oracle',[python,root/'scripts/oracle'/script,out/(label+'.stdout'),*arguments,'--failure-dir',out/'failures'])
    run('bytes-oracle',[python,root/'scripts/oracle/sign_det_json_bytes.py','--exe',root/'.lake/build/bin/hexsigndet_json_bytes'])
    run('oracle-adversarial-tests',[python,'-m','unittest','scripts.oracle.test_sign_det_flint','scripts.oracle.test_sign_det_common_fields','scripts.oracle.test_sign_det_nested_z3','scripts.oracle.test_sign_det_json_bytes'])
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==revision
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
    assert m['binary_sha256']=={n:hashlib.sha256((root/'.lake/build/bin'/n).read_bytes()).hexdigest() for n in binaries}
    m['state']='complete'
except BaseException as e:
    m.update(state='failed',error=str(e));raise
finally:
    m['load_after']=os.getloadavg();m['file_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file() and p.name!='metadata.json'};save();lease.close()
