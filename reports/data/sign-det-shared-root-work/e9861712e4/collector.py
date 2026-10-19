import hashlib, json, pathlib, shutil, subprocess, sys
root=pathlib.Path(sys.argv[1]).resolve(); out=pathlib.Path(sys.argv[2]).resolve(); python=sys.argv[3]
sys.path.insert(0,str(root))
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_compare import archive_sources
if subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True).strip():
    raise ValueError('source must be clean')
exe=root/'.lake/build/bin/hexsigndet_bench'
sources=source_hashes()
for name in ['bench/HexSignDet/SharedRoots.lean','scripts/bench/sign_det_shared_root_work.py','scripts/bench/sign_det_shared_roots.py']:
    sources[name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
metadata={'kind':'untimed-work-inventory','revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'source_sha256':sources,'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),'source_clean':True,'state':'running','runs':[]}
out.mkdir(parents=True,exist_ok=False)
shutil.copyfile(__file__,out/'collector.py');archive_sources(out,metadata)
for label,cmd in [('inputs',[str(exe),'inspect-shared-roots-work']),('oracle',[python,str(root/'scripts/bench/sign_det_shared_root_work.py'),str(out/'inputs.log')])]:
    r=subprocess.run(cmd,cwd=root,capture_output=True,text=True)
    (out/(label+'.log')).write_text(r.stdout);(out/(label+'.stderr.log')).write_text(r.stderr)
    metadata['runs'].append({'label':label,'command':cmd,'exit_code':r.returncode})
    if r.returncode:raise ValueError('diagnostic failed '+label)
old=[json.loads(s) for s in (root/'reports/data/sign-det-shared-roots/5b46a2db3b/inputs.log').read_text().splitlines()]
new=[json.loads(s) for s in (out/'inputs.log').read_text().splitlines()]
for a,b in zip(old,new,strict=True):
    for key in ['extraFactors','left','right','factor','commonHead','resultHash']:
        if a[key]!=b[key]:raise ValueError('baseline callback binding changed '+key)
    if a['jointMomentCounts']!=b['tableMomentCounts'][7:]:raise ValueError('joint counts changed')
if any(hashlib.sha256((root/p).read_bytes()).hexdigest()!=v for p,v in sources.items()) or hashlib.sha256(exe.read_bytes()).hexdigest()!=metadata['binary_sha256']:
    raise ValueError('source or binary changed')
metadata.update(state='complete',cases=len(new),baseline_bindings='passed',timing_claim='none')
(out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()}
(out/'archive.json').write_text(json.dumps({'algorithm':'sha256','files':files},indent=2)+'\n')
print('3/3 native inventories and independent root oracles pass; baseline polynomial/digest/joint-count bindings preserved; no timing observations collected')
