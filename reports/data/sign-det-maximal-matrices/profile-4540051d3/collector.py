from pathlib import Path
import hashlib,json,os,platform,shutil,subprocess,sys,time
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10377-maximal-timing')
sys.path.insert(0,str(root))
from scripts.bench.structural_tactic_sweep import acquire_cpu
from scripts.bench.sign_det_maximal_matrix import harness_binding
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_compare import archive_sources
out=Path('/home/kim/.local/state/hex/issue-10377-profiles/maximal-solve-4540051d3')
out.mkdir(exist_ok=False)
exe=root/'.lake/build/bin/hexsigndet_bench'
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert not subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
assert exe.resolve().is_relative_to(root)
cpu,lease=acquire_cpu()
os.sched_setaffinity(0,{cpu})
meta={'schema':'hex-sign-det-maximal-solve-profile-v1','revision':revision,'cpu':cpu,
 'host':platform.node(),'load_before':os.getloadavg(),'source_sha256':source_hashes(),
 'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),'executable':str(exe.resolve()),
 'collector_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'harness_binding':harness_binding(),'scope':'one cold size-243 actual solve; attribution only, no scientific timing verdict','state':'running'}
(out/'collector.py').write_bytes(Path(__file__).read_bytes())
shutil.copyfile(exe,out/'archived-debuggee')
command=[str(exe),'profile','Hex.SignDetBench.MaximalMatrix.runSolve','--param','5',
 '--cache-mode','cold','--profiler',f'perf record --clockid mono -e cycles:u -F 199 --call-graph dwarf -o {out}/perf.data --']
meta['command']=command
meta['perf_version']=subprocess.check_output(['perf','--version'],text=True).strip()
env=dict(os.environ,LEAN_BENCH_TIMED_REGIONS_SIDECAR=str(out/'regions-%p.jsonl'))
meta['environment']={'LEAN_BENCH_TIMED_REGIONS_SIDECAR':env['LEAN_BENCH_TIMED_REGIONS_SIDECAR']}
def save(): (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
try:
 archive_sources(out,meta)
 save()
 mono0=time.monotonic_ns();wall=time.time_ns();mono1=time.monotonic_ns()
 (out/'spawn-anchor.json').write_text(json.dumps({'wall_ns_at_spawn':wall,'mono_ns_at_spawn':(mono0+mono1)//2,
  'clock_bracket_ns':mono1-mono0,'scope':'parent clock pair immediately before launching the profiling command'},indent=2)+'\n')
 with (out/'profile.log').open('w') as log:
  run=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 meta['exit_code']=run.returncode
 run.check_returncode()
 rows=[json.loads(line) for line in (out/'profile.log').read_text().splitlines() if line.startswith('{')]
 assert len(rows)==1
 row=rows[0]
 expected=json.loads((root/'reports/data/sign-det-maximal-matrices/a7c9b34fb/runSolve.json').read_text())['results'][0]['points'][-1]['result_hash']
 assert row['status']=='ok' and row['result_hash']==expected and row['profile_kernel'] is True
 assert row['inner_repeats']==1 and row['param']==5
 assert row['env']['git_commit']==revision and row['env']['git_dirty'] is False
 sidecars=list(out.glob('regions-*.jsonl'))
 regions=[json.loads(line) for f in sidecars for line in f.read_text().splitlines()
  if json.loads(line).get('kind')=='region' and json.loads(line).get('label')=='kernel']
 assert len(regions)==1
 meta['profile_row']=row;meta['operation_region']=regions[0]
 for name,fields in [('perf-samples.txt','pid,tid,time,event'),('perf-script.txt','pid,tid,time,ip,sym,dso')]:
  args=['perf','script','--ns','--no-demangle','-i',str(out/'perf.data'),'-F',fields]
  with (out/name).open('w') as target: subprocess.run(args,stdout=target,check=True)
 meta['state']='captured'
except BaseException as e:
 meta.update(state='failed',error=str(e),exception=type(e).__name__)
 raise
finally:
 meta['source_sha256_after']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in meta['source_sha256']}
 meta['binary_sha256_after']=hashlib.sha256(exe.read_bytes()).hexdigest()
 meta['revision_after']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
 meta['status_after']=subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
 meta['harness_binding_after']=harness_binding()
 meta['load_after']=os.getloadavg()
 meta['provenance_unchanged']=(meta['source_sha256_after']==meta['source_sha256'] and
  meta['binary_sha256_after']==meta['binary_sha256'] and meta['revision_after']==revision and
  not meta['status_after'] and meta['harness_binding_after']==meta['harness_binding'])
 save();lease.close()
 assert meta['provenance_unchanged']
print(out)
