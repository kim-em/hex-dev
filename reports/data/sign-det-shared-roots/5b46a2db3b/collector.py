"""Bounded fixed shared-root observations; six trial-major rounds, no fitted model."""
import hashlib,json,os,pathlib,platform,statistics,subprocess,sys,time
root=pathlib.Path(sys.argv[1]).resolve();out=pathlib.Path(sys.argv[2]).resolve();python=sys.argv[3]
sys.path.insert(0,str(root));os.chdir(root)
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_compare import archive_sources
if subprocess.check_output(['git','status','--porcelain'],text=True).strip():raise ValueError('source must be clean')
out.mkdir(parents=True,exist_ok=False);exe=root/'.lake/build/bin/hexsigndet_bench'
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu})
sources=source_hashes();sources['scripts/bench/sign_det_shared_roots.py']=hashlib.sha256((root/'scripts/bench/sign_det_shared_roots.py').read_bytes()).hexdigest()
metadata={'revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_sha256':sources,'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),'harness_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root/'.lake/packages/lean-bench',text=True).strip(),'host':platform.node(),'platform':platform.platform(),'cpu':cpu,'affinity':sorted(os.sched_getaffinity(0)),'load_before':os.getloadavg(),'schedule':'six trial-major rounds; cases one,two,three in each round','target_inner_nanos':100000000,'state':'running','runs':[]}
def save():(out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
save();archive_sources(out,metadata);save()
try:
 r=subprocess.run([str(exe),'inspect-shared-roots'],capture_output=True,text=True)
 (out/'inputs.log').write_text(r.stdout);(out/'inputs.stderr.log').write_text(r.stderr)
 if r.returncode:raise ValueError('inspection failed')
 r=subprocess.run([python,str(root/'scripts/bench/sign_det_shared_roots.py'),str(out/'inputs.log')],capture_output=True,text=True)
 (out/'oracle.log').write_text(r.stdout);(out/'oracle.stderr.log').write_text(r.stderr)
 if r.returncode:raise ValueError('independent input oracle failed')
 expected={r['extraFactors']:r['resultHash'] for r in [json.loads(x) for x in (out/'inputs.log').read_text().splitlines()]}
 rows=[]
 with (out/'samples.jsonl').open('w') as f:
  for trial in range(6):
   for n,name in [(1,'runOne'),(2,'runTwo'),(3,'runThree')]:
    label=f'{trial}-{n}';cmd=[str(exe),'_child','--bench','Hex.SignDetBench.SharedRoots.'+name,'--fixed','--repeat-index',str(trial),'--min-total-nanos','100000000']
    start=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
    (out/(label+'.stdout.log')).write_text(r.stdout);(out/(label+'.stderr.log')).write_text(r.stderr)
    metadata['runs'].append({'label':label,'command':cmd,'exit_code':r.returncode,'wall_seconds':time.monotonic()-start,'load_after':os.getloadavg()});save()
    if r.returncode:raise ValueError('callback failed '+label)
    point=json.loads(r.stdout)
    if point['status']!='ok' or point['repeat_index']!=trial or point['result_hash']!=hex(expected[n]) or point['inner_repeats']<=0 or point['total_nanos']<=0 or point['peak_rss_kb']<=0:raise ValueError('invalid point '+label)
    rows.append({'case':n,'name':name,'point':point});f.write(json.dumps(rows[-1])+'\n');f.flush()
 for name,digest in sources.items():
  if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:raise ValueError('source changed '+name)
 if hashlib.sha256(exe.read_bytes()).hexdigest()!=metadata['binary_sha256']:raise ValueError('binary changed')
 summary={}
 for n in [1,2,3]:
  points=[r['point'] for r in rows if r['case']==n]
  values=[p['total_nanos']/p['inner_repeats']/1e6 for p in points]
  summary[str(n)]={'degree':n+2,'median_ms':statistics.median(values),'min_ms':min(values),'max_ms':max(values),'median_peak_rss_MiB':statistics.median(p['peak_rss_kb'] for p in points)/1024,'samples':len(points)}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');metadata['state']='complete';metadata['completed_samples']=len(rows);save();print(json.dumps(summary,indent=2))
except BaseException as e:
 metadata['state']='failed';metadata['error']=repr(e);save();raise
