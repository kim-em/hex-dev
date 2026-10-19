"""Small adjacent comparisons after the polynomial-power correction, no scaling fit."""
import hashlib, json, os, pathlib, platform, statistics, subprocess, sys, time
root=pathlib.Path(sys.argv[1]).resolve()
out=pathlib.Path(sys.argv[2]).resolve()
sys.path.insert(0,str(root))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_joint import validate as validate_inputs
from scripts.bench.sign_det_joint_timing import validate_hashes,RESULT_KEYS
os.chdir(root)
exe=root/'.lake/build/bin/hexsigndet_bench'
out.mkdir(parents=True,exist_ok=False)
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
if subprocess.check_output(['git','status','--porcelain'],text=True).strip():raise ValueError('source must be clean')
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu})
params=[3,7,15];trials=6
pairs=[('runReduced','runDirect'),('runCheckReduced','runCheckDirect')]
metadata={'revision':revision,'source_sha256':source_hashes(),'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),'harness_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root/'.lake/packages/lean-bench',text=True).strip(),'host':platform.node(),'platform':platform.platform(),'cpu':cpu,'affinity':sorted(os.sched_getaffinity(0)),'load_before':os.getloadavg(),'parameters':params,'trials':trials,'order':'trial-major, parameter-major, adjacent pairs; AB even trials and BA odd trials','cache_mode':'cold; one invocation per child; startup and preparation excluded from per_call_nanos, included in peak RSS','state':'running','runs':[]}
def save():(out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
save();archive_sources(out,metadata);save()
try:
 for n in params:
  for command,label in [('inspect-joint','inputs'),('inspect-joint-timings','callbacks')]:
   result=subprocess.run([str(exe),command,str(n)],capture_output=True,text=True)
   (out/f'{label}-{n}.log').write_text(result.stdout);(out/f'{label}-{n}.stderr.log').write_text(result.stderr)
   if result.returncode:raise ValueError('input inspection failed')
 (out/'inputs.log').write_text(''.join((out/f'inputs-{n}.log').read_text() for n in params))
 (out/'callbacks.log').write_text(''.join((out/f'callbacks-{n}.log').read_text() for n in params))
 validate_inputs(out/'inputs.log',params)
 expected=validate_hashes(out/'callbacks.log',params)
 rows=[]
 with (out/'samples.jsonl').open('w') as output:
  for trial in range(trials):
   for n in params:
    for pair in pairs:
     for name in pair if trial%2==0 else pair[::-1]:
      cmd=[str(exe),'_child','--bench','Hex.SignDetBench.Joint.'+name,'--param',str(n),'--target-nanos','0','--cache-mode','cold']
      start=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
      label=f'{trial}-{n}-{name}'
      (out/(label+'.stdout.log')).write_text(r.stdout);(out/(label+'.stderr.log')).write_text(r.stderr)
      metadata['runs'].append({'label':label,'command':cmd,'exit_code':r.returncode,'wall_seconds':time.monotonic()-start,'load_after':os.getloadavg()});save()
      if r.returncode:raise ValueError('failed callback '+label)
      point=json.loads(r.stdout)
      if point['status']!='ok' or point['inner_repeats']!=1 or point['result_hash']!=hex(expected[n][RESULT_KEYS[name]]):raise ValueError('wrong callback answer '+label)
      row={'trial':trial,'degree':n,'name':name,'point':point};rows.append(row);output.write(json.dumps(row)+'\n');output.flush()
 for k in ['source_sha256','binary_sha256']:
  actual=source_hashes() if k=='source_sha256' else hashlib.sha256(exe.read_bytes()).hexdigest()
  if metadata[k]!=actual:raise ValueError('source or binary changed')
 summary={}
 for left,right in pairs:
  for n in params:
   arms=[[r['point'] for r in rows if r['degree']==n and r['name']==arm] for arm in [left,right]]
   summary[f'{left}/{right}:{n}']={'left_median_ms':statistics.median(p['per_call_nanos'] for p in arms[0])/1e6,'right_median_ms':statistics.median(p['per_call_nanos'] for p in arms[1])/1e6,'right_over_left_pair_geomean':statistics.geometric_mean(arms[1][t]['per_call_nanos']/arms[0][t]['per_call_nanos'] for t in range(trials)),'left_peak_rss_median_MiB':statistics.median(p['peak_rss_kb'] for p in arms[0])/1024,'right_peak_rss_median_MiB':statistics.median(p['peak_rss_kb'] for p in arms[1])/1024}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');metadata['state']='complete';metadata['completed_samples']=len(rows);save();print(json.dumps(summary,indent=2))
except BaseException as e:
 metadata['state']='failed';metadata['error']=repr(e);save();raise
