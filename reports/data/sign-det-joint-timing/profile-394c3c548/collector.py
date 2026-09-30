from pathlib import Path
import collections, hashlib, json, os, platform, re, subprocess, sys, time
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10377-joint-evidence')
sys.path.insert(0,str(root))
from scripts.bench.structural_tactic_sweep import acquire_cpu
out=Path('/tmp/issue-10377-joint-profile-394c3c548')
out.mkdir(exist_ok=False)
exe=root/'.lake/build/bin/hexsigndet_bench'
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert not subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
cpu,lease=acquire_cpu();os.sched_setaffinity(0,{cpu})
meta={'schema':'hex-sign-det-joint-profile-v1','revision':revision,'cpu':cpu,'host':platform.node(),
      'load_before':os.getloadavg(),'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),
      'collector_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'state':'running'}
(out/'collector.py').write_bytes(Path(__file__).read_bytes())
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
command=[str(exe),'profile','Hex.SignDetBench.Joint.runComparison','--param','31',
         '--cache-mode','cold','--profiler',f'perf record --clockid mono -e cycles:u -F 199 --call-graph dwarf -o {out}/perf.data --']
meta['command']=command;meta['perf_version']=subprocess.check_output(['perf','--version'],text=True).strip()
env=dict(os.environ,LEAN_BENCH_TIMED_REGIONS_SIDECAR=str(out/'regions-%p.jsonl'))
meta['environment']={'LEAN_BENCH_TIMED_REGIONS_SIDECAR':env['LEAN_BENCH_TIMED_REGIONS_SIDECAR']}
try:
 with (out/'profile.log').open('w') as log:
  run=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 meta['exit_code']=run.returncode
 if run.returncode: raise RuntimeError('profiler failed; original output retained')
 script_command=['perf','script','--ns','-i',str(out/'perf.data'),'--no-demangle','-F','time,ip,sym,dso']
 meta['script_command']=script_command
 with (out/'perf-script.txt').open('w') as output:
  subprocess.run(script_command,stdout=output,check=True)
 sidecars=[json.loads(line) for p in out.glob('regions-*.jsonl') for line in p.read_text().splitlines()]
 regions=[(r['mono_t0_ns'],r['mono_t1_ns']) for r in sidecars if r['kind']=='region' and r['label']=='kernel']
 if len(regions)!=1: raise RuntimeError(f'expected one cold operation region, got {len(regions)}')
 raw=(out/'perf-script.txt').read_text();chunks=re.split(r'(?m)^(\d+\.\d+):\s*\n',raw)
 samples=[];outside=0
 for i in range(1,len(chunks),2):
  sec,frac=chunks[i].split('.');ns=int(sec)*10**9+int(frac.ljust(9,'0'))
  frames=[s.strip() for s in chunks[i+1].splitlines() if s.strip()]
  if any(a<=ns<=b for a,b in regions): samples.append({'mono_ns':ns,'frames':frames})
  else: outside+=1
 if not samples: raise RuntimeError('no operation-region samples parsed')
 counts=collections.Counter(re.sub(r'^[a-f0-9]+\s+','',s['frames'][0]) if s['frames'] else 'unresolved' for s in samples)
 summary={'operation_samples':len(samples),'outside_operation_samples':outside,'regions':regions,'sidecars':sidecars,
          'leaf_counts':dict(counts.most_common()),'samples':samples,
          'scope':'one operation-only cold comparison at degree 31; no scientific timing verdict or allocated-byte claim'}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 meta['state']='complete'
except BaseException as exc:
 meta.update(state='failed',error=str(exc),exception=type(exc).__name__);raise
finally:
 meta['binary_sha256_after']=hashlib.sha256(exe.read_bytes()).hexdigest()
 meta['revision_after']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
 meta['status_after']=subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
 meta['load_after']=os.getloadavg()
 (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
 lease.close()
