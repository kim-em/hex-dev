from pathlib import Path
import collections, hashlib, json, os, platform, re, subprocess, sys, time
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10377-joint-evidence')
sys.path.insert(0,str(root))
from scripts.bench.structural_tactic_sweep import acquire_cpu
out=Path('/tmp/issue-10377-joint-allocation-394c3c548')
out.mkdir(exist_ok=False)
exe=root/'.lake/build/bin/hexsigndet_bench'
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert not subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True)
cpu,lease=acquire_cpu();os.sched_setaffinity(0,{cpu})
meta={'schema':'hex-sign-det-joint-allocation-v1','revision':revision,'cpu':cpu,'host':platform.node(),
      'load_before':os.getloadavg(),'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),
      'collector_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'state':'running'}
(out/'collector.py').write_bytes(Path(__file__).read_bytes())
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
command=[str(exe),'profile','Hex.SignDetBench.Joint.runComparison','--param','31',
         '--cache-mode','cold','--profiler',f'heaptrack --record-only -o {out}/heaptrack --']
meta['command']=command;meta['heaptrack_version']=subprocess.check_output(['heaptrack','--version'],text=True).strip()
env=dict(os.environ,LEAN_BENCH_TIMED_REGIONS_SIDECAR=str(out/'regions-%p.jsonl'))
meta['environment']={'LEAN_BENCH_TIMED_REGIONS_SIDECAR':env['LEAN_BENCH_TIMED_REGIONS_SIDECAR']}
try:
 with (out/'profile.log').open('w') as log:
  run=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 meta['exit_code']=run.returncode
 if run.returncode: raise RuntimeError('profiler failed; original output retained')
 sidecars=[json.loads(line) for p in out.glob('regions-*.jsonl') for line in p.read_text().splitlines()]
 regions=[r for r in sidecars if r['kind']=='region' and r['label']=='kernel']
 if len(regions)!=1: raise RuntimeError('expected one cold comparison operation')
 meta['regions']=regions
 tracks=list(out.glob('heaptrack*.gz'))+list(out.glob('heaptrack*.zst'))
 if len(tracks)!=1: raise RuntimeError(f'expected one heaptrack output, found {tracks}')
 for label, extra in [('whole-process',[]),('comparison',['--filter-bt-function','l_Hex_SignDetBench_Joint_runComparison'])]:
  analyze=['heaptrack_print','-f',str(tracks[0]),'--print-peaks','0','--print-temporary','0','--print-allocators','1','--peak-limit','8',*extra]
  meta.setdefault('analysis_commands',[]).append(analyze)
  with (out/(label+'.txt')).open('w') as output:
   subprocess.run(analyze,stdout=output,stderr=subprocess.STDOUT,check=True)
 meta['scope']='one instrumented cold comparison; whole-process and callback-stack-filtered allocation observations, not scientific timings'
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
