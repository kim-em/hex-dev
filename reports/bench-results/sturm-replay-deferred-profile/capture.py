from pathlib import Path
import sys,os,json,hashlib,subprocess,datetime,gzip
root=Path.cwd();sys.path.insert(0,str(root))
from scripts.bench.det_symbolic_sweep import cpu_lease
out=root/'reports/bench-results/sturm-replay-deferred-profile';out.mkdir()
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu})
exe=root/'.lake/build/bin/hexsturm_bench';regions=out/'regions.jsonl'
cmd=[str(exe),'profile','Hex.SturmBench.runReplay','--param','1024','--target-inner-nanos','500000000','--profiler','perf record --clockid mono -F 1999 -g --call-graph dwarf -o /tmp/10375-replay-deferred.perf --']
meta={'git_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'git_status':subprocess.check_output(['git','status','--short'],text=True),'cpu':cpu,'host':os.uname().nodename,'start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'load_start':os.getloadavg(),'argv':cmd,'binary_sha256':hashlib.sha256(exe.read_bytes()).hexdigest()}
with (out/'profile.log').open('w') as f:
 meta['exit_code']=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,LEAN_BENCH_TIMED_REGIONS_SIDECAR=str(regions))).returncode
cmd2=['perf','script','--ns','-G','-F','pid,time,period,ip,sym','-i','/tmp/10375-replay-deferred.perf'];meta['samples_command']=cmd2
r=subprocess.run(cmd2,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
with gzip.open(out/'samples.txt.gz','wb') as f:f.write(r.stdout)
meta.update(end=datetime.datetime.now(datetime.timezone.utc).isoformat(),load_end=os.getloadavg())
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
(out/'registration.lean.txt').write_bytes((root/'bench/HexSturm/Bench.lean').read_bytes())
(out/'Basic.lean.txt').write_bytes((root/'HexRealRoots/Basic.lean').read_bytes())
(out/'capture.py').write_bytes(Path(__file__).read_bytes())
lease.close()
