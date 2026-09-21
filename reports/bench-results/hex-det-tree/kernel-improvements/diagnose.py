import json,os,re,sys,time,textwrap,hashlib
from pathlib import Path
sys.path.insert(0,str(Path.cwd()))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
from scripts.bench.det_bench_limits import supervise
stage=sys.argv[1];pairs=int(sys.argv[2]) if len(sys.argv)>2 else 2
out=Path('/tmp/issue-10320-kernel')/stage;out.mkdir(exist_ok=False)
probes=Path('bench/HexPolyDetMathlib/ProofProbe');prefix='HexPolyDetMathlib.ProofProbe.';records=[]
(out/'sources.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path('HexPolyDetMathlib/Frontend.lean'),Path('HexMvPoly/Kernel.lean')]},indent=2))
def run(deadline):
 cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});os.environ['LEAN_NUM_THREADS']='1';topology=sweep.cpu_topology(cpu);monitored=sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu];environment=sweep.environment()
 def observe(module,result):
  with (out/'observations.jsonl').open('a') as f:f.write(json.dumps(dict(module=module,result=result))+'\n')
 try:
  for pair in range(pairs):
   for name in ['DenseQuadratic4']:
    for arm in (['Mathlib','Hex'] if pair%2==0 else ['Hex','Mathlib']):
     old='Counter'+name+arm;module='KernelCompare'+name+arm
     source=Path(f'reports/bench-results/hex-det-tree/counterexamples/{old}.lean.txt').read_text()
     source=source.replace(old,module).replace('set_option profiler false','set_option profiler true\nset_option profiler.threshold 0')
     source=source.replace('namespace '+prefix,'''open Lean Elab Tactic
elab "kernel_compare_call" t:tacticSeq : tactic => do
  let start ← IO.monoNanosNow
  withOptions (fun opts => opts.setBool `profiler false) (evalTactic t)
  let elapsed := (← IO.monoNanosNow)-start
  logInfo m!"CALL_NS {elapsed}"
namespace '''+prefix,1)
     head,body=source.split(' := by\n',1);body,end=body.rsplit('\nend ',1)
     source=head+' := by\n  kernel_compare_call\n'+textwrap.indent(body,'  ')+'\nend '+end
     p=probes/(module+'.lean');assert not p.exists();p.write_text(source);(out/(p.name+'.txt')).write_text(source)
     try:result=sweep.build_sample(prefix+module,min(60,deadline-time.monotonic()-2),cpu,monitored,observe,True)
     finally:p.unlink(missing_ok=True)
     text=result['compiler_output'];call=int(re.search(r'CALL_NS (\d+)',text)[1])/1e6
     checks=re.findall(r'info: [^\n]+:(\d+):8: type checking took ([0-9.e+]+)(ms|s)',text)
     assert len(checks)==1,checks
     kernel=float(checks[0][1])*(1000 if checks[0][2]=='s' else 1)
     records.append(dict(pair=pair,name=name,arm=arm,call_ms=call,final_kernel_ms=kernel,proof_ms=call+kernel,result=result))
     (out/'results.json').write_text(json.dumps(dict(cpu=cpu,topology=topology,environment=environment,samples=records),indent=2))
     print(name,arm,pair,'call',round(call,2),'kernel',round(kernel,2),'total',round(call+kernel,2),flush=True)
 finally:lease.close()
raise SystemExit(supervise(run,360,out/'status.json'))
