"""One diagnostic attribution for each changed structural family."""
import json,os,re,sys,time
from pathlib import Path
sys.path.insert(0,str(Path.cwd()))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
from scripts.bench.det_bench_limits import supervise
root=Path('/tmp/issue-10320-structural-profiles')
root.mkdir(exist_ok=False)
quiet=Path('/tmp/issue-10320-integrated-structural-fixed')
spent=sum(json.loads((p/'status.json').read_text())['elapsed_seconds'] for p in [quiet,Path('/tmp/issue-10320-integrated-structural'),Path('/tmp/issue-10320-integrated-structural-recovery')])
seconds=min(360,int(1800-spent))
if seconds<=0:raise SystemExit('measurement budget exhausted')
records=[]
def run(deadline):
 cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});os.environ['LEAN_NUM_THREADS']='1'
 topology=sweep.cpu_topology(cpu);monitored=sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
 environment=sweep.environment()
 try:
  for name in ['Triangular3','RationalOne','SparseOne']:
   for arm in ['Mathlib','Hex']:
    original=Path(f'bench/HexPolyDetMathlib/ProofProbe/Structural{name}{arm}.lean').read_text()
    original=original.replace('set_option profiler false','set_option profiler true\nset_option profiler.threshold 0')
    original=original.replace('namespace HexPolyDetMathlib.ProofProbe.Structural', '''open Lean Elab Tactic
elab "structural_profile_call" t:tacticSeq : tactic => do
  let start ← IO.monoNanosNow
  evalTactic t
  logInfo m!"CALL_NS {(← IO.monoNanosNow) - start}"
namespace HexPolyDetMathlib.ProofProbe.StructuralProfile''',1)
    original=original.replace('end HexPolyDetMathlib.ProofProbe.Structural','end HexPolyDetMathlib.ProofProbe.StructuralProfile')
    original=original.replace(' := by\n  ', ' := by\n  structural_profile_call\n    ',1)
    p=Path(f'bench/HexPolyDetMathlib/ProofProbe/StructuralProfile{name}{arm}.lean')
    assert not p.exists();p.write_text(original);(root/(p.name+'.txt')).write_text(original)
    def observe(module,result):
     with (root/'observations.jsonl').open('a') as f:f.write(json.dumps(dict(module=module,result=result))+'\n')
    try:
     result=sweep.build_sample(f'HexPolyDetMathlib.ProofProbe.StructuralProfile{name}{arm}',min(60,deadline-time.monotonic()-2),cpu,monitored,observe,True)
    finally:p.unlink(missing_ok=True)
    out=result['compiler_output']
    call=int(re.search(r'CALL_NS (\d+)',out)[1])/1e6
    checks=re.findall(r'info: [^\n]+:(\d+):8: type checking took ([0-9.e+]+)(ms|s)',out)
    if len(checks)!=1:raise RuntimeError('expected one final theorem kernel counter: '+str(checks))
    kernel=float(checks[0][1])*(1000 if checks[0][2]=='s' else 1)
    records.append(dict(name=name,arm=arm,call_ms=call,final_kernel_ms=kernel,proof_ms=call+kernel,result=result))
    (root/'results.json').write_text(json.dumps(dict(cpu=cpu,topology=topology,environment=environment,samples=records),indent=2))
    print(name,arm,call,kernel,flush=True)
 finally:lease.close()
raise SystemExit(supervise(run,seconds,root/'status.json'))
