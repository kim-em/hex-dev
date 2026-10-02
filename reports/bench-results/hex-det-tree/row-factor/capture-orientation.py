import json,os,hashlib
from pathlib import Path
import sys
sys.path.insert(0,str(Path.cwd()))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
p=Path('bench/HexPolyDetMathlib/ProofProbe/Issue10320Inspect.lean')
assert not p.exists()
source=Path('bench/HexPolyDetMathlib/ProofProbe/PackedN4K2D2S4Packed.lean').read_text().replace('profiler.threshold 1000000','profiler.threshold 0')
inspect=Path('/tmp/issue-10320-profile/Inspect.paired.lean').read_text()
inspect=inspect[inspect.index('open Lean Meta'):]
start=inspect.index('      for order in [[')
inspect=inspect[:start]+'''      for trial in [:6] do
        let order := if trial % 2 == 0 then [("old", hp), ("new", cert)] else [("new", cert), ("old", hp)]
        for (name, h) in order do
          let before ← IO.monoNanosNow
          checkWithKernel h
          logInfo m!"paired_certificate trial {trial + 1} {name} ns {(← IO.monoNanosNow) - before}"
        let totalBefore ← IO.monoNanosNow
        for arg in args.toList.drop (args.size - 3) do
          let before ← IO.monoNanosNow
          checkWithKernel arg
          logInfo m!"entry_target trial {trial + 1} {arg.getAppFn.constName?} ns {(← IO.monoNanosNow) - before}"
        logInfo m!"entry_target_total trial {trial + 1} ns {(← IO.monoNanosNow) - totalBefore}"
'''
text='import HexReflect.Session\n'+source+'\n'+inspect
p.write_text(text)
cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});os.environ['LEAN_NUM_THREADS']='1'
record=dict(environment=sweep.environment(),cpu=cpu,stage='entry-orientation',inspector_sha256=hashlib.sha256(text.encode()).hexdigest())
observed=[]
try:
 result=sweep.build_sample('HexPolyDetMathlib.ProofProbe.Issue10320Inspect',45,cpu,[cpu],lambda _m,r:observed.append(r),retain_compiler_output=True)
 record['result']=result
 out=Path('/tmp/issue-10320-profile/entry-orientation.json');out.write_text(json.dumps(record,indent=2))
 for line in result['compiler_output'].splitlines():
  if any(t in line for t in ['auxiliary nodes','paired_certificate trial','entry_target_total trial','det.symbolic.nodes','det.symbolic.kernel']):print(line)
except Exception as e:
 record['error']=str(e)
 if observed:record['result']=observed[-1]
 Path('/tmp/issue-10320-profile/entry-orientation.json').write_text(json.dumps(record,indent=2))
 raise
finally:
 p.unlink();lease.close()
