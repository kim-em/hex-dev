import json, os
from pathlib import Path
import sys
sys.path.insert(0, str(Path.cwd()))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
path = Path('bench/HexPolyDetMathlib/ProofProbe/Issue10320RowInspect.lean')
assert not path.exists()
source = '''import HexPolyDetMathlib.ProofProbe.N4K2D2S4Hex
import HexReflect.Session
open Lean Meta
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_meta do
  let some proof := (← getConstInfo `result).value? (allowOpaque := true) | throwError "no result"
  lambdaTelescope proof fun _ e => do
    let some body := (← getConstInfo e.getAppFn.constName!).value? (allowOpaque := true)
      | throwError "no auxiliary proof"
    logInfo m!"auxiliary nodes {Hex.Reflect.sourceNodeCount body 10000000}"
    lambdaLetTelescope body fun _ e => do
      let mut e := e
      while e.getAppFn.isConstOf ``id do e := e.appArg!
      unless e.getAppFn.isConstOf ``Eq.trans do throwError "unexpected proof shape"
      let args := e.getAppArgs
      for trial in [:6] do
        for (label, arg) in [("entries", args[args.size - 2]!),
            ("numeric_certificate_and_transport", args[args.size - 1]!)] do
          let before ← IO.monoNanosNow
          checkWithKernel arg
          logInfo m!"component {label} trial {trial + 1} ns {(← IO.monoNanosNow) - before}"
'''
path.write_text(source)
cpu, lease = cpu_lease()
os.sched_setaffinity(0, {cpu})
os.environ['LEAN_NUM_THREADS'] = '1'
record = dict(stage='row-factor-shared-components', cpu=cpu, inspector=source, environment=sweep.environment())
observed = []
try:
    record['result'] = sweep.build_sample('HexPolyDetMathlib.ProofProbe.Issue10320RowInspect', 45, cpu, [cpu], lambda m,r: observed.append(r), retain_compiler_output=True)
except Exception as exc:
    record['error'] = str(exc)
    record['result'] = observed[-1] if observed else {}
finally:
    Path('/tmp/issue-10320-profile/row-factor-components-final.json').write_text(json.dumps(record, indent=2))
    print(record['result'].get('compiler_output', ''))
    path.unlink()
    lease.close()
