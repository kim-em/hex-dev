"""Bounded quiet AB/BA comparison; run from the repository root."""
import hashlib,json,os,re,statistics,sys,time
from pathlib import Path
sys.path.insert(0,str(Path.cwd()))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease, AXIOMS
from scripts.bench.det_bench_limits import supervise
root=Path('/tmp/issue-10320-kernel/final');root.mkdir(exist_ok=False)
probes=Path('bench/HexPolyDetMathlib/ProofProbe');prefix='HexPolyDetMathlib.ProofProbe.'
inputs=Path('reports/bench-results/hex-det-tree/counterexamples')
names=['DenseIndependent4','DenseQuadratic4','Blocks6']
records=[]
(root/'run.py').write_text(Path(__file__).read_text())
(root/'production-sources.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path('HexMvPoly/Kernel.lean'),Path('HexPolyDetMathlib/Frontend.lean')]},indent=2))
def run(deadline):
 cpu,lease=cpu_lease();os.sched_setaffinity(0,{cpu});os.environ['LEAN_NUM_THREADS']='1';topology=sweep.cpu_topology(cpu);monitored=sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu];environment=sweep.environment();created=[]
 def save():
  (root/'results.json').write_text(json.dumps(dict(cpu=cpu,topology=topology,environment=environment,cases=records),indent=2))
 def observe(module,result):
  with (root/'observations.jsonl').open('a') as f:f.write(json.dumps(dict(module=module,result=result))+'\n')
 def build(module):
  remaining=deadline-time.monotonic()-2
  if remaining<=0:raise RuntimeError('measurement deadline exhausted')
  return sweep.build_sample(prefix+module,min(60,remaining),cpu,monitored,observe,True)
 try:
  baseline='KernelBaseline';p=probes/(baseline+'.lean');assert not p.exists();p.write_text((probes/'StructuralBaseline.lean').read_text());created.append(p)
  (root/(p.name+'.txt')).write_text(p.read_text())
  for name in names:
   record=dict(name=name,samples=[],audits={});records.append(record)
   for arm in ['Mathlib','Hex']:
    old='Counter'+name+arm;module='KernelQuiet'+name+arm
    text=(inputs/(old+'.lean.txt')).read_text().replace(old,module)
    p=probes/(module+'.lean');assert not p.exists();p.write_text(text);created.append(p);(root/(p.name+'.txt')).write_text(text)
    build(module)
    audit='KernelAudit'+name+arm;target=prefix+module+'.result';text=f'import {prefix+module}\n#print axioms {target}\n'
    if arm=='Hex':text+=f'''run_meta do
  let root := ``{target}
  let mut pending := [root]
  let mut found := false
  while let name :: rest := pending do
    pending := rest
    let some value := (← Lean.getConstInfo name).value? (allowOpaque := true)
      | throwError "missing proof"
    for used in value.getUsedConstants do
      if used == ``HexMatrixMathlib.DetPoly.Polynomial.target_det then found := true
      if root.isPrefixOf used then pending := used :: pending
  unless found do throwError "unexpected determinant route"
'''
    p=probes/(audit+'.lean');assert not p.exists();p.write_text(text);created.append(p);(root/(p.name+'.txt')).write_text(text)
    result=build(audit);match=re.search(r"depends on axioms: \[(.*?)\]",result['compiler_output'],re.S)
    assert match and [x.strip() for x in match[1].split(',')]==list(AXIOMS)
    record['audits'][arm]=result;save()
   for pair in range(6):
    for arm in (['Mathlib','Hex'] if pair%2==0 else ['Hex','Mathlib']):
     module='KernelQuiet'+name+arm
     order=[('baseline',baseline),('candidate',module)]
     if pair%2:order.reverse()
     built={role:build(mod) for role,mod in order}
     record['samples'].append(dict(pair=pair,arm=arm,order=[r for r,_ in order],delta_ms=(built['candidate']['wall_nanos']-built['baseline']['wall_nanos'])/1e6,**built));save()
    print(name,pair,{arm:round(statistics.median(s['delta_ms'] for s in record['samples'] if s['arm']==arm),1) for arm in ['Mathlib','Hex']},flush=True)
 finally:
  for p in created:p.unlink(missing_ok=True)
  lease.close()
raise SystemExit(supervise(run,600,root/'status.json'))
