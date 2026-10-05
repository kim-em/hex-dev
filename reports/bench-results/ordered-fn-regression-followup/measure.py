"""Adjacent historical/current arms for the retained OrderedFn workload ladders."""
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10575')
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease

out = Path(__file__).resolve().parent
sources = json.loads((out / 'sources.json').read_text())
small = [128, 256, 512, 1024, 2048, 4096, 8192, 16384]
height = [65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608]
search = [8192, 10240, 12288, 14336, 16384, 20480, 24576, 28672]
nested = [4, 6, 8, 10, 12, 14, 16, 18]
workloads = [(n, small, 1) for n in ['scan', 'second', 'third', 'comparison', 'degree', 'height']]
workloads += [('subtraction', small, 4), ('denominators', [16,32,64,128,256,512,1024,2048], 1)]
workloads += [(n, height, 1) for n in ['compareHeight', 'realHeight', 'provider']]
workloads += [(n, search, 1) for n in ['refinement', 'jointRefinement', 'approximation']]
workloads += [('horner', search, 4), ('successiveApproximation', nested, 4), ('thirdApproximation', nested, 4)]
schedule = {'question': 'Which retained computational workloads regress from the last committed benchmark baseline to the API-polished candidate?', 'trials': 3, 'order': 'trial-major; adjacent baseline/candidate arms; AB on even trials, BA on odd trials', 'timeout_seconds': 180, 'workloads': [{'name': 'Hex.OrderedFnBench.'+n, 'parameters': ps, 'target_nanos': sec*1000000000} for n,ps,sec in workloads], 'scope': 'Whole pinned source/toolchain comparison; not causal attribution to the API patch and not a fresh Phase-4 complexity attestation.'}
(out/'schedule.json').write_text(json.dumps(schedule,indent=2)+'\n')
cpu, lease = cpu_lease()
os.sched_setaffinity(0,{cpu})
os.environ['LEAN_NUM_THREADS']='4'
context = {'cpu':cpu, 'host':platform.node(), 'platform':platform.platform(), 'load_before':os.getloadavg(), 'started_unix':time.time(), 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(out/'context.json').write_text(json.dumps(context,indent=2)+'\n')
failures = 0
try:
  with (out/'observations.jsonl').open('x') as rows:
    for trial in range(3):
      for work in schedule['workloads']:
        name = work['name']; short = name.rsplit('.',1)[-1]
        for param in work['parameters']:
          for arm in (['baseline','candidate'] if trial%2==0 else ['candidate','baseline']):
            binary = Path(sources[arm]['binary'])
            if hashlib.sha256(binary.read_bytes()).hexdigest()!=sources[arm]['binary_sha256']:raise RuntimeError('changed frozen executable')
            command = [str(binary),'_child','--bench',name,'--param',str(param),'--target-nanos',str(work['target_nanos'])]
            stem=out/f'{trial}-{short}-{param}-{arm}'
            record={'trial':trial,'name':name,'param':param,'arm':arm,'command':command,'load_before':os.getloadavg()}
            with stem.with_suffix('.stdout').open('w') as stdout, stem.with_suffix('.stderr').open('w') as stderr:
              try:
                run=subprocess.run(command,stdout=stdout,stderr=stderr,timeout=schedule['timeout_seconds'])
                record['returncode']=run.returncode
              except subprocess.TimeoutExpired:
                record.update(returncode=None, failure='parent timeout')
            record['load_after']=os.getloadavg()
            try:
              record['observation']=json.loads(stem.with_suffix('.stdout').read_text())
            except (ValueError, UnicodeError) as e:
              record['parse_error']=str(e)
            if record.get('returncode')!=0 or record.get('observation',{}).get('status')!='ok': failures+=1
            rows.write(json.dumps(record)+'\n');rows.flush()
        print(f'trial {trial}: {short} complete; cumulative failed arms {failures}',flush=True)
finally:
  context.update(finished_unix=time.time(),load_after=os.getloadavg(),failed_arms=failures,binaries_after={arm:hashlib.sha256(Path(src['binary']).read_bytes()).hexdigest() for arm,src in sources.items()})
  (out/'context.json').write_text(json.dumps(context,indent=2)+'\n')
  lease.close()
raise SystemExit(1 if failures else 0)
