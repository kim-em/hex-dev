#!/usr/bin/env python3
"""Compare sampled driver initializers and explicit random-state boundaries."""
from pathlib import Path
import json,subprocess,sys,tempfile
root=Path(__file__).resolve().parents[2];sys.path.insert(0,str(root));from scripts.bench.groebner_json import loads
records=[loads(line)for line in(root/'conformance-fixtures/HexGroebner/f4.jsonl').read_text().splitlines()];binaries=[root/'.lake/build/bin/hexgroebner_sample',root/'.lake/build/bin/hexgroebner_sample_full'];count=0
with tempfile.TemporaryDirectory(prefix='sampled-driver-')as directory:
 path=Path(directory)/'input.json'
 for record in records:
  value=record['value'];path.write_text(json.dumps({k:value[k]for k in ['p','variables','order','generators']}));responses=[]
  for binary in binaries:
   r=subprocess.run([str(binary),'--seed','10987','--scheduling',value['scheduling'],str(path)],capture_output=True,text=True,timeout=30);assert r.returncode==0,(record['case'],r.stdout,r.stderr);output=loads(r.stdout);output.pop('candidateNanos');assert output['kind']=='unchecked_candidate'and output['algorithm']=='f4-sampled';assert output['randomState']==(10987+output['sampling']['randomWords']*0x9e3779b97f4a7c15)%(1<<64);responses.append(output)
  assert responses[0]==responses[1],record['case'];count+=1
print('sampled driver: both initializers agree on',count,'complete outputs, counters and advanced random states')

with tempfile.TemporaryDirectory(prefix='sampled-boundaries-')as directory:
 path=Path(directory)/'input.json'
 unit={"p":2,"variables":1,"order":"grevlex","generators":[[[[2],1],[[1],1]]]}
 path.write_text(json.dumps(unit))
 for binary in binaries:
  for flags,code,kind in [([],0,"unchecked_candidate"),(["--work","0"],3,"exhausted"),(["--block-rows","0"],2,"invalid_configuration"),(["--block-rows","4097"],2,"invalid_configuration"),(["--zero-tests","0"],2,"invalid_configuration")]:
   r=subprocess.run([str(binary),"--seed","9",*flags,str(path)],capture_output=True,text=True,timeout=30);value=loads(r.stdout);assert r.returncode==code and value['kind']==kind
   assert value['randomState']==9
   if code==0:assert value['basis']==unit['generators']
   else:assert value['sampling']['randomWords']==0 and 'basis'not in value
print('sampled driver: configuration/exhaustion preserve state; ordinary F2 keeps x^2+x')

with tempfile.TemporaryDirectory(prefix='sampled-cutoff-')as directory:
 path=Path(directory)/'input.json'
 value=next(r['value']for r in records if r['value']['p']==2147483647 and 'missing-s-pair'in r['case'])
 path.write_text(json.dumps({k:value[k]for k in ['p','variables','order','generators']}))
 responses=[]
 for binary in binaries:
  for cutoff in ['0','1000000',str(2**90)]:
   r=subprocess.run([str(binary),'--seed','10987','--min-targets',cutoff,str(path)],capture_output=True,text=True,timeout=30)
   assert r.returncode==0,(r.stdout,r.stderr)
   output=loads(r.stdout);output.pop('candidateNanos');assert output['minimumTargets']==int(cutoff)
   if int(cutoff)>0:assert output['sampling']['randomWords']==output['sampling']['calls']==0 and output['randomState']==10987
   responses.append(output)
  for cutoff in ['-1','nope']:
   r=subprocess.run([str(binary),'--min-targets',cutoff,str(path)],capture_output=True,text=True,timeout=30)
   assert r.returncode==2 and loads(r.stdout)['kind']=='invalid_input'
 assert responses[:3]==responses[3:]
 assert responses[0]['sampling']['calls']>0
 assert responses[0]['basis']==responses[1]['basis']==responses[2]['basis']
 deterministic=subprocess.run([str(root/'.lake/build/bin/hexgroebner_compute'),str(path)],capture_output=True,text=True,timeout=30)
 assert deterministic.returncode==0
 reference=loads(deterministic.stdout)
 assert responses[1]['basis']==reference['basis']and responses[1]['statistics']==reference['statistics']
 mixed=next(r['value']for r in records if r['value']['p']==2147483647 and 'grevlex/katsura-2'in r['case'])
 path.write_text(json.dumps({k:mixed[k]for k in ['p','variables','order','generators']}))
 responses=[]
 for binary in binaries:
  pair=[]
  for flags in [[],['--min-targets','2'],['--min-targets','2','--min-targets','0']]:
   r=subprocess.run([str(binary),'--seed','10987',*flags,str(path)],capture_output=True,text=True,timeout=30)
   assert r.returncode==0
   output=loads(r.stdout);output.pop('candidateNanos');pair.append(output)
  assert pair[0]==pair[2]and 0<pair[1]['sampling']['calls']<pair[0]['sampling']['calls']
  assert pair[1]['basis']==pair[0]['basis']and pair[1]['minimumTargets']==2
  responses.append(pair)
 assert responses[0]==responses[1]
print('sampled driver: explicit zero/huge cutoff and malformed values pass on both initializers')
