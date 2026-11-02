#!/usr/bin/env python3
"""Verify the ordinary-real stored arithmetic compilation evidence."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
p=Path(__file__).resolve().parent
root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((p/'context.json').read_text())
parent=root/'reports/data/hexrcf-public-model/context.json'
assert sha(parent.read_bytes())==c['parent_context_sha256']
subprocess.run(['git','merge-base','--is-ancestor',c['parent_source_commit'],c['source_commit']],cwd=root,check=True)
for name,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+name],cwd=root)
 assert sha(raw)==digest,name
 if args.check_head:assert sha((root/name).read_bytes())==digest,name
for name,digest in json.loads((p/'manifest.json').read_text()).items():assert sha((p/name).read_bytes())==digest,name
read=lambda name:gzip.decompress((p/(name+'.gz')).read_bytes()).decode()
for name in c['successful_logs']:assert 'code=exited, status=0/SUCCESS' in read(name),name
log=read('tower-compile-final-integration-3.log')
for marker in ['fresh tower quotation: 36 actual theorem bodies; nonempty traces=35',
 'ordered tower inventory: 2 coefficients, 2 original guards',
 'original guard inventories survive zero multiplication; reset source budgets rejected',
 'terminal leaf failure restored state; swapped model and unsupported function rejected',
 'empty coefficient/divisor inventories still validate the retained real model',
 'transferred source usage is checked against every enclosing limit']:
 assert marker in log,marker
assert any('fresh tower quotation: 36 actual theorem bodies' in line and 'full axioms=[propext, Classical.choice, Quot.sound]' in line for line in log.splitlines())
for n in [441,711,1111,540,826,742,2284,247,276]:assert f'proofNodes={n}' in log,n
checks=json.loads((p/'tower-compile-final-metadata.json').read_text())
assert [x['name'] for x in checks]==['dag_tests','copyright','lines','dag','admissions','manifest','freshness','literals','source_literals','diff']
assert all(x['exit_code']==0 for x in checks)
assert 'Ran 12 tests' in read('tower-compile-final-dag_tests.log')
for name,digest in json.loads((p/'tower-compile-final-inputs.json').read_text()).items():assert c['sources'][name]==digest,name
ins=json.loads((p/'inspection.json').read_text())
assert {(x['viewport'],x['kind']) for x in ins}=={(w,k) for w in [1440,390] for k in ['api','code','provenance']}
assert len(ins)==6 and all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in ins)
print(f'Verified tower source arithmetic: {len(c["sources"])} source bindings, actual/private 36-body fresh audit, ordered original inventories, failure/decline/model/budget controls and six manual views. Full #10358 incomplete.')
