#!/usr/bin/env python3
"""Check consumption of the landed public presentation-model equation."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest();c=json.loads((p/'context.json').read_text())
subprocess.run(['git','merge-base','--is-ancestor',c['owner_merge'],c['source_commit']],cwd=root,check=True)
assert sha((root/'reports/data/hexrcf-joint-source-assembly/context.json').read_bytes())==c['parent_context_sha256']
for name,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+name],cwd=root);assert sha(raw)==digest,name
 if args.check_head:assert sha((root/name).read_bytes())==digest,name
 if name in c['owner_paths']:assert raw==subprocess.check_output(['git','show',c['owner_merge']+':'+name],cwd=root),name
for name,digest in json.loads((p/'manifest.json').read_text()).items():assert sha((p/name).read_bytes())==digest,name
ci=json.loads((p/'completion-audit-pr10967-ci.json').read_text());assert ci['headSha']==c['owner_head'] and ci['status']=='completed' and ci['conclusion']=='success'
assert ci['jobs'] and all(j['status']=='completed' and j['conclusion']=='success' for j in ci['jobs'])
assert not [(s['name'],s['conclusion']) for j in ci['jobs'] for s in j['steps'] if s['conclusion'] in ['failure','cancelled']]
state=json.loads((p/'pr10967-merged-state.json').read_text());assert state['state']=='MERGED' and state['mergeCommit']['oid']==c['owner_merge']
read=lambda name:gzip.decompress((p/(name+'.gz')).read_bytes()).decode()
for name in ['public-model-integration-1.log','public-model-manual-integration-1.log','public-model-render-1.log','public-model-browser-1.log']:
 assert 'code=exited, status=0/SUCCESS' in read(name),name
native=read('public-model-integration-1.log')
assert 'fresh source acceptance bodies retain original domains and actual complete production laws with the standard three axioms' in native
assert 'thirteen automatic algebraic-input proof bodies and actual owner dependencies checked' in native
full=read('public-model-manual-integration-1.log');assert '1191 theorems/202 definitions; nonempty traces=1351' in full
assert 'proofNodes=9337314' in full
metadata=json.loads((p/'public-model-final-metadata.json').read_text())
assert [r['name'] for r in metadata]==['dag_tests','copyright','lines','dag','admissions','manifest','freshness','literals','source_literals','diff']
for r in metadata:assert r['exit_code']==0,r
assert 'Ran 12 tests' in read('public-model-final-dag_tests.log')
for name,digest in json.loads((p/'public-model-final-inputs.json').read_text()).items():assert c['sources'][name]==digest,name
adapter=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/NumberField.lean'],cwd=root).decode()
assert 'import all HexRealClosureTheory.NumberFieldTower' not in adapter
assert 'rw [Hex.RealClosure.NumberField.Presentation.model_eq]' in adapter
manual=subprocess.check_output(['git','show',c['source_commit']+':HexManual/Chapters/HexRCF/AlgebraicCells.lean'],cwd=root).decode()
assert 'meta def quoteSourcePacket' in manual and 'SourceIdentity.restorePacketWith' in manual
assert 'authenticates its coefficient within its own' in manual
ins=json.loads((p/'inspection.json').read_text());assert len(ins)==6
assert {(x['viewport'],x['kind']) for x in ins}=={(w,k) for w in [1440,390] for k in ['api','code','provenance']}
assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in ins)
print(f'Verified landed public model: {len(c["sources"])} source bindings, exact-head prerequisite CI, ordinary adapter import, native/source/fresh proof compatibility and six manual captures; full #10358 incomplete.')
