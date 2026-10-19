#!/usr/bin/env python3
"""Check prepared scalar and finite-valuation assembly evidence."""
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest();c=json.loads((p/'context.json').read_text())
assert sha((root/'reports/data/hexrcf-tower-compile/context.json').read_bytes())==c['parent_context_sha256']
subprocess.run(['git','merge-base','--is-ancestor',c['parent_source_commit'],c['source_commit']],cwd=root,check=True)
for name,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+name],cwd=root);assert sha(raw)==digest,name
 if args.check_head:assert sha((root/name).read_bytes())==digest,name
for name,digest in json.loads((p/'manifest.json').read_text()).items():assert sha((p/name).read_bytes())==digest,name
read=lambda name:gzip.decompress((p/(name+'.gz')).read_bytes()).decode()
for name in c['successful_logs']:assert 'code=exited, status=0/SUCCESS' in read(name),name
quote=read('source-valuation-full-quote-2.log')
for n in [705649,705699,707592,9330130,9336963,9337057]:assert f'proofNodes={n}' in quote,n
assert 'prepared source coefficient inventory compiled in request' in quote
assert 'reused=2; validated=7' in quote
full=re.sub(r'\s+',' ',read(c['full_audit_log']))
t,d,tr=c['full_audit_counts']
assert f'{t} theorems/{d} definitions; nonempty traces={tr}' in full
assert 'full axioms=[propext, Classical.choice, Quot.sound]' in full
final=re.sub(r'\s+',' ',read(c['integration_log']))
for marker in ['fresh source valuations: 14 actual theorem bodies; nonempty traces=13',
 'source valuation coordinates=0; proofNodes=7590','source valuation coordinates=1; proofNodes=11174',
 'source valuation coordinates=2; proofNodes=16484',
 'swapped coordinates/proofs, missing entries and wrong coordinate counts rejected',
 'unresolved coordinates rejected without metavariable or declaration changes']:
 assert marker in final,marker
checks=json.loads((p/'source-valuation-final-metadata.json').read_text())
assert [x['name'] for x in checks]==['dag_tests','copyright','lines','dag','admissions','manifest','freshness','literals','source_literals','diff']
assert all(x['exit_code']==0 for x in checks)
assert 'Ran 12 tests' in read('source-valuation-final-dag_tests.log')
for name,digest in json.loads((p/'source-valuation-final-inputs.json').read_text()).items():assert c['sources'][name]==digest,name
ins=json.loads((p/'inspection.json').read_text())
assert len(ins)==6 and {(x['viewport'],x['kind']) for x in ins}=={(w,k) for w in [1440,390] for k in ['api','code','provenance']}
assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in ins)
source=subprocess.check_output(['git','show',c['source_commit']+':conformance/HexRCF/CellSourceQuote.lean'],cwd=root).decode()
assert 'TowerCompile.prepareWith source' in source and 'CellQuote.valuationWith source' in source
assert 'fin_cases i; exact $coefficientTerm' not in source
print(f'Verified prepared source valuations: {len(c["sources"])} source bindings, whole original-goal quote, private proof audits, ordered finite families and six final manual captures. Full #10358 incomplete.')
