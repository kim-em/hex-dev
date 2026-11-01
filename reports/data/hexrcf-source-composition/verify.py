#!/usr/bin/env python3
"""Verify the immutable source-arithmetic composition evidence."""
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=Path(__file__).resolve().parent
root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((p/'context.json').read_text())
parent=root/'reports/data/hexrcf-source-valuations/context.json'
assert sha(parent.read_bytes())==c['parent_context_sha256']
for ancestor in [c['parent_source_commit'],c['owner_merge_commit']]:
 subprocess.run(['git','merge-base','--is-ancestor',ancestor,c['source_commit']],cwd=root,check=True)
for name,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+name],cwd=root)
 assert sha(raw)==digest,name
 if args.check_head:assert sha((root/name).read_bytes())==digest,name
for name,digest in json.loads((p/'manifest.json').read_text()).items():assert sha((p/name).read_bytes())==digest,name
read=lambda n:gzip.decompress((p/(n+'.gz')).read_bytes()).decode()
for name in c['successful_logs']:assert 'code=exited, status=0/SUCCESS' in read(name),name
full=re.sub(r'\s+',' ',read('review-full-source-1.log'))
for n in [705649,705699,707592,9330130,9337056,9337150]:assert f'proofNodes={n}' in full,n
assert '1192 theorems/202 definitions; nonempty traces=1352' in full
assert 'reused=2; validated=7' in full
assert 'full axioms=[propext, Classical.choice, Quot.sound]' in full
strong=re.sub(r'\s+',' ',read('composition-strengthened-audits-1.log'))
for marker in ['fresh tower quotation: 40 actual theorem bodies; nonempty traces=39',
 'fresh source valuations: 13 actual theorem bodies; nonempty traces=12',
 'fresh compound source: 30 actual theorem bodies; nonempty traces=30',
 'compiled compound coefficient and original divisor finished: proofNodes=32257',
 'charged/uncharged difference is exactly nine',
 'checked leaf shared across both inventories, fresh per request, outer metadata removed']:
 assert marker in strong,marker
for n,k in [(0,7590),(1,11306),(2,16802)]:assert f'source valuation coordinates={n}; proofNodes={k}' in strong
assert 'no blockers' in read('composition-opus-final-3.log').lower()
owner=json.loads((p/'owner-merged.json').read_text())
assert owner['state']=='MERGED' and owner['mergeCommit']['oid']==c['owner_merge_commit']
ci=json.loads((p/'owner-ci.json').read_text())
assert ci['headSha']==owner['headRefOid'] and ci['status']=='completed' and ci['conclusion']=='success'
assert all(j['conclusion']=='success' for j in ci['jobs'])
checks=json.loads((p/'composition-metadata.json').read_text())
assert [x['name'] for x in checks]==['dag_tests','copyright','lines','dag','admissions','manifest','freshness','literals','source_literals','diff']
assert all(x['exit_code']==0 for x in checks)
assert 'Ran 12 tests' in read('composition-dag_tests.log')
for name,digest in json.loads((p/'composition-integration-inputs.json').read_text()).items():assert c['sources'][name]==digest,name
ins=json.loads((p/'inspection.json').read_text())
assert len(ins)==6 and {(x['viewport'],x['kind']) for x in ins}=={(w,k) for w in [1440,390] for k in ['api','code','provenance']}
assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in ins)
for name in c['owner_files']:
 actual=subprocess.check_output(['git','show',c['owner_merge_commit']+':'+name],cwd=root)
 assert sha(actual)==c['sources'][name],name
print(f'Verified checked source composition: {len(c["sources"])} source bindings; exact arithmetic/domain proof paths, final original-source audit, owner provenance and six manual views. Full #10358 remains incomplete.')
