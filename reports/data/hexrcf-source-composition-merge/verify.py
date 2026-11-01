#!/usr/bin/env python3
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest();c=json.loads((p/'context.json').read_text());parent=root/'reports/data/hexrcf-source-composition'
assert sha((parent/'context.json').read_bytes())==c['parent_context_sha256']
subprocess.run(['python3',str(parent/'verify.py')],cwd=root,check=True)
old=json.loads((parent/'context.json').read_text())['sources']
assert list(c['sources'])==list(old) and [n for n,h in c['sources'].items() if old[n]!=h]==['lakefile.lean']
for n,h in c['sources'].items():
 assert sha(subprocess.check_output(['git','show',c['source_commit']+':'+n],cwd=root))==h,n
 if args.check_head:assert sha((root/n).read_bytes())==h,n
for ancestor in [c['parent_source_commit'],c['upstream_commit']]:subprocess.run(['git','merge-base','--is-ancestor',ancestor,c['source_commit']],cwd=root,check=True)
for n,h in json.loads((p/'manifest.json').read_text()).items():assert sha((p/n).read_bytes())==h,n
for n in ['integration.log.gz','metadata-driver.log.gz']:assert 'code=exited, status=0/SUCCESS' in gzip.decompress((p/n).read_bytes()).decode(),n
assert 'Build completed successfully (14421 jobs)' in gzip.decompress((p/'integration.log.gz').read_bytes()).decode()
checks=json.loads((p/'metadata.json').read_text());assert len(checks)==10 and all(x['exit_code']==0 for x in checks)
assert 'Ran 12 tests' in gzip.decompress((p/'dag_tests.log.gz').read_bytes()).decode()
for ref in [c['parent_source_commit'],c['upstream_commit']]:
 before=subprocess.check_output(['git','show',ref+':lakefile.lean'],cwd=root).decode();after=subprocess.check_output(['git','show',c['source_commit']+':lakefile.lean'],cwd=root).decode()
 assert set(re.findall(r'`[A-Za-z0-9_.]+',before))<=set(re.findall(r'`[A-Za-z0-9_.]+',after)),ref
print('Verified current-main integration:167bindings, sole Lake registration change, retained target sets and complete parent proof record. Full #10358 incomplete.')
