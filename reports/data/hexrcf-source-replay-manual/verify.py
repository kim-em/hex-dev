from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
for name,digest in json.loads((p/'manifest.json').read_text()).items():assert sha((p/name).read_bytes())==digest,name
c=json.loads((p/'context.json').read_text());raw=gzip.decompress((p/'manual.lean.gz').read_bytes());assert sha(raw)==c['source_sha256']
original=subprocess.check_output(['git','show',c['base_commit']+':'+c['source']],cwd=root);assert raw==original+b'\n'+(p/'paragraph.md.txt').read_bytes()
if args.check_head:assert (root/c['source']).read_bytes()==raw
for name in ['source-replay-manual-build-2.log','source-replay-manual-render-2.log','source-replay-manual-browser-1.log']:
 assert 'code=exited, status=0/SUCCESS' in gzip.decompress((p/(name+'.gz')).read_bytes()).decode(),name
ins=json.loads((p/'inspection.json').read_text());assert len(ins)==2 and {x['viewport'] for x in ins}=={390,1440};assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in ins)
assert sha((root/'reports/data/hexrcf-source-replay-dimensions/manifest.json').read_bytes())==c['measurement_manifest_sha256']
print('Verified manual-only addition, successful full manual build/render, two viewport records and unchanged measurement pin')
