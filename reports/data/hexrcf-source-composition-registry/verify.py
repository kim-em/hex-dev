#!/usr/bin/env python3
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
def sha(b):return hashlib.sha256(b).hexdigest()
def file_sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
def git_sha(ref,name):
 process=subprocess.Popen(['git','show',ref+':'+name],cwd=root,stdout=subprocess.PIPE)
 h=hashlib.sha256()
 for chunk in iter(lambda:process.stdout.read(1048576),b''):h.update(chunk)
 assert process.wait()==0,(ref,name)
 return h.hexdigest()
def show(ref,name):return subprocess.check_output(['git','show',ref+':'+name],cwd=root,text=True)
def text(name):return gzip.decompress((p/name).read_bytes()).decode()
def names(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return set(re.findall(r'`([A-Za-z0-9_.]+)',s))
def outside(s):
 for name in ['HexRCFRealCoefficients','HexConformance','HexReleaseTests']:
  start=s.index('lean_lib '+name+' where')
  m=re.search(r'^(?:(?:private )?def|lean_lib|lean_exe|extern_lib|target|package|require)\b',s[start+1:],re.M)
  end=start+1+m.start() if m else len(s)
  s=s[:start]+'<'+name+'>\n'+s[end:]
 return s
c=json.loads((p/'context.json').read_text());parent=root/'reports/data/hexrcf-source-composition-scheduling'
assert sha((parent/'context.json').read_bytes())==c['parent_context_sha256']
subprocess.run(['python3',str(parent/'verify.py')],cwd=root,check=True)
old=json.loads((parent/'context.json').read_text())['sources']
assert len(c['sources'])==167 and list(c['sources'])==list(old)
assert [n for n,h in c['sources'].items() if old[n]!=h]==c['changed_bindings']==['lakefile.lean']
for n,h in c['sources'].items():
 assert git_sha(c['source_commit'],n)==h,n
 if args.check_head:assert file_sha(root/n)==h,n
for ref in [c['parent_source_commit'],c['upstream_commit']]:subprocess.run(['git','merge-base','--is-ancestor',ref,c['source_commit']],cwd=root,check=True)
expected=set(subprocess.check_output(['git','diff','--name-only',c['upstream_parent'],c['upstream_commit']],cwd=root,text=True).splitlines())-{'lakefile.lean'}
assert set(c['upstream_files'])==expected
for n,h in c['upstream_files'].items():
 assert git_sha(c['upstream_commit'],n)==git_sha(c['source_commit'],n)==h,n
 if args.check_head:assert file_sha(root/n)==h,n
assert subprocess.check_output(['git','rev-parse',c['upstream_commit']+':lakefile.lean'],cwd=root,text=True).strip()==c['upstream_lake_blob']=='cc2c0a52713b58070188f4cfd410d1b8800bb13c'
lake=show(c['source_commit'],'lakefile.lean');up=show(c['upstream_commit'],'lakefile.lean');before=show(c['parent_source_commit'],'lakefile.lean')
assert names(lake)==names(up)|names(before) and outside(lake)==outside(up)
assert 'rcfConformanceGlobs' not in lake
suffix=lake.split('`HexRCF.SelectedRoot.Upper].map Glob.one',1)[1]
block=re.match(r'\s*\+\+\s*#\[(.*?)\]\.map Glob.one',suffix,re.S).group(1)
entries=re.findall(r'`([A-Za-z0-9_.]+)',block)
assert entries==c['isolated_conformance'] and len(entries)==len(set(entries))==67
for name in entries:assert 'conformance/'+name.replace('.','/')+'.lean' in c['sources'],name
manifest=json.loads((p/'manifest.json').read_text());assert set(manifest)=={n.name for n in p.iterdir() if n.is_file()}-{'manifest.json'}
for n,h in manifest.items():assert file_sha(p/n)==h,n
assert 'Build completed successfully (14508 jobs)' in text('integration.log.gz')
for n in ['integration.log.gz','metadata-driver.log.gz']:assert 'code=exited, status=0/SUCCESS' in text(n),n
checks=json.loads((p/'metadata.json').read_text());assert len(checks)==12 and all(x['exit_code']==0 for x in checks)
assert 'Ran 12 tests' in text('dag_tests.log.gz') and 'Ran 62 tests' in text('freshness_tests.log.gz') and '\nOK' in text('freshness_tests.log.gz')
assert 'FAIL: test_current_import_closure_and_library_ownership' in text('initial-freshness-failure.log.gz')
assert 'No such file or directory' in text('initial-link-failure.log.gz') and '/nix/store/864ny9w74d1xf5kvzd5lncjlhkdldzwi-elan-4.2.4' in text('initial-link-failure.log.gz')
assert 'no remaining blocker' in text('opus-followup.log.gz')
assert '/home/kim/.codex/tasks/hex-10358/native-linker/ld.lld' in text('linker-dry-run.log.gz')
runner=(p/'bounded-runner.sh').read_text();assert 'MemoryMax=32G' in runner and 'MemorySwapMax=0' in runner and 'LEAN_NUM_THREADS=2' in runner
probe=json.loads(subprocess.check_output(['python3',str(p/'merge-probes.py'),'--source',c['source_commit']],cwd=root,text=True))
assert probe==json.loads((p/'merge-probes.json').read_text()) and len(probe['checks'])==3
assert all(x['expected']==x['actual'] for x in probe['checks'])
print('Verified literal registry integration:167 source bindings,34 unchanged upstream files,67 isolated entries,12 repository checks,3 merge probes and the complete parent proof record. Full #10358 incomplete.')
