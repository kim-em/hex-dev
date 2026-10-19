#!/usr/bin/env python3
"""Check source-bound enumerated progress evidence and exact code projection."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
here=Path(__file__).resolve().parent;root=next(p for p in here.parents if (p/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((here/'context.json').read_text())
assert sha((root/'reports/data/hexrcf-scalar-acceptance/context.json').read_bytes())==c['parent_context_sha256']
for p,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+p],cwd=root);assert sha(raw)==digest,p
 if args.check_head:assert sha((root/p).read_bytes())==digest,p
 before=subprocess.check_output(['git','show',c['base_commit']+':'+p],cwd=root)
 if p not in c['changed']:assert raw==before,p;continue
 s=raw.decode();old=before.decode()
 if p.startswith('adapters/'):
  for start,end in [('/-- A list of actual roots with exactly one positive window match','/-- Enumerate with the existing owner root producer'),('/-- A squarefree real head with exactly one positive window root','/-- Propose a source in an open interval')]:
   first=s.index(start);last=s.index(end,first);s=s[:first]+s[last:]
 else:
  s=s.replace('import KernelReplay.AxiomClosure\n','');first=s.index('  let roots := #[');last=s.index('\nprivate def require',first);old_first=old.index('  for name in #[``ScalarPacket.buildParts_success');old_last=old.index('\nprivate def require',old_first);s=s[:first]+old[old_first:old_last]+s[last:]
 assert s==old,p
for name,digest in json.loads((here/'manifest.json').read_text()).items():assert sha((here/name).read_bytes())==digest,name
read=lambda name:gzip.decompress((here/(name+'.gz')).read_bytes()).decode()
for name in ['source-enumeration-conformance-2.log','source-enumeration-final-integration.log']:
 assert 'code=exited, status=0/SUCCESS' in read(name),name
native=read('source-enumeration-conformance-2.log')
assert '7 actual theorem bodies rechecked; full axioms=[propext, Classical.choice, Quot.sound]' in native
assert 'six independent graph replays, ambiguous/empty/zero windows, wrong equation and duplicate-root refusals passed' in native
assert '25477 frozen bytes; six scalar graphs;' in native
log=read('source-enumeration-final-integration.log')
for number in [687781,690200,731070,6371355,6442217,8127841]:assert f'proofNodes={number}' in log,number
assert 'limit=687780' in log and '392 theorems/449 definitions; nonempty traces=811' in log
for r in json.loads((here/'source-enumeration-final-metadata.json').read_text()):assert r['exit_code']==0,r
for p,digest in json.loads((here/'source-enumeration-final-inputs.json').read_text()).items():assert c['sources'][p]==digest,p
source=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/SourceBuild.lean'],cwd=root).decode()
for name in ['select_success','select_checks','build_success','build_checked','build_checks']:assert f'theorem {name}' in source,name
assert 'roots.coverage model' in source and 'RootBuild.success model polynomial squarefree' in source
assert '∃! x : ℝ' in source
print(f'Verified {len(c["sources"])} source bindings; exact proof/audit-only projection, seven fresh bodies/standard-three axioms and native/frozen compatibility. Full #10358 remains incomplete.')
