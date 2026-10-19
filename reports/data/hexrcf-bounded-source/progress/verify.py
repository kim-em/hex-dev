#!/usr/bin/env python3
"""Verify the proof-only selected-source progress supplement."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
here=Path(__file__).resolve().parent
root=next(p for p in here.parents if (p/'.git').exists())
parser=argparse.ArgumentParser();parser.add_argument('--check-head',action='store_true');args=parser.parse_args()
def sha(raw):return hashlib.sha256(raw).hexdigest()
c=json.loads((here/'context.json').read_text());parent=here.parent
assert sha((parent/'context.json').read_bytes())==c['parent_context_sha256']
subprocess.run(['python3',str(parent/'verify.py')],cwd=root,check=True,stdout=subprocess.DEVNULL)
for path,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+path],cwd=root)
 assert sha(raw)==digest,path
 if args.check_head:assert sha((root/path).read_bytes())==digest,path
for path,digest in c['artifacts'].items():assert sha((here/path).read_bytes())==digest,path
previous=json.loads((parent/'context.json').read_text())
for path,digest in c['sources'].items():
 current=subprocess.check_output(['git','show',c['source_commit']+':'+path],cwd=root).decode()
 if path not in c['changed']:
  assert previous['sources'][path]==digest,path
  continue
 before=subprocess.check_output(['git','show',c['base_commit']+':'+path],cwd=root).decode()
 if path.endswith('ScalarPacket.lean'):
  first=current.index('/-- A produced scalar proposal');last=current.index('/-- Literal assembly',first)
  current=current[:first]+current[last:]
 elif path.endswith('SourceBuild.lean'):
  first=current.index('/-- A lawful selected root');last=current.index('/-- Enumerate with',first)
  current=current[:first]+current[last:]
  first=current.index('/-- An ordinary-real count-one domain');last=current.index('end Hex.RCF.RealCoefficients.SourceBuild',first)
  current=current[:first]+current[last:]
 else:
  current=current.replace('import KernelReplay.AxiomClosure\n','')
  first=current.index('  let roots := #[``ScalarPacket.buildParts_sign');last=current.index('\n\nprivate def descriptorError',first)
  current=current[:first]+current[last+1:]
 assert current==before,path
read=lambda name:gzip.decompress((here/(name+'.gz')).read_bytes()).decode()
log=read('bounded-source-progress-controls-2.log')
assert 'code=exited, status=0/SUCCESS' in log
assert 'three actual theorem bodies rechecked; full axioms=[propext, Classical.choice, Quot.sound]' in log
assert '25477 frozen bytes; six scalar graphs;' in log
for result in json.loads((here/'source-progress-metadata.json').read_text()):assert result['exit_code']==0,result
build=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/SourceBuild.lean'],cwd=root).decode()
body=build[build.index('theorem buildOn_success'):]
assert '(degree :' not in body and 'Polynomial.degree_pos_of_root domain.1 rootZero' in body
assert 'Descriptor.build_success_iff' in body
print(f'Verified source progress: {len(c["sources"])} source bindings/{len(c["artifacts"])} artifacts; three fresh theorem bodies/standard-three axioms; exact proof-only projection; frozen-byte/refusal controls; full #10358 incomplete')
