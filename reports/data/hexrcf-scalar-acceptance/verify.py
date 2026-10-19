#!/usr/bin/env python3
"""Verify immutable accepted-source proof composition and scoped validation."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
here=Path(__file__).resolve().parent;root=next(p for p in here.parents if (p/'.git').exists())
parser=argparse.ArgumentParser();parser.add_argument('--check-head',action='store_true');args=parser.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((here/'context.json').read_text());parent=root/'reports/data/hexrcf-bounded-source/progress'
assert sha((parent/'context.json').read_bytes())==c['parent_context_sha256']
subprocess.run(['python3',str(parent/'verify.py')],cwd=root,check=True,stdout=subprocess.DEVNULL)
previous=json.loads((parent/'context.json').read_text())
for path,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+path],cwd=root)
 assert sha(raw)==digest,path
 if args.check_head:assert sha((root/path).read_bytes())==digest,path
 if path not in c['changed']:
  if path in previous['sources']:assert digest==previous['sources'][path],path
  continue
 s=raw.decode();before=subprocess.check_output(['git','show',c['base_commit']+':'+path],cwd=root).decode()
 if path.endswith('ScalarPacket.lean'):
  for line in ['public import HexSignDet.DagBounds\n','public import HexSignDet.Codec.GraphLaws\n','public import HexSignDet.Codec.FiniteGraph\n']:s=s.replace(line,'')
  a=s.index('/-- The wire key retains');b=s.index('/-- A produced scalar proposal retains the sign',a);s=s[:a]+s[b:]
  a=s.index('/-- Checked selected-sign evidence passes literal scalar replay');b=s.index('/-- The fallback is unobservable',a);s=s[:a]+s[b:]
 elif path.endswith('SourceBuild.lean'):
  s=s.replace('public import HexRCF.RealCoefficients.SourceIdentity\n','')
  for first,last in [('/-- Successful singleton selection retains','/-- Enumerate with'),('/-- Actual bounded production implies','/-- An ordinary-real count-one domain'),('/-- Valid count-one real inputs yield','end Hex.RCF.RealCoefficients.SourceBuild')]:
   a=s.index(first);b=s.index(last,a);s=s[:a]+s[b:]
 else:
  a=s.index('  let roots := #[');b=s.index('  let axioms ←',a);olda=before.index('  let roots := #[');oldb=before.index('  let axioms ←',olda);s=s[:a]+before[olda:oldb]+s[b:]
  s=s.replace('bounded source progress: {roots.size} actual theorem bodies','bounded source progress: three actual theorem bodies')
 assert s==before,path
for path,digest in c['artifacts'].items():assert sha((here/path).read_bytes())==digest,path
read=lambda name:gzip.decompress((here/(name+'.gz')).read_bytes()).decode()
for name in ['scalar-acceptance-integration-1.log','scalar-acceptance-integration-2.log']:
 assert 'code=exited, status=0/SUCCESS' in read(name),name
log=read('scalar-acceptance-integration-2.log')
assert '11 actual theorem bodies rechecked; full axioms=[propext, Classical.choice, Quot.sound]' in log
assert '25477 frozen bytes; six scalar graphs;' in log
for nodes in [687781,690200,731070,673461]:assert f'proofNodes={nodes}' in log
assert 'limit=687780' in log
assert '392 theorems/449 definitions; nonempty traces=811' in log
assert '218 theorems/179 definitions; nonempty traces=385' in log
assert 'fresh complete-packet source body rechecked' in log
assert 'fresh algebraic source body rechecked' in log
for result in json.loads((here/'scalar-acceptance-final-metadata.json').read_text()):assert result['exit_code']==0,result
inv=json.loads((here/'scalar-acceptance-final-invocation.json').read_text());assert len(inv['argv'][3:])==6
for path,digest in json.loads((here/'scalar-acceptance-final-inputs.json').read_text()).items():assert c['sources'][path]==digest,path
scalar=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/ScalarPacket.lean'],cwd=root).decode()
section=scalar[scalar.index('theorem read_checked'):scalar.index('/-- A produced packet passes independent literal replay')]
assert 'value.Lawful' not in section and 'value.Covers' in section
assert 'Codec.read_graph_covered' in section and 'Codec.Shape.of_validate validated' in section
build=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/SourceBuild.lean'],cwd=root).decode()
assert 'theorem buildOn_identify' in build and 'apply SourceIdentity.identify' in build
assert 'result.root.raw = ⟨parent.signature,polynomial,lower,upper,[],[]⟩' in build
print(f'Verified accepted sources: {len(c["sources"])} source bindings/{len(c["artifacts"])} artifacts; finite codec coverage, exact subjects, eleven fresh bodies/standard-three axioms, six-target compatibility; full #10358 incomplete')
