#!/usr/bin/env python3
"""Verify immutable bounded-source production and independent-proof evidence."""
import argparse,gzip,hashlib,json,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent
root=next(p for p in here.parents if (p/'.git').exists())
def sha(raw):return hashlib.sha256(raw).hexdigest()
args=argparse.ArgumentParser();args.add_argument('--check-head',action='store_true');args=args.parse_args()
c=json.loads((here/'context.json').read_text())
parent=root/'reports/data/hexrcf-enumerated-source'
assert sha((parent/'context.json').read_bytes())==c['parent_context_sha256']
subprocess.run(['python3',str(parent/'verify.py')],cwd=root,check=True,stdout=subprocess.DEVNULL)
for path,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+path],cwd=root)
 assert sha(raw)==digest,path
 if args.check_head:assert sha((root/path).read_bytes())==digest,path
for path,digest in c['artifacts'].items():assert sha((here/path).read_bytes())==digest,path
previous=json.loads((parent/'context.json').read_text())
changed={'HexManual/Chapters/HexRCF/AlgebraicCells.lean','adapters/HexRCF/RealCoefficients/SourceBuild.lean','conformance/HexRCF/SelectedRoot/KernelCheck.lean','lakefile.lean','scripts/rcf/selected_literals.py'}
for path,digest in previous['sources'].items():
 if path not in changed:assert c['sources'][path]==digest,path
read=lambda name:gzip.decompress((here/(name+'.gz')).read_bytes()).decode()
for name in ['bounded-source-probe-1.log','bounded-source-quote-1.log','bounded-source-core-1.log','bounded-source-production-1.log','bounded-source-controls-1.log','bounded-source-integration-1.log','bounded-source-render-2.log','bounded-source-browser-1.log']:
 assert 'code=exited, status=0/SUCCESS' in read(name),name
log=read('bounded-source-controls-1.log')
for nodes in [687781,690200,731070]:assert f'proofNodes={nodes}' in log
assert 'limit=687780' in log
assert '392 theorems/449 definitions; nonempty traces=811' in log
assert c['proof_nodes']==[687781,690200,731070]
assert c['targets']==57
inv=json.loads((here/'bounded-source-integration-invocation.json').read_text())
assert len(inv['argv'][3:])==57
assert all(x in inv['argv'] for x in ['HexManual','HexRCFRealCoefficients','HexRCF.SourceBuild','HexRCF.BoundedSource','HexRCF.BoundedSource.Proofs'])
for result in json.loads((here/'bounded-source-final-metadata.json').read_text()):assert result['exit_code']==0,result
fixture=json.loads(subprocess.check_output(['git','show',c['source_commit']+':conformance-fixtures/HexRCF/bounded-source.json'],cwd=root))
assert fixture==json.loads(read('bounded-source-native.json'))
assert '25477 frozen bytes' in read('bounded-source-production-1.log')
for path,digest in c['integration_sources'].items():
 if path=='HexManual/Chapters/HexRCF/AlgebraicCells.lean':
  assert sha(gzip.decompress((here/'manual-before-final-timing.lean.gz').read_bytes()))==digest
 else:assert c['sources'][path]==digest,path
shots=json.loads((here/'bounded-source-viewed.json').read_text())
assert shots['actually_viewed'] is True and len(shots['images'])==6
for path in shots['images']:assert path in c['artifacts']
inspection=json.loads((here/'bounded-source-final-inspection.json').read_text())
assert len(inspection)==6
assert all(x['descendantOverflow']<=1 and x['targetScrollWidth']<=x['targetWidth']+1 for x in inspection)
code=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/SourceBuild.lean'],cwd=root).decode()
quote=subprocess.check_output(['git','show',c['source_commit']+':conformance/HexRCF/BoundedSource/Quote.lean'],cwd=root).decode()
assert 'RootQuote.runWith (quote literal anchor equationValue enclosureValue)' in quote
assert 'proofNodes := 24000000' not in quote
assert 'RootQuote.runWith action small' in quote
assert 'def buildOn' in code and 'Descriptor.build parent.sign parent.signature raw' in code
assert '| .error error => .error (.production error)' in code
assert '| .ok (.error error) => .error (.descriptor error)' in code
print(f"Verified bounded sources: {len(c['sources'])} source bindings/{len(c['artifacts'])} artifacts; default687781/690200/731070 nodes, rollback,392/449/811 fresh audit,57 targets and six viewed captures; full #10358 incomplete")
