#!/usr/bin/env python3
"""Check immutable complete-source quotation assembly evidence."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
here=Path(__file__).resolve().parent;root=next(p for p in here.parents if (p/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((here/'context.json').read_text());parent=root/'reports/data/hexrcf-enumerated-progress/context.json'
assert sha(parent.read_bytes())==c['parent_context_sha256']
for p,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+p],cwd=root);assert sha(raw)==digest,p
 if args.check_head:assert sha((root/p).read_bytes())==digest,p
 if p not in c['changed']:
  before=subprocess.check_output(['git','show',c['base_commit']+':'+p],cwd=root);assert raw==before,p
for name,digest in json.loads((here/'manifest.json').read_text()).items():assert sha((here/name).read_bytes())==digest,name
read=lambda name:gzip.decompress((here/(name+'.gz')).read_bytes()).decode()
for name in ['source-packet-assembly-core-1.log','source-packet-assembly-quote-2.log','source-packet-assembly-final-integration.log']:
 assert 'code=exited, status=0/SUCCESS' in read(name),name
log=read('source-packet-assembly-quote-2.log')
for count in [687783,690202,731072]:assert f'proofNodes={count}' in log,count
assert 'limit=687782' in log
for kind in ['descriptor binding','equation sign','coefficient law','parent model']:
 assert f'assembled source refused {kind}; metavariables and declarations restored' in log,kind
for name in ['source-packet-assembly-quote-2.log','source-packet-assembly-final-integration.log']:
 s=read(name);assert '392 theorems/449 definitions; nonempty traces=811' in s,name
log=read('source-packet-assembly-final-integration.log')
assert 'proofNodes=673461' in log and '218 theorems/179 definitions; nonempty traces=385' in log
assert 'full axioms=[propext,' in log and 'Quot.sound]' in log
for r in json.loads((here/'source-packet-assembly-final-metadata.json').read_text()):assert r['exit_code']==0,r
for p,digest in json.loads((here/'source-packet-assembly-inputs.json').read_text()).items():assert c['sources'][p]==digest,p
source=subprocess.check_output(['git','show',c['source_commit']+':adapters/HexRCF/RealCoefficients/SourceIdentityQuote.lean'],cwd=root).decode()
before=subprocess.check_output(['git','show',c['base_commit']+':adapters/HexRCF/RealCoefficients/SourceIdentityQuote.lean'],cwd=root).decode()
start=source.index('/-- Literal inputs for one source-selection request.')
rest=source[:start].removesuffix('\n')+source[source.index('end Hex.RCF.RealCoefficients.SourceIdentity',start):]
assert rest.replace('public meta import HexRCF.RealCoefficients.RootPrepare\n','')==before
section=source[source.index('def quotePacketWith'):]
for name in ['Tower.Context.codec','Tower.Context.sign','Tower.Context.signature','RootHeader.quoteWith','RootPrepare.prepareWith','quoteWith anchor packets']:assert name in section,name
assert '.build' not in section
probe=subprocess.check_output(['git','show',c['source_commit']+':conformance/HexRCF/BoundedSource/Quote.lean'],cwd=root).decode()
assert 'let .ok repeated ← RootQuote.runWith action exact' in probe
assert 'repeated.usage == result.usage' in probe and 'before.eAssignment.toList == after.eAssignment.toList' in probe
assert 'SourceIdentity.quotePacketWith' in probe
print(f'Verified source packet assembly: {len(c["sources"])} sources, exact/below budgets, four terminal refusals with state restoration and two fresh proof audits. Full #10358 remains incomplete.')
