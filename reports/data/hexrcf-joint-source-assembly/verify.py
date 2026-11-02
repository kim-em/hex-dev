#!/usr/bin/env python3
"""Verify same-request source and goal quotation evidence, retaining scope."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,re
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if (x/'.git').exists())
a=argparse.ArgumentParser();a.add_argument('--check-head',action='store_true');args=a.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
c=json.loads((p/'context.json').read_text())
assert sha((root/'reports/data/hexrcf-source-packet-assembly/context.json').read_bytes())==c['parent_context_sha256']
for name,digest in c['sources'].items():
 raw=subprocess.check_output(['git','show',c['source_commit']+':'+name],cwd=root);assert sha(raw)==digest,name
 if args.check_head:assert sha((root/name).read_bytes())==digest,name
 if name not in c['changed']:assert raw==subprocess.check_output(['git','show',c['base_commit']+':'+name],cwd=root),name
for name,digest in json.loads((p/'manifest.json').read_text()).items():assert sha((p/name).read_bytes())==digest,name
read=lambda name:gzip.decompress((p/(name+'.gz')).read_bytes()).decode()
for name in ['joint-source-assembly-quote-3.log','joint-source-assembly-final-integration.log','joint-source-assembly-render-1.log','joint-source-assembly-browser-1.log']:
 assert 'code=exited, status=0/SUCCESS' in read(name),name
quote=read('joint-source-assembly-quote-3.log')
for count in [705636,707529,9330067,9337220,9337314]:assert f'proofNodes={count}' in quote,count
assert 'reused=2; validated=7' in quote
final=read('joint-source-assembly-final-integration.log')
assert '1191 theorems/202 definitions; nonempty traces=1351' in final
assert '392 theorems/449 definitions; nonempty traces=811' in final
assert '218 theorems/179 definitions; nonempty traces=385' in final
for count in [687783,690202,731072,673461]:assert f'proofNodes={count}' in final,count
assert 'limit=687782' in final and '25477 frozen bytes; six scalar graphs;' in final
assert '7 actual theorem bodies rechecked' in final
for r in json.loads((p/'joint-source-assembly-final-metadata.json').read_text()):assert r['exit_code']==0,r
for name,digest in json.loads((p/'joint-source-assembly-final-inputs.json').read_text()).items():assert c['sources'][name]==digest,name
for name,digest in json.loads((p/'joint-source-assembly-quote-3-inputs.json').read_text()).items():assert c['sources'][name]==digest,name
get=lambda revision,name:subprocess.check_output(['git','show',revision+':'+name],cwd=root).decode()
source=get(c['source_commit'],'conformance/HexRCF/CellSourceQuote.lean');old=get(c['base_commit'],'conformance/HexRCF/CellSourceQuote.lean')
start='    let target : Q(Prop) := q(∃ x : ℝ';end='    let basic : Hex.RealFormula.Reify.Config'
assert source[source.index(start):source.index(end)]==old[old.index(start):old.index(end)]
for name in ['SourceIdentityPacket.coefficient','SourceIdentityPacket.selected']:assert name not in source,name
for name in ['SourceIdentity.restorePacketWith','Tower.Model.root_generator','let coefficient ← sourceCoefficient']:assert name in source,name
assert source.index('let coefficient ← sourceCoefficient') < source.index('let p ← ScalarQuote.quotePolyWith')
audit=get(c['source_commit'],'conformance/HexRCF/CellSourceProofs.lean');prior=get(c['base_commit'],'conformance/HexRCF/CellSourceProofs.lean')
def names(text,first,last):
 return set(re.findall(r'``([A-Za-z0-9_.]+)',text[text.index(first):text.index(last,text.index(first))]))
assert names(prior,'  for forbidden in #[','  let names :=') <= names(audit,'  for forbidden in #[','  let names :=')
for name in ['Hex.RCF.SourceIdentityPacket.coefficient','Hex.RCF.SourceIdentityPacket.selected']:assert name in names(audit,'  for forbidden in #[','  let names :='),name
assert '``Tower.Model.root_generator' in audit and '``ScalarPacket.restore' in audit
assert 'theorems == 1191 && definitions == 202 && traces == 1351' in audit
assert 'complete source inventory changed: 1191/202/1351' in read('joint-source-assembly-audit-1.log')
helper=get(c['source_commit'],'adapters/HexRCF/RealCoefficients/SourceIdentityQuote.lean');before=get(c['base_commit'],'adapters/HexRCF/RealCoefficients/SourceIdentityQuote.lean')
marker='/-- Literal inputs for one source-selection request.'
assert helper[:helper.index(marker)]==before[:before.index(marker)]
assert 'def restorePacketWith' in helper and 'return (← restorePacketWith anchor packet parent model decode).identity' in helper
ins=json.loads((p/'inspection.json').read_text());assert len(ins)==6
assert {(x['viewport'],x['kind']) for x in ins}=={(width,kind) for width in [1440,390] for kind in ['source','budget','audit']}
assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in ins)
print(f'Verified joint source/goal quotation: {len(c["sources"])} sources, unchanged original target, prior source identities forbidden, 1191/202/1351 actual body audit, scoped compatibility and six manual captures. Full #10358 remains incomplete.')
