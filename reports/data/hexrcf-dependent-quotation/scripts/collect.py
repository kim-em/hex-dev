"""Bind completed dependent-quotation validation to its committed source tree."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--task-root', type=Path, required=True)
parser.add_argument('--render-root', type=Path, required=True)
parser.add_argument('--source', required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
repo = root.parents[2]

def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=repo)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def keep(source, destination):
    target = root / destination
    target.parent.mkdir(parents=True, exist_ok=True)
    raw = source.read_bytes()
    target.write_bytes(gzip.compress(raw, mtime=0) if target.suffix == '.gz' else raw)

validation = {
    'integration': 'public-packet-review-integration-3.log',
    'render': 'public-packet-review-render-1.log',
    'browser': 'public-packet-review-browser-1.log'}
for key, name in validation.items():
    text = (args.task_root / name).read_text()
    assert 'status=0/SUCCESS' in text, name
    assert ('Saved public-packet desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, name
    keep(args.task_root / name, 'validation/' + name + '.gz')
metadata = json.loads((args.task_root / 'public-packet-review-metadata-results-1.json').read_text())
assert all(item['exit_code'] == 0 for item in metadata)
keep(args.task_root / 'public-packet-review-metadata-results-1.json', 'validation/metadata.json')
for item in metadata:
    keep(args.task_root / item['log'], 'validation/' + item['log'] + '.gz')
keep(args.task_root / 'dependent-quotation-memory-policy.txt', 'validation/memory-policy.txt.gz')
keep(args.task_root / 'bin' / 'run-bounded', 'scripts/run-bounded')
for source in sorted(args.task_root.glob('public-packet-review-integration-[12].log')):
    keep(source, 'diagnostics/' + source.name + '.gz')
for pattern in ['dependent-scalar-production-*.log', 'transport-production-*.log',
                'codec-transport-review-audit-[89].log', 'codec-transport-target-only-1.log',
                'context-transport-*.log', 'multi-codec-context-*.log',
                'public-packet-pr10978-opus-1.log', 'public-packet-conversion-opus-2.log',
                'public-packet-review-fix-opus-3.log']:
    for source in sorted(args.task_root.glob(pattern)):
        keep(source, 'diagnostics/' + source.name + '.gz')
for name in ['RootQuote-before-transport-review-fix.lean.txt',
             'ContextQuote-before-multi-diagnostic.lean.txt',
             'CodecTransportProbe-recursive-callback.lean.txt',
             'CodecTransportProbe-direct-callback.lean.txt',
             'CodecTransportCases-hidden-query-type.lean.txt']:
    keep(args.task_root / name, 'diagnostics/' + name + '.gz')
for name in ['MultiCodecQuote.lean', 'MultiCodecAudit.lean',
             'CodecTransportCases.lean', 'CodecTransportAudit.lean', 'ContextQuote.lean']:
    keep(args.render_root / name, 'diagnostics/' + name + '.txt.gz')
for source in sorted(args.task_root.glob('codec-transport-*body-*.txt')):
    keep(source, 'diagnostics/' + source.name + '.gz')
for source in sorted(args.render_root.glob('public-packet-*.png')):
    keep(source, 'captures/' + source.name)
for source in sorted(args.render_root.glob('public-packet-*.json')):
    keep(source, 'captures/' + source.name)
prior = json.loads((root.parent / 'hexrcf-public-packet' / 'context.json').read_text())
paths = set(prior['sources']) | {
    'HexRCF/Tactic.lean', 'adapters/HexRCF/RealCoefficients/Reify.lean',
    'conformance/HexRCF/DependentQuoteProofs.lean',
    'conformance/HexRCF/DependentScalarQuote.lean',
    'conformance/HexRCF/DependentScalarProofs.lean'}
record = {
    'source_commit': args.source,
    'source_tree': git('rev-parse', args.source + '^{tree}').decode().strip(),
    'baseline_commit': prior['baseline_commit'],
    'previous_source_commit': prior['source_commit'],
    'sources': {path: sha(git('show', args.source + ':' + path)) for path in sorted(paths)},
    'unchanged_guards': prior['unchanged_guards'],
    'validation': {key: 'validation/' + name + '.gz' for key, name in validation.items()},
    'body_scope': {
        'conformance/HexRCF/PublicSignPacketProofs.lean': prior['body_scope'],
        'conformance/HexRCF/DependentQuoteProofs.lean': [
            'HexRCF.DependentQuote', 'HexRCF.DependentQuoteData', 'HexRCF.RealCoefficients.RootQuote'],
        'conformance/HexRCF/DependentScalarProofs.lean': [
            'HexRCF.DependentScalarQuote', 'HexRCF.RealCoefficients.RootQuote']},
    'audit_counts': {'public packet': [656, 67, 713],
                     'dependent quotation': [114, 14, 64],
                     'dependent scalar': [61, 4, 56]},
    'diagnostics': {
        'multi-codec-context-probe-6.log': 'completed diagnostic with forbidden reductions; not an acceptance audit',
        'multi-codec-context-probe-7.log': 'completed prototype diagnostic with no reported forbidden reductions',
        'public-packet-review-integration-1.log': 'cancelled after invalid target name',
        'public-packet-review-integration-2.log': 'failed only the stale public-packet inventory assertion',
        'public-packet-review-fix-opus-3.log': 'unavailable: Claude weekly limit; not a completed review'},
    'artifacts': []}
for path in sorted(root.rglob('*')):
    if not path.is_file() or path.name == 'context.json':
        continue
    raw = path.read_bytes()
    entry = {'path': path.relative_to(root).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}
    if path.suffix == '.gz':
        entry['uncompressed_sha256'] = sha(gzip.decompress(raw))
    record['artifacts'].append(entry)
(root / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(f"Retained {len(record['artifacts'])} artifacts against {len(record['sources'])} source files")
