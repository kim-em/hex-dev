from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

T = Path('/home/kim/.codex/tasks/hex-10358')
R = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10358')
V = T / 'scalar-review-render'
D = R / 'reports/data/hexrcf-sign-packet-quotation'
D.mkdir(parents=True, exist_ok=True)
sha = lambda b: hashlib.sha256(b).hexdigest()
artifacts = []

def keep(source, target, compress=False):
    raw = source.read_bytes()
    data = gzip.compress(raw, mtime=0) if compress else raw
    path = D / target
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    row = {'path': target, 'bytes': len(data), 'sha256': sha(data)}
    if compress:
        row['uncompressed_sha256'] = sha(raw)
    artifacts.append(row)

paths = ['adapters/HexRCF/RealCoefficients.lean',
         'adapters/HexRCF/RealCoefficients/RootQuote.lean',
         'adapters/HexRCF/RealCoefficients/ScalarQuote.lean',
         'adapters/HexRCF/RealCoefficients/RationalQuote.lean',
         'adapters/HexRCF/RealCoefficients/ScalarPacket.lean',
         'adapters/HexRCF/RealCoefficients/ScalarPacketQuote.lean',
         'conformance/HexRCF/SignPacketQuote.lean',
         'conformance/HexRCF/SignPacketProofs.lean',
         'HexManual/Chapters/HexRCF/RootQuote.lean', 'HexRCF/README.md',
         'conformance/HexRCF/SelectedRoot/Data.lean',
         'conformance/HexRCF/SelectedRoot/Literals.lean',
         'conformance/HexRCF/CellReplay/Algebraic/Scalars.lean',
         'conformance/HexRCF/CellReplay/Algebraic/ScalarData0.lean',
         'conformance/HexRCF/CellReplay/Algebraic/ScalarData1.lean',
         'HexRCF.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
validation = (T / 'sign-packet-final-source.txt').read_text().strip()
for path in paths:
    assert subprocess.check_output(['git', 'show', validation + ':' + path], cwd=R) == (R / path).read_bytes(), path
integration = (T / 'sign-packet-integration-3.log').read_text()
for text in ['Build completed successfully',
             '80 theorem bodies, 11 definitions', 'diagnostic traces: 81',
             'valid-graph rejection: sign; caller restored',
             'valid-graph rejection: polynomial; caller restored',
             'root-table quotation: 74 theorem bodies, 14 data definitions',
             'callback/public quotation: 65 theorem bodies, 14 definitions',
             'recursive scalar quotation: 87 theorem bodies, 5 definitions']:
    assert text in integration, text

def observation(name, success):
    raw = (T / name).read_text()
    assert success in raw, name
    return {'log': 'logs/' + name + '.gz', **{
        k: re.findall(pattern, raw)[-1] for k, pattern in [
            ('elapsed', r'Service runtime: ([^\n]+)'),
            ('cpu', r'CPU time consumed: ([^\n]+)'),
            ('memory', r'Memory peak: ([^\n]+)')]}}

observations = {
    'integration': observation('sign-packet-integration-3.log', 'Build completed successfully'),
    'render': observation('sign-packet-render-3.log', 'Build completed successfully'),
    'browser': observation('sign-packet-browser-2.log', 'Saved sign-packet desktop/narrow screenshots')}
policy = (T / 'sign-packet-memory-policy.txt').read_text()
assert all(s in policy for s in ['ActiveState=active', 'MemoryMax=34359738368', 'MemorySwapMax=0'])
for source in sorted(T.glob('sign-packet-*.log')):
    keep(source, 'logs/' + source.name + '.gz', True)
for name in ['root-table-pr-landed-ae509.json', 'root-table-ci-final-ae509.json',
             'root-table-landed-verification-ae509.json', 'root-table-landed-comment.md']:
    keep(T / name, 'prerequisite/' + name)
keep(T / 'option-reader-quote-api-1.log', 'logs/option-reader-quote-api-1.log.gz', True)
for source in sorted((T / 'sign-packet-browser-failed-1').iterdir()):
    keep(source, 'failed-browser-1/' + source.name)
for source in sorted(T.glob('sign-packet-public-*.lean')):
    keep(source, 'probes/' + source.name + '.txt')
keep(T / 'sign-packet-final-source.txt', 'validation-source.txt')
for source in [T / 'bin/run-bounded', T / 'sign-packet-browser.mjs', Path(__file__),
               T / 'sign-packet-memory-policy.txt', T / 'sign-packet-review-resolution.txt',
               T / 'sign-packet-relative-links.py',
               T / 'signature-codec-owner-request.md', V / 'ScalarReviewRender.lean', V / 'lakefile.lean']:
    keep(source, 'scripts/' + source.name + ('.txt' if source.name == 'ScalarReviewRender.lean' else ''))
opened = json.loads((T / 'sign-packet-captures-opened.json').read_text())
assert len(opened) == 4
for name, digest in opened.items():
    assert sha((V / name).read_bytes()) == digest, name
    keep(V / name, 'captures/' + name)
for name in ['sign-packet-document.json', 'sign-packet-inspection.json', 'sign-packet-section-overflow.json']:
    keep(V / name, name)
sections = json.loads((V / 'sign-packet-section-overflow.json').read_text())
assert [v['width'] for v in sections] == [1440, 390]
assert all(len(v['targets']) >= 6 and all(t['overflow'] <= 1 for t in v['targets']) for v in sections)
record = {
    'source_commit': validation, 'record_parent': head,
    'sources': {p: sha((R / p).read_bytes()) for p in paths},
    'artifacts': artifacts, 'observations': observations,
    'earlier_validation_source': {'integration1': '73776d2137c25215d8a3e3ca0a527d7c583c81ca', 'render1': '73776d2137c25215d8a3e3ca0a527d7c583c81ca', 'integration2': 'f47e495645a5fb4675b4922e0f0bc0bcaaf7c66d', 'render2': 'f47e495645a5fb4675b4922e0f0bc0bcaaf7c66d', 'browser1': 'f47e495645a5fb4675b4922e0f0bc0bcaaf7c66d', 'layout1': '6220ac42837d2c208301572abce3185f95a7fe31'},
    'prerequisite': {'pr': 10975, 'head': 'ae50996ab1a1f3ee0c71959d38eea722f48bc45c', 'squash': '6c8a9a35f83fe2e75a71247d79a7cef615126118', 'ci': 39003871439, 'job': 117312272681, 'conclusion': 'success', 'tree_matches': True, 'branch_retained': True},
    'failed_browser1': {'source': 'f47e495645a5fb4675b4922e0f0bc0bcaaf7c66d', 'overflows_px': [10, 6], 'retained_captures': 4, 'opened': ['sign-packet-narrow-value.png']},
    'proof_nodes': {'parent_and_packet': 54777, 'prepared_packet': 32815,
                    'coefficient': 966, 'one_below_consumed': 32792, 'one_below_requested': 23},
    'audit': {'theorem_bodies': 80, 'definitions': 11, 'nonempty_diagnostics': 81,
              'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
              'native_guard_unchanged': True, 'decoded_value_own_closure_requires_new_fact': True, 'legacy_Records_dependencies_excluded': True,
              'temporary_audit_copies_discarded': True,
              'body_modules': ['HexRCF.SignPacketQuote', 'HexRCF.RealCoefficients.RootQuote',
                               'HexRCF.RealCoefficients.ScalarPacket']},
    'metadata': {'dag': 0, 'copyright': 0, 'line_counts': 0, 'named_admissions': 0, 'diff_against_main': 0, 'relative_filesystem_links': 59, 'logs': 'logs/sign-packet-metadata-*-3.log.gz'},
    'public_module_acceptance': False,
    'base_umbrella_matches_main': subprocess.check_output(['git','show','6c8a9a35f83fe2e75a71247d79a7cef615126118:HexRCF.lean'],cwd=R) == (R/'HexRCF.lean').read_bytes(),
    'owner_request': 'https://github.com/kim-em/hex-dev/issues/10378#issuecomment-6230331731',
    'resources': 'One own build/browser at a time; aggregate hard32GiB/no swap/two Lean threads.',
    'commands': {
        'integration': {'cwd': str(R), 'argv': [str(T / 'bin/run-bounded'), 'lake', 'build',
            'HexRCF', 'HexRCFRealCoefficients', '+HexRCF.SignPacketProofs',
            '+HexRCF.RecursiveScalarProofs', '+HexRCF.RootTableQuote.Conformance',
            '+HexRCF.RootTableQuote.Runtime', '+HexRCF.SharedQuoteCallbackProofs',
            '+HexRCF.SharedQuoteConformance',
            '+HexRCF.ScalarQuoteConformance', '+HexRCF.RationalQuoteConformance',
            '+HexRCF.NamedConstantProofs', '+HexManual.Chapters.HexRCF.RootQuote',
            '+HexManual.Chapters.HexRCF.RootTableQuote']},
        'render': {'cwd': str(V), 'argv': [str(T / 'bin/run-bounded'), 'env',
            'LAKE_NO_CACHE=true', 'lake', 'build', '+ScalarReviewRender']},
        'browser': {'cwd': str(T), 'argv': [str(T / 'bin/run-bounded'), 'node',
            str(T / 'sign-packet-browser.mjs'), str(V)]}},
    'visual': {'captures': 4, 'all_opened': True,
               'local_targets': [len(v['targets']) for v in sections],
               'maximum_local_overflow': max(t['overflow'] for v in sections for t in v['targets']),
               'scope': 'New original sign-packet subsection only.'},
    'limitations': ['Reused-dependency validation observations, not scaling, unique DAG nodes or speedups.',
                   'Earlier exploratory failure logs are diagnostic and not all have a complete paired source snapshot.',
                   'Fully frozen public-module replay remains blocked on an owner codec equation; encoded variants reach a later Boolean boundary.',
                   'No generic source/provider/predecessor discovery, general tactic/completeness, strict deeper compiled replay or inverse/xgcd repair.']}
(D / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
for row in artifacts:
    data = (D / row['path']).read_bytes()
    assert sha(data) == row['sha256']
    if 'uncompressed_sha256' in row:
        assert sha(gzip.decompress(data)) == row['uncompressed_sha256']
print(f'Retained {len(artifacts)} verified sign-packet artifacts at {head}')
