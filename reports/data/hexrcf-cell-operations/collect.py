#!/usr/bin/env python3
"""Retain source-scoped complete-cell replay, quotation and manual evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys

ROOT = Path.cwd()
TASK = Path('/home/kim/.codex/tasks/hex-10358')
SCRATCH = TASK / 'boolean-render'
OUT = ROOT / 'reports/data/hexrcf-cell-operations'
RECORD = OUT / 'context.json'
SOURCE = sys.argv[1] if len(sys.argv) > 1 else json.loads(RECORD.read_text())['source_commit']
FILES = [
    'adapters/HexRCF/RealCoefficients/CellOperations.lean',
    'adapters/HexRCF/RealCoefficients/CellQuote.lean',
    'adapters/HexRCF/RealCoefficients/RealModel.lean',
    'adapters/HexRCF/RealCoefficients/CellPacketRead.lean',
    'adapters/HexRCF/RealCoefficients/RowOperations.lean',
    'adapters/HexRCF/RealCoefficients/SectorEncode.lean',
    'adapters/HexRCF/RealCoefficients/AlgebraicCells.lean',
    'adapters/HexRCF/RealCoefficients/Reify.lean',
    'adapters/HexRCF/RealCoefficients.lean', 'HexRCF/Tactic.lean',
    'conformance/HexRCF/CellReplay/Operations.lean',
    'conformance/HexRCF/CellReplay/OperationsKernel.lean',
    'conformance/HexRCF/CellReplay/OperationsPublic.lean',
    'conformance/HexRCF/CellReplay/Assembled.lean',
    'conformance/HexRCF/CellReplay/AssembledKernel.lean',
    'conformance/HexRCF/RealModelConformance.lean',
    'conformance/HexRCF/AlgebraicPreparationCases.lean',
    'conformance/HexRCF/SelectedRoot/Data.lean',
    'conformance/HexRCF/CellReplay/Algebraic/Records.lean',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean',
    'adapters/HexRealClosureTheory/NativeRecords.lean',
    'adapters/HexRealClosureTheory/NativeAssembly.lean',
    'adapters/HexRealClosureTheory/NativeAssemblyModels.lean',
    'adapters/HexRealClosureTheory/KernelReplay.lean',
    'experiments/KernelReplay/AxiomClosure.lean',
    'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'libraries.yml',
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


def inventory(commit, strict):
    result = {}
    for name in FILES:
        try:
            raw = blob(commit, name)
        except subprocess.CalledProcessError:
            if strict:
                raise
            continue
        if strict:
            assert raw == (ROOT / name).read_bytes(), name
        result[name] = sha(raw)
    return result


sources = inventory(SOURCE, True)
final_log = TASK / 'cell-assembled-final.log'
raw = final_log.read_bytes()
for marker in [
    b'status=0/SUCCESS', b'Build completed successfully',
    b'fresh original real goal proved from actual reached-record assembly',
    b'fresh ordinary-kernel real witness checked from actual record assembly',
]:
    assert marker in raw, marker
checks = ['dag-3', 'admissions-3', 'copyright-3', 'dag-tests-3',
          'admissions-tests-3', 'literals-2', 'links-3', 'lines-4']
for check in checks:
    assert b'exit_status=0' in (TASK / ('cell-operations-model-' + check + '.log')).read_bytes(), check
inspection_path = SCRATCH / 'cell-operations-model-inspection.json'
inspection = json.loads(inspection_path.read_text())
assert len(inspection) == 8
for item in inspection:
    assert item['descendantOverflow'] == 0, item
    assert item['targetScrollWidth'] <= item['targetWidth'] + 1, item
logs = {}
patterns = ['cell-operations-*.log', 'cell-operation-quote-*.log', 'cell-assembled-*.log',
            'real-model-current-*.log', 'native-cell-assembly-*.log',
            'native-source-assembly-*.log', 'native-source-ordinary-*.log']
for path in sorted({p for pattern in patterns for p in TASK.glob(pattern)}):
    raw = path.read_bytes()
    destination = OUT / (path.name + '.gz')
    destination.write_bytes(gzip.compress(raw, mtime=0))
    status = ('success' if b'status=0/SUCCESS' in raw and b'Build completed successfully' in raw
              else 'check-success' if b'exit_status=0' in raw
              else 'interrupted' if b'code=killed' in raw else 'diagnostic')
    logs[str(destination.relative_to(ROOT))] = {
        'sha256': sha(destination.read_bytes()), 'uncompressed_sha256': sha(raw), 'status': status}
artifacts = {}
paths = [TASK / 'native-cell-assembly-source-3.lean', TASK / 'native-real-model-source-3.lean',
         TASK / 'native-cell-assembly-events-3.txt', TASK / 'native-cell-assembly-3-stack-1.log',
         TASK / 'cell-operations-model-browser.mjs', SCRATCH / 'CellOperationsRender.lean', inspection_path,
         TASK / 'bin/run-bounded', TASK / 'bin/lake-bounded',
         TASK / 'cell-assembled-live-limits.properties']
paths += sorted(TASK.glob('native-source-assembly-source-*.lean'))
paths += sorted(TASK.glob('native-source-ordinary-source-*.lean'))
paths += sorted(TASK.glob('native-source-assembly*.events'))
paths += sorted(TASK.glob('cell-assembled*.events'))
paths += sorted(SCRATCH.glob('cell-operations-model-*.png'))
for path in paths:
    name = path.name + ('.txt' if path.suffix == '.lean' else '')
    destination = OUT / name
    destination.write_bytes(path.read_bytes())
    artifacts[str(destination.relative_to(ROOT))] = sha(destination.read_bytes())
for path in sorted((TASK / 'cell-operations-overflow-1').iterdir()):
    destination = OUT / ('overflow-1-' + path.name)
    destination.write_bytes(path.read_bytes())
    artifacts[str(destination.relative_to(ROOT))] = sha(destination.read_bytes())
record = {
    'source_commit': SOURCE, 'sources_sha256': sources,
    'packet_source_commit': 'cf60237d1c9053d8f45bd8dcee5f59f27b3c0b59',
    'packet_sources_sha256': inventory('cf60237d1c9053d8f45bd8dcee5f59f27b3c0b59', False),
    'quotation_source_commit': 'f4f25d7f521d87640e6c41a1cdb74ccb7367c3c6',
    'quotation_sources_sha256': inventory('f4f25d7f521d87640e6c41a1cdb74ccb7367c3c6', False),
    'public_source_commit': '30fdfd8bf6cba84bf2164d2a221f42159a9a3655',
    'public_sources_sha256': inventory('30fdfd8bf6cba84bf2164d2a221f42159a9a3655', False),
    'repository_source_commit': 'd00786311dc609adc8b842102f09b4b27ecb726d',
    'repository_sources_sha256': inventory('d00786311dc609adc8b842102f09b4b27ecb726d', False),
    'logs': logs, 'artifacts_sha256': artifacts,
    'rendered_html_sha256': sha((SCRATCH / 'cell-operations-html/html-single/index.html').read_bytes()),
    'validation': {'complete_source_and_fresh_consumer_markers': True,
                   'direct_checked_body_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
                   'visual_inspected': [p.name for p in paths if p.suffix == '.png'],
                   'memory_bytes': 34359738368, 'swap_bytes': 0, 'lean_threads': 2,
                   'own_build_concurrency': 1,
                   'check_dag_exit_status': 0,
                   'named_admissions_exit_status': 0,
                   'copyright_exit_status': 0,
                   'dag_unit_tests_exit_status': 0,
                   'admission_unit_tests_exit_status': 0,
                   'literals_exit_status': 0,
                   'relative_links_exit_status': 0,
                   'line_counts_exit_status': 0},
    'log_scopes': {
        'native-cell-assembly-3': 'Successful packet acceptance at the packet source commit; first four appended events belong to failed attempt 2.',
        'native-source-assembly-2': 'Explicitly stopped to correct the negative-source control before expensive discovery; killed status is not completion.',
        'native-source-assembly-3': 'Packet acceptance completed, then the unannotated conversion proof failed elaborator type agreement; no source proof completed.',
        'native-source-assembly-4': 'Inline exact-target annotation and source quotation at the quotation source commit; direct body audit and refusal controls complete.',
        'native-source-assembly-5': 'Actual public quotation API and fresh consuming equality theorem at the public source commit.',
        'cell-assembled-1': 'Successful first portable repository version before refusal-test resource propagation and consumer completion-reference corrections; not final-source validation.',
        'cell-assembled-2': 'Corrected portable assembly, raw failure observation and consumer completion reference; later real-model test/manual corrections are validated by the final selection.',
        'cell-assembled-3': 'Repository source selection: cached assembled source/consumer proofs, rebuilt real-model controls and manual, before the narrow-page code layout correction.',
        'cell-assembled-final': 'Final source selection including the narrow-page correction; source and fresh-consumer proofs are cached and both completion markers are present.',
        'other_diagnostic_logs': 'Intermediate source versions, failures or narrower selections; not final-source validations.',
    },
    'limits': ['Selected source inventory; the commit pins the tree and Lake manifest pins external dependencies.',
               'One fixed retained depth-one fixture, not general source/provider/predecessor history reconstruction.',
               'No public Codec.readGraph exposure or strict compiled arbitrary-missing-record rejection is established.',
               'Incremental builds and targeted assembly observations are not speedup comparisons or algorithm scaling.'],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-cell-operations.md', 'HexRCF/README.md',
             'reports/data/hexrcf-cell-operations/collect.py']
try:
    current = {p: blob(head, p) for p in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    current = {}
if current and all(current[p] == (ROOT / p).read_bytes() for p in current):
    record['document_commit'] = head
    record['documents_sha256'] = {p: sha(current[p]) for p in documents}
    record['artifact_commit'] = head
RECORD.write_text(json.dumps(record, indent=2) + '\n')
print(SOURCE, len(sources), 'sources;', len(logs), 'logs;', len(artifacts), 'artifacts')
