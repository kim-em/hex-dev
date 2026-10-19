#!/usr/bin/env python3
"""Retain source-scoped gathering validation; this does not run measurements."""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path.cwd()
SCRATCH = Path('/home/kim/.codex/tasks/hex-10358')
OUT = ROOT / 'reports/data/hexrcf-gather-cells'
INITIAL = '441169931169dd04428c8a0834e3ce753b6b464e'
INTERMEDIATE = '338609b7c640d056ee745f332ae672d0f80a2018'
FINAL = '0f6d6f9ddcfec2e6f387c2f1b5c1ee6aa16c3430'
SOURCES = [
    'adapters/HexRCF/RealCoefficients/GatherCells.lean',
    'adapters/HexRCF/RealCoefficients/NumberField.lean',
    'conformance/HexRCF/GatherCellsConformance.lean',
    'adapters/HexRCF/RealCoefficients.lean',
    'lakefile.lean',
    'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean',
    'HexRCF/README.md',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path])


for log, needle in [
    ('gather-cells-final-build-1.log', b'Build completed successfully (11766 jobs)'),
    ('gather-cells-source-final-1.log', b'Build completed successfully (11766 jobs)'),
    ('gather-cells-source-final-2.log', b'Build completed successfully (11766 jobs)'),
    ('gather-cells-manual-render-1.log', b'Build completed successfully (14295 jobs)'),
    ('gather-cells-manual-browser-1.log', b'Saved gather-cells desktop/narrow screenshots'),
]:
    raw = (SCRATCH / log).read_bytes()
    assert needle in raw and b'status=0/SUCCESS' in raw, log

manual = 'HexManual/Chapters/HexRCF/AlgebraicCells.lean'
assert source(INITIAL, manual) == source(FINAL, manual)
assert (ROOT / manual).read_bytes() == source(FINAL, manual)
logs = {}
for pattern in ['gather-cells-*.log', 'field-source-model-*.log', 'field-source-adapter-*.log']:
    for path in sorted(SCRATCH.glob(pattern)):
        raw = path.read_bytes()
        destination = OUT / (path.name + '.gz')
        destination.write_bytes(gzip.compress(raw, mtime=0))
        logs[destination.relative_to(ROOT).as_posix()] = {
            'sha256': digest(destination.read_bytes()),
            'uncompressed_sha256': digest(raw),
        }
artifacts = {}


def retain(path, name=None):
    destination = OUT / (name or path.name)
    shutil.copyfile(path, destination)
    artifacts[destination.relative_to(ROOT).as_posix()] = digest(destination.read_bytes())


render = SCRATCH / 'boolean-render'
for path in sorted(render.glob('gather-cells-*.png')):
    retain(path)
retain(render / 'gather-cells-inspection.json')
retain(SCRATCH / 'gather-cells-browser.mjs')
retain(SCRATCH / 'gather-cells-memory-properties.txt')
retain(SCRATCH / 'bin/run-bounded')
retain(SCRATCH / 'bin/lake-bounded')
inspection = json.loads((render / 'gather-cells-inspection.json').read_text())
assert len(inspection) == 8
assert all(row['descendantOverflow'] == 0 for row in inspection)
assert all(row['targetScrollWidth'] <= row['targetWidth'] for row in inspection)
record = {
    'initial_source_commit': INITIAL,
    'source_commit': FINAL,
    'intermediate_source_commit': INTERMEDIATE,
    'intermediate_sources_sha256': {p: digest(source(INTERMEDIATE, p)) for p in SOURCES},
    'initial_sources_sha256': {p: digest(source(INITIAL, p)) for p in SOURCES},
    'sources_sha256': {p: digest(source(FINAL, p)) for p in SOURCES},
    'logs': logs,
    'artifacts_sha256': artifacts,
    'rendered_html_sha256': digest((render / 'full-html/html-single/index.html').read_bytes()),
    'validation': {
        'initial_actual_bodies': 6,
        'intermediate_actual_bodies': 8,
        'final_actual_bodies': 9,
        'selected_build_jobs': 11766,
        'renderer_build_jobs': 14295,
        'browser_captures': 8,
        'admission_scan_cones': 643,
        'admission_scan_modules': 1543,
        'checker_unit_tests': 11,
        'memory_bytes': 34359738368,
        'swap_bytes': 0,
        'lean_threads': 2,
        'own_build_concurrency': 1,
    },
    'limits': [
        'Compiled native controls and actual theorem-body audits are distinct evidence.',
        'The initial six-proof source owns the displayed manual rendering; its text is unchanged in the later proof extension.',
        'The ordinary base model and original nonzero guards remain mathematical progress hypotheses.',
        'No frozen provider/predecessor history, arbitrary missing-record strictness, primitive common-field certification or frontend accepted completeness is inferred.',
        'Build/render observations are operational evidence, not a speedup comparison.',
    ],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-gather-cells.md',
             'reports/data/hexrcf-gather-cells/collect.py']
try:
    tracked = {path: source(head, path) for path in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[path] == (ROOT / path).read_bytes() for path in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {path: digest(tracked[path]) for path in documents}
    record['artifact_commit'] = head
(OUT / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(FINAL, len(SOURCES), 'sources per version;', len(logs), 'logs;', len(artifacts), 'artifacts')
