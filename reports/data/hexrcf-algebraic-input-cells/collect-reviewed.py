#!/usr/bin/env python3
"""Retain separate main-integration, revised proof and displayed-manual evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path.cwd()
SCRATCH = Path('/home/kim/.codex/tasks/hex-10358')
OUT = ROOT / 'reports/data/hexrcf-algebraic-input-cells'
SOURCE = '9336360f98e5690b6a1027476061f57825fe4430'
MAIN = 'f9f3b4d054b14ed5467f0b9369460b0bf46ce4de'
RENDER = '0a268ebb3105ccc613f6710d969262aadee24cf1'
SOURCES = [
    'adapters/HexRCF/RealCoefficients/AlgebraicCells.lean',
    'adapters/HexRCF/RealCoefficients/GatherCells.lean',
    'adapters/HexRCF/RealCoefficients/NumberField.lean',
    'adapters/HexRCF/RealCoefficients/RootCodec.lean',
    'conformance/HexRCF/AlgebraicCellsConformance.lean',
    'conformance/HexRCF/GatherCellsConformance.lean',
    'conformance/HexRCF/CellCodecProofs.lean',
    'adapters/HexRCF/RealCoefficients.lean',
    'lakefile.lean',
    'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
    'scripts/check_dag.py',
    'scripts/libgraph.py',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean',
    'HexRCF/README.md',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


for name, needle in [
    ('algebraic-input-main-integration-1.log', b'Build completed successfully (11772 jobs)'),
    ('original-input-review-controls-1.log', b'Build completed successfully (10999 jobs)'),
    ('original-input-review-final-1.log', b'Build completed successfully (11768 jobs)'),
    ('original-input-review-integrated-1.log', b'Build completed successfully (11773 jobs)'),
    ('original-input-reviewed-manual-render-1.log', b'Build completed successfully (14296 jobs)'),
    ('original-input-reviewed-manual-browser-1.log', b'Saved original-input-reviewed desktop/narrow screenshots'),
]:
    raw = (SCRATCH / name).read_bytes()
    assert needle in raw and b'status=0/SUCCESS' in raw, name
manual = 'HexManual/Chapters/HexRCF/AlgebraicCells.lean'
assert source(SOURCE, manual) == source(RENDER, manual)
logs = {}
for pattern in ['algebraic-input-main-*.log', 'original-input-review-*.log',
                'original-input-reviewed-*.log']:
    for path in sorted(SCRATCH.glob(pattern)):
        raw = path.read_bytes()
        destination = OUT / (path.name + '.gz')
        destination.write_bytes(gzip.compress(raw, mtime=0))
        logs[destination.relative_to(ROOT).as_posix()] = {
            'sha256': digest(destination.read_bytes()),
            'uncompressed_sha256': digest(raw),
        }
artifacts = {}


def retain(path):
    destination = OUT / path.name
    shutil.copyfile(path, destination)
    artifacts[destination.relative_to(ROOT).as_posix()] = digest(destination.read_bytes())


render = SCRATCH / 'boolean-render'
for path in sorted(render.glob('original-input-reviewed-*.png')):
    retain(path)
retain(render / 'original-input-reviewed-inspection.json')
retain(SCRATCH / 'original-input-reviewed-browser.mjs')
inspection = json.loads((render / 'original-input-reviewed-inspection.json').read_text())
assert len(inspection) == 10
assert all(row['descendantOverflow'] == 0 for row in inspection)
assert all(row['targetScrollWidth'] <= row['targetWidth'] for row in inspection)
for label in ['desktop', 'narrow']:
    first = next(row for row in inspection if row['label'] == label and row['kind'] == 'api-start')
    last = next(row for row in inspection if row['label'] == label and row['kind'] == 'api-end')
    assert first['scrollY'] != last['scrollY']
    assert first['targetTop'] != last['targetTop']
record = {
    'source_commit': SOURCE,
    'sources_sha256': {p: digest(source(SOURCE, p)) for p in SOURCES},
    'main_source_commit': MAIN,
    'main_sources_sha256': {p: digest(source(MAIN, p)) for p in SOURCES},
    'render_source_commit': RENDER,
    'render_sources_sha256': {manual: digest(source(RENDER, manual))},
    'logs': logs,
    'artifacts_sha256': artifacts,
    'rendered_html_sha256': digest((render / 'full-html/html-single/index.html').read_bytes()),
    'validation': {
        'gathering_actual_bodies': 10,
        'automatic_input_actual_bodies': 12,
        'serialization_actual_bodies': 21,
        'main_selected_jobs': 11772,
        'revised_control_jobs': 10999,
        'revised_optional_manual_jobs': 11768,
        'combined_jobs': 11773,
        'renderer_jobs': 14296,
        'captures_opened': 10,
        'local_overflow_pixels': 0,
        'admission_scan_cones': 647,
        'admission_scan_modules': 1547,
        'memory_bytes': 34359738368,
        'swap_bytes': 0,
        'lean_threads': 2,
        'own_build_concurrency': 1,
    },
    'limits': [
        'The initial context is historical and predates main integration; it is not final-head evidence.',
        'Every declared algebraic input is presented and gathered; an unused irrational input can enlarge the tower.',
        'Acceptance wrappers derive guard validity from successful production; native contexts still do not establish general source-goal quotation.',
        'The exact model definition remains an import-all dependency pending an owning public equation; no owning source file is edited by this adapter.',
        'The displayed chapter bytes are identical across the renderer and subsequent owner-proof reuse source versions.',
        'API captures share a paragraph anchor; their scroll offsets and code-box bounds are distinct.',
        'The prior interrupted stress case remains without a recorded acceptance or completed timing; IR interpreter frames are visible in its samples.',
        'Build observations have different incremental scopes and are not before/after timing comparisons.',
    ],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-algebraic-input-cells.md', 'reports/hexrcf-gather-cells.md',
             'reports/data/hexrcf-algebraic-input-cells/collect-reviewed.py']
try:
    tracked = {path: source(head, path) for path in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[path] == (ROOT / path).read_bytes() for path in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {path: digest(tracked[path]) for path in documents}
    record['artifact_commit'] = head
(OUT / 'review-context.json').write_text(json.dumps(record, indent=2) + '\n')
print(SOURCE, len(SOURCES), 'sources per version;', len(logs), 'logs;', len(artifacts), 'artifacts')
