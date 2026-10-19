#!/usr/bin/env python3
"""Bind the corrected native-source API, compiler ordering and completed tests."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path.cwd()
TASK = Path('/home/kim/.codex/tasks/hex-10358')
RENDER = TASK / 'boolean-render'
OUT = ROOT / 'reports/data/hexrcf-algebraic-preparation'
RECORD = OUT / 'corrective-context.json'
SOURCE = sys.argv[1] if len(sys.argv) > 1 else json.loads(RECORD.read_text())['source_commit']
SOURCES = [
    'adapters/HexRCF/RealCoefficients/AlgebraicPreparation.lean',
    'adapters/HexRCF/RealCoefficients/FieldRuntime.lean',
    'adapters/HexRCF/RealCoefficients/Interpret.lean',
    'adapters/HexRCF/RealCoefficients.lean', 'HexRCF/Tactic.lean',
    'conformance/HexRCF/AlgebraicPreparationCases.lean',
    'conformance/HexRCF/AlgebraicPreparationConformance.lean',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean', 'HexRCF/README.md',
    'lakefile.lean', 'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
    'adapters/HexRealClosureTheory/FiniteBase.lean',
    'libraries.yml', 'lake-manifest.json', 'lean-toolchain',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


for path in SOURCES:
    assert blob(SOURCE, path) == (ROOT / path).read_bytes(), path
marker = b'native source identities, ordered irrational and guard-only inputs, aggregate budget and transactional refusals checked'
completion = b'native source conformance completion independently checked'
integration = (TASK / 'algebraic-preparation-review-integration-2.log').read_bytes()
assert marker in integration and completion in integration
assert b'status=0/SUCCESS' in integration
assert b'fresh complete-packet source body rechecked' in integration
assert b'fresh Boolean source body rechecked' in integration
jobs = int(re.search(rb'Build completed successfully \((\d+) jobs\)', integration).group(1))
assert jobs >= 14301
order = (TASK / 'algebraic-preparation-order-2.log').read_text()
assert 'status=0/SUCCESS' in order
chunks = order.split('[Compiler.result] size:')
body = next(c for c in chunks if 'def Hex.RCF.RealCoefficients.AlgebraicPreparation.Inputs.buildWith._redArg environment' in c)
helper = next(c for c in chunks if 'consumeBuilt._redArg result consume' in c)
assert body.index('Inputs.build environment registry') < body.index('consumeBuilt._redArg _x.')
assert helper.index('IO.CancelToken.isSet') < helper.index('consume result')
trace_source = (TASK / 'algebraic-preparation-order-trace-source-2.lean').read_text()
assert trace_source.replace('set_option trace.Compiler.result true in\n', '') == (ROOT / SOURCES[0]).read_text()
render_log = (TASK / 'algebraic-preparation-review-render-2.log').read_bytes()
browser_log = (TASK / 'algebraic-preparation-review-browser-2.log').read_bytes()
assert b'status=0/SUCCESS' in render_log and b'status=0/SUCCESS' in browser_log
inspection = json.loads((RENDER / 'algebraic-preparation-corrected-inspection.json').read_text())
assert len(inspection) == 6
for item in inspection:
    assert item['descendantOverflow'] == 0
    assert item['targetScrollWidth'] <= item['targetWidth'] + 1
    assert item['targetTop'] >= 50 and item['targetBottom'] <= 1000

logs = {}
patterns = [
    'algebraic-preparation-landed-parent-1.log',
    'algebraic-preparation-review-*.log', 'algebraic-preparation-order-*.log',
    'algebraic-preparation-resources-*.log',
]
paths = sorted({p for pattern in patterns for p in TASK.glob(pattern)})
for path in paths:
    raw = path.read_bytes()
    destination = OUT / (path.name + '.gz')
    destination.write_bytes(gzip.compress(raw, mtime=0))
    logs[destination.relative_to(ROOT).as_posix()] = {
        'sha256': digest(destination.read_bytes()), 'uncompressed_sha256': digest(raw)}
artifacts = {}
inputs = {
    'algebraic-preparation-order-source.lean.txt': TASK / 'algebraic-preparation-order-trace-source-2.lean',
    'algebraic-preparation-corrected-browser.mjs': TASK / 'algebraic-preparation-corrected-browser.mjs',
    'algebraic-preparation-review-statuses.json': TASK / 'algebraic-preparation-review-statuses.json',
    'algebraic-preparation-pr-opus-1.log': TASK / 'algebraic-preparation-pr-opus-1.log',
}
for prefix in ['algebraic-preparation-review', 'algebraic-preparation-corrected']:
    inputs[prefix + '-inspection.json'] = RENDER / (prefix + '-inspection.json')
    for label in ['desktop', 'narrow']:
        for kind in ['api-start', 'api-end', 'scope']:
            name = f'{prefix}-{label}-{kind}.png'
            inputs[name] = RENDER / name
for name, path in inputs.items():
    destination = OUT / name
    destination.write_bytes(path.read_bytes())
    artifacts[destination.relative_to(ROOT).as_posix()] = digest(destination.read_bytes())
record = {
    'source_commit': SOURCE,
    'sources_sha256': {p: digest(blob(SOURCE, p)) for p in SOURCES},
    'logs': logs, 'artifacts_sha256': artifacts,
    'rendered_html_sha256': digest((RENDER / 'native-preparation-html/html-single/index.html').read_bytes()),
    'validation': {
        'final_selected_jobs': jobs, 'own_conformance_marker': marker.decode(),
        'independent_completion_marker': completion.decode(),
        'strict_argument_before_postcheck_helper': True,
        'visual_inspected': [n for n in inputs if n.endswith('.png')],
        'memory_bytes': 34359738368, 'swap_bytes': 0,
        'lean_threads': 2, 'own_build_concurrency': 1,
    },
    'log_scopes': {
        'landed-parent-1': 'Exact old PR head b23d570a631f3afbe058433b780e7c417b17267f.',
        'review-integration-2': 'The final source commit in this record.',
        'order-2': 'The retained trace source matches the final API source except trace options.',
        'resources-3': 'Aggregate success without the completion marker: an uncaught test interrupt stopped the command. Not a completed conformance result.',
        'other_earlier_logs': 'Retained diagnostic intermediate versions, not final-source validation.',
    },
    'limits': [
        'This record supersedes the earlier checkpoint cancellation-order interpretation.',
        'The first three records retain their distinct historical source/document bindings.',
        'Build/render observations have distinct incremental scopes and are not performance comparisons.',
        'No general frozen quotation, literal authentication or strict arbitrary-missing-record compiled replay is established.',
    ],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-algebraic-preparation.md',
             'reports/data/hexrcf-algebraic-preparation/collect-corrective.py']
try:
    tracked = {p: blob(head, p) for p in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[p] == (ROOT / p).read_bytes() for p in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {p: digest(tracked[p]) for p in documents}
    record['artifact_commit'] = head
RECORD.write_text(json.dumps(record, indent=2) + '\n')
print(SOURCE, len(SOURCES), 'sources;', len(logs), 'logs;', len(artifacts), 'artifacts')
