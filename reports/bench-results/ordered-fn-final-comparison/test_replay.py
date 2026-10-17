"""Negative controls for archived full-comparison replay; no native executions."""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

SOURCE = Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as temporary:
    root = Path(temporary) / 'evidence'
    shutil.copytree(SOURCE, root)
    reference = root.parent / 'ordered-fn-regression-followup'
    reference.mkdir()
    shutil.copy2(SOURCE.parent / 'ordered-fn-regression-followup/analyze_guard.py',
                 reference / 'analyze_guard.py')
    def refuse(expected):
        result = subprocess.run([sys.executable, str(root / 'replay.py')], capture_output=True, text=True)
        if result.returncode == 0 or expected not in result.stderr:
            raise RuntimeError('negative control did not refuse: ' + result.stderr)
    def change(name, edit):
        path = root / 'capture' / (name + '.gz')
        original = path.read_bytes()
        data = edit(gzip.decompress(original))
        compressed = gzip.compress(data, mtime=0)
        path.write_bytes(compressed)
        manifest = root / 'manifest.json'
        saved = manifest.read_bytes()
        record = json.loads(saved)
        entry = next(e for e in record['files'] if e['path'] == str(path.relative_to(root)))
        entry.update(raw_sha256=hashlib.sha256(data).hexdigest(), gzip_sha256=hashlib.sha256(compressed).hexdigest(), raw_bytes=len(data))
        manifest.write_text(json.dumps(record))
        return lambda: (path.write_bytes(original), manifest.write_bytes(saved))
    path = root / 'capture/comparison/0-scan-128-baseline.stdout.gz'
    original = path.read_bytes();path.write_bytes(original + b'changed')
    refuse('compressed binding');path.write_bytes(original)
    path = root / 'capture/extra.txt';path.write_text('unlisted')
    refuse('complete archive inventory');path.unlink()
    reset = change('comparison/observations.jsonl', lambda data: b'\n'.join(data.splitlines()[:-1]) + b'\n')
    refuse('complete ordered schedule');reset()
    def edit_json(data, edit):
        record = json.loads(data);edit(record)
        return (json.dumps(record, indent=2)+'\n').encode()
    reset = change('comparison/guard-analysis.json', lambda data: edit_json(data, lambda d: d.update(regression_count=1)))
    refuse('median analysis replay');reset()
    reset = change('comparison/context.json', lambda data: edit_json(data, lambda d: d.update(affinity_after=[-1])))
    refuse('CPU/thread selection');reset()
    reset = change('consumed-reservation.json', lambda data: edit_json(data, lambda d: d.update(decision_sha256='wrong')))
    refuse('source-pair reservation');reset()
    path = reference / 'analyze_guard.py'
    saved = path.read_bytes(); path.write_bytes(saved + b'\n')
    refuse('unchanged follow-up analyzer'); path.write_bytes(saved)
    result = subprocess.run([sys.executable, str(root / 'replay.py')], capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stderr)
print('PASS: seven independent corruption/inventory/schedule/median/affinity/reservation/analyzer refusal controls; clean archive still passes.')
