"""Tamper controls for the retained build checker; no native executions."""
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
    root = Path(temporary) / 'repo/reports/ordered-fn-declaration-review/core-runtime'
    shutil.copytree(SOURCE, root)
    comparison = root.parents[1] / 'bench-results/ordered-fn-final-comparison'
    comparison.parent.mkdir()
    shutil.copytree(SOURCE.parents[1] / 'bench-results/ordered-fn-final-comparison', comparison)

    def run(expected=None):
        result = subprocess.run([sys.executable, str(root / 'check.py')], capture_output=True, text=True)
        if expected is None:
            assert result.returncode == 0, result.stderr
        else:
            assert result.returncode != 0 and expected in result.stderr, result.stderr

    def change(name, edit):
        path = root / (name + '.gz')
        original = path.read_bytes()
        record = json.loads(gzip.decompress(original))
        edit(record)
        data = (json.dumps(record, indent=2) + '\n').encode()
        compressed = gzip.compress(data, mtime=0)
        path.write_bytes(compressed)
        manifest = root / 'manifest.json'
        saved = manifest.read_bytes()
        entries = json.loads(saved)
        entry = next(e for e in entries['files'] if e['path'] == path.name)
        entry.update(raw_sha256=hashlib.sha256(data).hexdigest(),
                     gzip_sha256=hashlib.sha256(compressed).hexdigest(), raw_bytes=len(data))
        manifest.write_text(json.dumps(entries))
        return lambda: (path.write_bytes(original), manifest.write_bytes(saved))

    run()  # Archive validation needs neither a Git checkout nor current source inputs.
    reset = change('candidate-source.json', lambda d: d.update(binary_sha256='wrong'))
    run('measured executable identity'); reset()
    reset = change('candidate-source.json', lambda d: d.update(head='wrong'))
    run('unchanged build inputs'); reset()
    path = comparison / 'capture/candidate-source.json.gz'
    saved = path.read_bytes(); path.write_bytes(saved + b'changed')
    run('measured record compressed binding'); path.write_bytes(saved)
    path = root / 'candidate-verify.stdout.gz'
    saved = path.read_bytes(); path.write_bytes(saved + b'changed')
    run('compressed binding'); path.write_bytes(saved)
    run()
print('PASS: standalone archive, altered executable/source, unauthenticated measured record and corrupted verification refusal controls.')
