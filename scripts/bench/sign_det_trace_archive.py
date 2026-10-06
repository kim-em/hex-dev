"""Check diagnostic archives without relying on ephemeral PR commits."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def check_retained(path):
    path = Path(path)
    meta = json.loads(path.with_name('metadata.json').read_text())
    if hashlib.sha256(path.read_bytes()).hexdigest() != meta['observationsSha256']:
        raise ValueError('retained output hash mismatch')
    source = meta['sourcePatch']
    if source['file'] != 'source.patch':
        raise ValueError('invalid source archive path')
    patch = path.with_name(source['file']).read_bytes()
    if hashlib.sha256(patch).hexdigest() != source['sha256']:
        raise ValueError('retained source patch hash mismatch')
    # baseRevision is on main. The checked-in patch survives squash merges
    # and automatic deletion of the original head branch.
    with tempfile.TemporaryDirectory() as folder:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(folder)/'index'))
        subprocess.run(['git','read-tree',meta['baseRevision']], cwd=ROOT,env=env,check=True)
        subprocess.run(['git','apply','--cached','--unidiff-zero'],input=patch,
                       cwd=ROOT,env=env,check=True,capture_output=True)
        for name, expected in meta['sourceSha256'].items():
            blob = subprocess.run(['git','show',':'+name],cwd=ROOT,env=env,
                                  capture_output=True,check=True).stdout
            if hashlib.sha256(blob).hexdigest() != expected:
                raise ValueError('retained source hash mismatch')
    # This identifies the local executable, not cross-host byte identity.
    digest = meta['binarySha256']
    if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
        raise ValueError('invalid recorded binary hash')
