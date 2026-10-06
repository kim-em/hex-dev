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
    # Only an immutable ancestor of main can survive squash/branch deletion.
    base = meta['baseRevision']
    if len(base) != 40 or any(c not in '0123456789abcdef' for c in base):
        raise ValueError('source base must be a full main commit SHA')
    main = subprocess.run(['git','merge-base','--is-ancestor',base,'origin/main'],
                          cwd=ROOT,capture_output=True)
    if main.returncode != 0:
        raise ValueError('source base is not an ancestor of main')
    def git(args, env, data=None):
        result = subprocess.run(['git',*args],input=data,cwd=ROOT,env=env,capture_output=True)
        if result.returncode:
            raise ValueError('source reconstruction failed: '+result.stderr.decode(errors='replace'))
        return result.stdout
    with tempfile.TemporaryDirectory() as folder:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(folder)/'index'))
        git(['read-tree',base],env)
        git(['apply','--cached','--unidiff-zero'],env,patch)
        for name, expected in meta['sourceSha256'].items():
            if hashlib.sha256(git(['show',':'+name],env)).hexdigest() != expected:
                raise ValueError('retained source hash mismatch')
    # This identifies the local executable, not cross-host byte identity.
    digest = meta['binarySha256']
    if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
        raise ValueError('invalid recorded binary hash')
