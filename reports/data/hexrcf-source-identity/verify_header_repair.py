#!/usr/bin/env python3
"""Verify that the tracked-file copyright repair changes only two comments."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
repo = root.parents[2]
subprocess.run([sys.executable, str(root / 'verify.py')], check=True)
record = json.loads((root / 'context.json').read_text())
repair = json.loads((root / 'header-repair.json').read_text())
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)
assert repair['original_source_commit'] == record['source_commit']
expected = {'conformance/HexRCF/SourceIdentityControls.lean',
            'conformance/HexRCF/SourceIdentityPacket.lean'}
assert set(repair['changed']) == expected
header = ('/-\nCopyright (c) 2026 Lean FRO, LLC. All rights reserved.\n'
          'Released under Apache 2.0 license as described in the file LICENSE.\n'
          'Authors: Kim Morrison\n-/\n').encode()
assert repair['header'].encode() == header
for path in record['sources']:
    before = git('show', record['source_commit'] + ':' + path)
    after = git('show', repair['source_commit'] + ':' + path)
    assert after == (header + before if path in expected else before), path
    assert (repo / path).read_bytes() == after, path
for item in repair['artifacts']:
    assert hashlib.sha256((root / item['path']).read_bytes()).hexdigest() == item['sha256']
subprocess.run([sys.executable, 'scripts/check_copyright_headers.py'], cwd=repo, check=True)
print('Verified all 106 current sources: only the two exact copyright prefixes differ')
