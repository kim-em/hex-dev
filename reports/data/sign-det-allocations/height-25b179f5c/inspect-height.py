"""Record a post-capture validation of the retained height inputs and binary."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument('--worktree', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
os.chdir(args.worktree)
sys.path.insert(0, str(args.worktree))
from scripts.bench.sign_det_sparse import source_hashes

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

out = args.output
meta = json.loads((out / 'metadata.json').read_text())
exe = args.worktree / '.lake/build/bin/hexsigndet_bench'
def sources():
    return source_hashes() | {name: digest(Path(name)) for name in meta['collector_sha256']}

record = {'scope': 'post-capture input validation; hashes are not capture-time provenance',
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'script_sha256': digest(Path(__file__)),
          'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
          'git_status': subprocess.check_output(['git', 'status', '--porcelain'], text=True),
          'source_sha256_before': sources(), 'binary_sha256_before': digest(exe)}
assert record['revision'] == meta['revision'] and record['git_status'] == ''
assert record['source_sha256_before'] == meta['source_sha256']
assert record['binary_sha256_before'] == meta['binary_sha256']
record['command'] = [str(exe), 'inspect-height-phases']
result = subprocess.run(record['command'], capture_output=True, text=True)
log = out / 'height-inspection.pending.log'
with log.open('x') as stream:
    stream.write(result.stdout + result.stderr)
record.update(exit_code=result.returncode, log_sha256=digest(log))
result.check_returncode()
inputs = [json.loads(line) for line in result.stdout.splitlines()]
assert [row['height'] for row in inputs] == meta['parameters']
for sample in meta['samples']:
    row = next(row for row in inputs if row['height'] == sample['parameter'])
    key = 'productionResultHash' if sample['function'].endswith('runReduce') else 'replayResultHash'
    assert sample['result_hash'] == hex(row[key])
record.update(source_sha256_after=sources(), binary_sha256_after=digest(exe),
              finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
assert record['source_sha256_after'] == meta['source_sha256_after']
assert record['binary_sha256_after'] == meta['binary_sha256_after']
pending = out / 'height-inspection.pending.json'
with pending.open('x') as stream:
    stream.write(json.dumps(record, indent=2) + '\n')
log.replace(out / 'height-inspection.log')
pending.replace(out / 'height-inspection.json')
print('Post-capture validation passed with complete source and binary bindings')
