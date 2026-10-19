#!/usr/bin/env python3
"""Verify packet-derived selected-source authentication evidence."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-head', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = root.parents[2]
record = json.loads((root / 'context.json').read_text())
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: gzip.decompress((root / p).read_bytes()).decode()
log = lambda key: read(record['validation'][key])

assert git('rev-parse', record['source_commit'] + '^{tree}').decode().strip() == record['source_tree']
for path, digest in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + path)) == digest, path
    if args.check_head:
        assert sha((repo / path).read_bytes()) == digest, path
if args.check_head:
    paths = git('diff', '--name-only', record['source_commit']).decode().splitlines()
    paths += git('ls-files', '--others', '--exclude-standard').decode().splitlines()
    assert all(p.startswith('reports/') for p in paths), paths
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git('show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']
for key in record['validation']:
    assert 'code=exited, status=0/SUCCESS' in log(key), key
assert 'Build completed successfully (14473 jobs)' in log('integration')
for text in ['quoted source selection proofNodes=673461',
             'source identity exact/below budgets and success/failure rollback checked: 673461',
             'source identity refused wrong conjugate with complete rollback',
             'source identity refused wrong coefficient proof with complete rollback',
             '218 theorems/179 definitions; nonempty traces=385']:
    assert text in log('component'), text
for text in ['original algebraic source quotation proofNodes=8644422',
             '1192 theorems/202 definitions; nonempty traces=1352',
             'source-identity proposals match frozen packets (10284 bytes)']:
    assert text in log('integration'), text
assert 'Source identity constructor literals are current' in read('validation/constructor-check.log.gz')
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {x['name'] for x in metadata} == {'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(x['exit_code'] == 0 for x in metadata)
invocation = json.loads(read('validation/source-identity-expanded-invocation.json.gz'))
targets = read('validation/source-identity-expanded-targets.txt.gz').splitlines()
assert len(set(targets)) == len(targets) == 45
assert invocation['argv'][1:] == ['build', *targets]
assert {'HexManual', 'HexRCFRealCoefficients', 'HexRCF.CellSourceProofs', 'HexRCF.SourceIdentityProofs', 'HexRCF.SourceIdentityEmit'} <= set(targets)
memory = read('validation/source-identity-memory-policy.txt.gz')
assert all(x in memory for x in ['ActiveState=active', 'MemoryMax=34359738368', 'MemorySwapMax=0', 'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
kinds = ['source', 'sourcecode', 'api', 'apicode', 'limits', 'controls']
assert {(x['label'], x['kind']) for x in inspection} == {(a, b) for a in ['desktop', 'narrow'] for b in kinds}
assert all(x['descendantOverflow'] == 0 and x['targetScrollWidth'] <= x['targetWidth'] + 1 for x in inspection)
review = json.loads((root / 'captures/visual-review.json').read_text())
assert len(review['captures']) == 12
for item in review['captures']:
    assert item['viewed'] and sha((root / item['path']).read_bytes()) == item['sha256']
assert len(record['compiled_files']) == 6 and all(x['bytes'] > 0 for x in record['compiled_files'])
print(f'Verified {len(record["artifacts"])} artifacts/{len(record["sources"])} sources; '
      '45 targets/manual, packet-derived selected-source identity and 12 inspected captures; '
      'general source/history assembly remains incomplete')
