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
assert 'Build completed successfully (' in log('integration')
for text in ['continued cell finishing exact/below/source budgets, bindings and rollback checked: proofNodes=7430; sourceNodes=250',
             'prepared finishing refused zero/cancelled divisors despite valid source equivalences',
             'joint replay and original-source finishing proofNodes=448469',
             '163 theorems/43 definitions; nonempty traces=170']:
    assert text in log('component'), text
for text in ['complete original-source attempt consumed proofNodes=8651669',
             '1193 theorems/202 definitions; nonempty traces=1353',
             '1247 theorems/101 definitions; nonempty traces=1298']:
    assert text in log('integration'), text
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {x['name'] for x in metadata} == {'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(x['exit_code'] == 0 for x in metadata)
invocation = json.loads(read('validation/cell-finish-expanded-invocation.json.gz'))
targets = read('validation/cell-finish-expanded-targets.txt.gz').splitlines()
assert len(set(targets)) == len(targets) == 47
assert invocation['argv'][1:] == ['build', *targets]
assert {'HexManual', 'HexRCFRealCoefficients', 'HexRCF.CellSourceProofs', 'HexRCF.CellFinishCases', 'HexRCF.CellFinishProofs'} <= set(targets)
memory = read('validation/cell-finish-memory-policy.txt.gz')
assert all(x in memory for x in ['ActiveState=active', 'MemoryMax=34359738368', 'MemorySwapMax=0', 'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
kinds = ['source', 'api', 'apicode']
assert {(x['label'], x['kind']) for x in inspection} == {(a, b) for a in ['desktop', 'narrow'] for b in kinds}
assert all(x['descendantOverflow'] == 0 and x['targetScrollWidth'] <= x['targetWidth'] + 1 for x in inspection)
review = json.loads((root / 'captures/visual-review.json').read_text())
assert len(review['captures']) == 6
for item in review['captures']:
    assert item['viewed'] and sha((root / item['path']).read_bytes()) == item['sha256']
assert len(record['compiled_files']) == 6 and all(x['bytes'] > 0 for x in record['compiled_files'])
inputs = json.loads(read('diagnostics/cell-finish-expanded-1-inputs.json.gz'))
manual = 'HexManual/Chapters/HexRCF/AlgebraicCells.lean'
for name, digest in inputs.items():
    if name != manual:
        assert record['sources'][name] == digest, name
original = read('diagnostics/cell-finish-expanded-1-inputs/' + manual + '.gz')
wrapped = original.replace('    (source :\n      Hex.RCF.RealCoefficients.Reify.Source)',
                           '    (source : Reify.Source)').replace(
    '    (target checker accepted model identity : Expr)',
    '    (target checker accepted : Expr)\n    (model identity : Expr)')
assert git('show', record['source_commit'] + ':' + manual).decode() == wrapped
print(f'Verified {len(record["artifacts"])} artifacts/{len(record["sources"])} sources; '
      '47 targets/manual, continued source-finishing budgets and 6 inspected captures; '
      'general source/history assembly and the full tactic remain incomplete')
