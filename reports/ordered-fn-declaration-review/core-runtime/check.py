"""Check the post-merge build's identity without executing native benchmarks."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--current', action='store_true', help='also require all frozen current-tree inputs')
args = parser.parse_args()

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[2]
sha = lambda data: hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


manifest = json.loads((ROOT / 'manifest.json').read_text())
raw = {}
for entry in manifest['files']:
    path = Path(entry['path'])
    require(len(path.parts) == 1 and path.suffix == '.gz', 'archive path')
    require(str(path) not in raw, 'duplicate archive path')
    compressed = (ROOT / path).read_bytes()
    require(sha(compressed) == entry['gzip_sha256'], 'compressed binding')
    data = gzip.decompress(compressed)
    require(sha(data) == entry['raw_sha256'] and len(data) == entry['raw_bytes'], 'raw binding')
    raw[str(path)] = data
require(set(raw) == {p.name for p in ROOT.glob('*.gz')}, 'complete archive')
read = lambda name: json.loads(raw[name + '.gz'])
build = read('candidate-source.json')
before = read('candidate-inputs-before.json')
require(before == read('candidate-inputs-after.json') and
        all(build[key] == value for key, value in before.items()), 'unchanged build inputs')
require(build['head'] == manifest['build_source'] and build['status'] == '' and
        build['build_result'] == 'success' and build['inputs_unchanged'] and
        not build['measurements_collected'], 'clean build')
require(len(build['sources']) == manifest['bound_inputs'] == 5172 and
        len(build['packages']) == manifest['package_count'] == 16, 'source coverage')
comparison = REPOSITORY / 'reports/bench-results/ordered-fn-final-comparison'
comparison_manifest = json.loads((comparison / 'manifest.json').read_text())


def measured_record(name):
    path = 'capture/' + name + '.gz'
    entries = [entry for entry in comparison_manifest['files'] if entry['path'] == path]
    require(len(entries) == 1, 'measured record inventory')
    entry = entries[0]
    compressed = (comparison / path).read_bytes()
    require(sha(compressed) == entry['gzip_sha256'], 'measured record compressed binding')
    data = gzip.decompress(compressed)
    require(sha(data) == entry['raw_sha256'] and len(data) == entry['raw_bytes'],
            'measured record raw binding')
    return json.loads(data)


measured = measured_record('candidate-source.json')
require(measured['head'] == manifest['measured_source'] == comparison_manifest['candidate_source'],
        'measured source identity')
require(build['command'] == measured['command'], 'native build command')
expected_names = {work['name'] for work in measured_record('schedule.json')['workloads']}
listed = {line.split()[0] for line in raw['candidate-list.stdout.gz'].decode().splitlines()
          if line.startswith('  Hex.')}
verified = {line.split()[-1] for line in raw['candidate-verify.stdout.gz'].decode().splitlines()
            if line.startswith('  [ok ] ')}
require(listed == verified == expected_names and len(expected_names) == 17 and
        raw['candidate-verify.stdout.gz'].decode().rstrip().endswith('all 17 benchmark(s) passed') and
        not raw['candidate-list.stderr.gz'] and not raw['candidate-verify.stderr.gz'],
        'native list/verify coverage')
require(build['binary_sha256'] == measured['binary_sha256'] == manifest['binary_sha256'],
        'measured executable identity')
require(build['sdk'] == measured['sdk'] and build['packages'] == measured['packages'] and
        build['native_import_closure'] == measured['native_import_closure'] and
        len(build['native_import_closure']['files']) == manifest['native_files'] == 89,
        'SDK, pin and native import identity')
require(set(build['generated_code']) == set(measured['generated_code']) == {'Infinitesimal', 'Bench'},
        'complete generated-code identity')
require(build['sources']['lakefile.lean'] == manifest['lakefile']['current_sha256'] and
        measured['sources']['lakefile.lean'] == manifest['lakefile']['measured_sha256'],
        'archived configuration binding')
for key, entry in build['generated_code'].items():
    require(sha(raw[entry['capture'] + '.gz']) == entry['sha256'] ==
            measured['generated_code'][key]['sha256'], 'native code identity')
if args.current:
    for path, expected in build['sources'].items():
        require(sha((REPOSITORY / path).read_bytes()) == expected, 'current input: ' + path)
    tracked = subprocess.check_output(['git', 'ls-files'], cwd=REPOSITORY, text=True).splitlines()
    selected = {path for path in tracked if Path(path).suffix in {'.lean', '.c', '.h', '.cpp', '.hpp'}
                or Path(path).name in {'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}}
    require(selected <= set(build['sources']), 'new unbound source input')
    for name, pin in build['packages'].items():
        directory = REPOSITORY / '.lake/packages' / name
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        status = subprocess.check_output(['git', 'status', '--porcelain'], cwd=directory, text=True).strip()
        require(head == pin['head'] and status == '', 'current package: ' + name)
    require(sha((REPOSITORY / 'lakefile.lean').read_bytes()) == manifest['lakefile']['current_sha256'],
            'current configuration binding')
print('PASS: 11 build records; 5172 bound inputs; 89 native files; 16 pins; identical measured executable/SDK/generated C; no measurements.' + (' Current inputs/pins also match.' if args.current else ''))
