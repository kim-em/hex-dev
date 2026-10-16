"""Verify and recompute the complete retained comparison without measurements."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import tempfile

from analyze_guard import analyze


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--current', action='store_true', help='also check current native input/configuration bytes')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'manifest.json').read_text())
    raw = {}
    for entry in manifest['files']:
        path = entry['path']
        relative = Path(path)
        require(not relative.is_absolute() and '..' not in relative.parts, 'archive path')
        require(path not in raw, 'duplicate archive entry')
        compressed = (root / path).read_bytes()
        require(sha(compressed) == entry['gzip_sha256'], 'compressed binding: ' + path)
        data = gzip.decompress(compressed)
        require(sha(data) == entry['raw_sha256'] and len(data) == entry['raw_bytes'], 'raw binding: ' + path)
        raw[path] = data
    require(set(raw) == {str(path.relative_to(root)) for path in (root / 'capture').rglob('*') if path.is_file()},
            'complete archive inventory')

    def data(path):
        return raw['capture/' + path + '.gz']

    def read(path):
        return json.loads(data(path))

    decision = read('comparison/decision.json')
    context = read('comparison/context.json')
    require(data('decision.json') == data('comparison/decision.json') and
            sha(data('decision.json')) == context['decision_sha256'], 'decision binding')
    require(data('schedule.json') == data('comparison/schedule.json') and
            sha(data('schedule.json')) == decision['schedule_sha256'], 'schedule binding')
    require(context['status'] == 'completed' and context['outcome'] == 'pass' and
            context['inputs_unchanged'] and context['failed_arms'] == 0 and context['completed_arms'] == 816,
            'complete passing capture')
    require(context['lean_num_threads'] == '4' and context['affinity_after'] == [context['cpu']] and
            context['affinity_final'] == [context['cpu']] and context['cpu'] in context['affinity_before'],
            'recorded CPU/thread selection')
    require(context['measurement_environment'] == {'LEAN_NUM_THREADS':'4', 'LEAN_BENCH_*':'unset'},
            'ordinary measurement environment')
    for filename, field in [('build-provenance.json', 'baseline_selection_record_sha256'),
                            ('benchmark-source-reconciliation.json', 'benchmark_source_reconciliation_sha256'),
                            ('proposal.json', 'proposal_sha256')]:
        require(data(filename) == data('comparison/' + filename) and sha(data(filename)) == decision[field],
                'pre-timing provenance binding: ' + filename)
    for name in ('measure.py', 'analyze_guard.py'):
        require(data(name) == data('comparison/' + name), 'executed script binding')
        hashes = [value for path, value in decision['tools'].items() if Path(path).name == name]
        require(hashes == [sha(data(name))], 'declared script hash: ' + name)
    require((root / 'analyze_guard.py').read_bytes() == data('analyze_guard.py'), 'committed comparison arithmetic')

    sources = read('comparison/sources.json')
    expected_heads = {'baseline':manifest['baseline_source'], 'candidate':manifest['candidate_source']}
    require({arm:source['head'] for arm, source in sources.items()} == expected_heads == context['source_heads'],
            'frozen source pair')
    identity = sha(json.dumps(expected_heads, sort_keys=True).encode())
    reservation = read('consumed-reservation.json')
    require(context['comparison_identity'] == identity and Path(context['reservation']).stem == identity and
            reservation['decision_sha256'] == context['decision_sha256'] and
            reservation['output'] == str(Path(next(path for path in decision['tools']
                if Path(path).name == 'measure.py')).parent / 'comparison'), 'consumed source-pair reservation')
    for arm, source in sources.items():
        require(source == read(arm + '-source.json') and
                data(arm + '-source.json') == data('comparison/' + arm + '-source.json') and
                sha(data(arm + '-source.json')) == decision['source_manifests'][arm], 'source manifest binding')
        require(context['binaries'][arm] == context['binaries_after'][arm] == source['binary_sha256'],
                'executable binding')
        before = read(arm + '-inputs-before.json')
        require(before == read(arm + '-inputs-after.json') and
                all(source[key] == value for key, value in before.items()), 'build input inventories')
        require(source['status'] == '' and source['inputs_unchanged'] and source['build_result'] == 'success' and
                all(pin['status'] == '' for pin in source['packages'].values()), 'clean pinned source build')
        require('Lean version ' + decision['compiler_versions'][arm] in source['sdk']['version_output'],
                'pinned SDK version')
        for entry in source['generated_code'].values():
            require(sha(data(entry['capture'])) == entry['sha256'], 'generated native code binding')
    provenance = read('build-provenance.json')
    require(provenance['historical_source'] == sources['baseline']['head'] and
            provenance['historical_fresh_binary_sha256'] == sources['baseline']['binary_sha256'] and
            provenance['candidate_binary_sha256'] == sources['candidate']['binary_sha256'] and
            provenance['historical_sdk'] == sources['baseline']['sdk'] and
            provenance['candidate_sdk'] == sources['candidate']['sdk'], 'fresh build provenance')

    with tempfile.TemporaryDirectory() as temporary:
        capture = Path(temporary)
        prefix = 'capture/comparison/'
        for path, content in raw.items():
            if path.startswith(prefix):
                destination = capture / path.removeprefix(prefix).removesuffix('.gz')
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(content)
        result = analyze(capture)
        require(result == read('comparison/guard-analysis.json'), 'complete median analysis replay')
    require(result['completed_arms'] == 816 and result['parameters_compared'] == 136 and
            result['regression_count'] == 0 and not result['failures'] and result['all_hashes_agree'],
            'full comparison verdict')
    rows = [json.loads(line) for line in data('comparison/observations.jsonl').splitlines()]
    hashes = {}
    schedule = read('schedule.json')
    targets = {work['name']:work['target_nanos'] for work in schedule['workloads']}
    for row in rows:
        expected = [sources[row['arm']]['binary'], '_child', '--bench', row['name'], '--param', str(row['param']),
                    '--target-nanos', str(targets[row['name']])]
        require(row['command'] == expected and row['observation']['env']['lean_version'] ==
                decision['compiler_versions'][row['arm']], 'recorded command/compiler')
        hashes.setdefault((row['name'], row['param']), set()).add(row['observation']['result_hash'])
    require(all(len(values) == 1 for values in hashes.values()), 'cross-trial result hashes')
    if args.current:
        repository = root.parents[2]
        inputs = dict(sources['candidate']['native_import_closure']['files'])
        for path in ('HexOrderedFn/Tests.lean','lakefile.lean','lake-manifest.json','lean-toolchain'):
            inputs[path] = sources['candidate']['sources'][path]
        for path, expected in inputs.items():
            require(sha((repository / path).read_bytes()) == expected, 'current native input: ' + path)
    print(f"PASS: {len(raw)} archive bindings; 816 arms; 136 comparisons; zero failures/regressions; all hashes agree.")


if __name__ == '__main__':
    main()
