"""Bind final projection checks and the packed-before/after experiment."""
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_trie_report import mean, require, source


def validate(cap, selected, original_bench, checks):
    before, after = source(cap, 'before'), source(cap, 'after')
    require(after == selected and before['compilers'] == after['compilers'] and
            before['native_options'] == after['native_options'], 'before/after controls differ')
    a, b = listing(before['source_manifest']), listing(after['source_manifest'])
    require(set(a) == set(b) and {k for k in a if a[k] != b[k]} ==
            {'HexGroebner/Elimination.lean', 'HexGroebner/EliminationKernel.lean',
             'HexGroebner/ffi/matrix_eliminate.c'}, 'before/after implementation delta differs')
    identity = checks(cap, after, True)
    status = cap.json('after/kernel-before-after-status.json')
    require(status['identity'] == identity and status['threads'] == 1 and
            status['manifest'] == {'A': before, 'B': after} and status['binary_sha256'] == status['binary_sha256_after'] ==
            {'A': before['binary_sha256']['bench'], 'B': after['binary_sha256']['bench']}, 'before/after kernel binding differs')
    rows = status['samples']
    expected = [f'complexity/knownProjectionBeforeAfter/{a}' for a in ['A', 'B']] + [
        f'matched/knownProjectionBeforeAfter/b{b}-{n}-{a}' for b in [0, 1] for n in [64, 128, 256, 512]
        for a in (['A', 'B'] if b == 0 else ['B', 'A'])]
    require([r['label'] for r in rows] == expected and len({r['cpu'] for r in rows}) == 1, 'before/after schedule differs')
    digest = cap.json('digest/status.json')
    require(digest['exit_code'] == 0 and digest['kind'] == 'projection' and
            digest['source_commit'] == before['commit'] and digest['sizes'] == [64, 65, 128, 129, 256, 257, 512, 513] and
            cap.text('digest/run.stderr') == '', 'independent digest checks differ')
    digests = {int(k): v for k, v in digest['digests'].items()}
    require({int(line.split(',')[0]): int(line.split(',')[1]) for line in cap.text('digest/run.stdout').splitlines()} == digests,
            'digest output differs')
    require(cap.read('before/root-sources/bench/HexGroebner/Bench/Projection.lean') ==
            cap.read('after/root-sources/bench/HexGroebner/Bench/Projection.lean'), 'kernel workload changed')
    points = {}
    for row in rows:
        cmd, label = row['command'], row['label']
        require(row['exit_code'] == 0 and 'Hex.Groebner.Bench.binaryProjection' in cmd and
                cmd[cmd.index('--target-inner-nanos')+1] == '4000000000', 'before/after command differs')
        result = cap.json('after/kernels/'+label+'/result.json')['results'][0]
        require(result['config']['target_inner_nanos'] == 4000000000, 'inner target was truncated')
        ps = result['points']
        require(all(p['status'] == 'ok' and not p['below_signal_floor'] and
                    int(p['result_hash'], 16) == digests[p['param']] for p in ps), 'invalid complete result or signal flag')
        if label.startswith('complexity/'):
            require([(p['trial_index'], p['param']) for p in ps] ==
                    [(t, n) for t in range(3) for n in [64, 128, 256, 512]], 'before/after complexity schedule differs')
        else:
            require(len(ps) == 1, 'before/after point differs')
            points[label] = ps[0]
    for row in original_bench.json('bench/kernel-status.json')['samples']:
        for point in original_bench.json('bench/kernels/'+row['label']+'/result.json')['results'][0]['points']:
            require(int(point['result_hash'], 16) == digests[point['param']], 'sparse-comparison digest differs')
    values = [(n, mean([points[f'matched/knownProjectionBeforeAfter/b{b}-{n}-B']['per_call_nanos']/
                       points[f'matched/knownProjectionBeforeAfter/b{b}-{n}-A']['per_call_nanos'] for b in [0, 1]]))
              for n in [64, 128, 256, 512]]
    lines = ['## Direct comparison with the previous packed provider', '',
        f'Baseline `{before["source_fingerprint"]}` backports the identical benchmark to the pre-PR packed runtime; '
        f'candidate `{after["source_fingerprint"]}` includes metadata, known-pivot projection and four-row tables. '
        'Both computation executables match their respective full-system snapshots byte for byte. This isolates the '
        'combined implementation change from the earlier packed-versus-sparse comparison, but does not separate its three components.', '',
        f'CPU {rows[0]["cpu"]}, one thread, four-second inner targets, three trial-major complexity trials and adjacent '
        'AB/BA matched samples. Every complete result hash matches an independently compiled successful rank/unit/counter '
        'check. There are no signal flags. This deliberately favorable workload selects every known head in every target; '
        'it does not measure sparse-target performance.', '',
        '| n | New packed / previous packed time |', '|---:|---:|']
    lines += [f'| {n} | {ratio:.6f} |' for n, ratio in values]
    lines += ['', 'The final runtime also passes all twelve sanitized native variants and nine required project checks '
        'with reducer-dominated permuted sugar labels, explicit single-pivot extent checks, and seeded mixed sparse/dense '
        '193/1031-column matrices in both modes, with and without labels.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '']
    return '\n'.join(lines)+'\n', identity
