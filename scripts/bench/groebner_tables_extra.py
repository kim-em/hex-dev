"""Validate the retained, unselected eight-row projection experiment."""
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_trie_report import mean, require, source


def study(cap, baseline, checks):
    before, after = source(cap, 'baseline'), source(cap, 'candidate')
    require(before == baseline, 'eight-row baseline differs')
    identity = checks(cap, after, True)
    a, b = listing(before['source_manifest']), listing(after['source_manifest'])
    require(set(a) == set(b) and {k for k in a if a[k] != b[k]} ==
            {'HexGroebner/EliminationKernel.lean', 'HexGroebner/ffi/matrix_eliminate.c'}, 'eight-row runtime delta differs')
    require(before['compilers'] == after['compilers'] and before['native_options'] == after['native_options'],
            'eight-row compiler controls differ')
    results = [(label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag}))
               for label, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                                         ('prime-control', 14, None), ('prime-control-repeat', 14, None)]]
    status = cap.json('candidate/kernel-status.json')
    require(status['identity'] == identity and status['threads'] == 1 and
            status['manifest'] == {'A': before, 'B': after} and status['binary_sha256'] == status['binary_sha256_after'] ==
            {'A': before['binary_sha256']['bench'], 'B': after['binary_sha256']['bench']}, 'eight-row kernel binding differs')
    rows = status['samples']
    expected = [f'complexity/knownProjectionFourEight/{a}' for a in ['A', 'B']] + [
        f'matched/knownProjectionFourEight/b{b}-{n}-{a}' for b in [0, 1] for n in [64, 128, 256, 512]
        for a in (['A', 'B'] if b == 0 else ['B', 'A'])]
    require([r['label'] for r in rows] == expected and len({r['cpu'] for r in rows}) == 1, 'eight-row kernel schedule differs')
    points = {}
    for row in rows:
        cmd, label = row['command'], row['label']
        require(row['exit_code'] in [0, 2] and 'Hex.Groebner.Bench.binaryProjection' in cmd and
                cmd[cmd.index('--target-inner-nanos')+1] == '4000000000', 'eight-row kernel command differs')
        ps = cap.json('candidate/kernels/'+label+'/result.json')['results'][0]['points']
        require(all(p['status'] == 'ok' and p['result_hash'] is not None for p in ps), 'eight-row kernel failed')
        if label.startswith('complexity/'):
            require([(p['trial_index'], p['param']) for p in ps] ==
                    [(t, n) for t in range(3) for n in [64, 128, 256, 512]], 'eight-row complexity schedule differs')
        else:
            require(len(ps) == 1, 'eight-row matched point differs')
            points[label] = ps[0]
    values = []
    for n in [64, 128, 256, 512]:
        ps = {(b, a): points[f'matched/knownProjectionFourEight/b{b}-{n}-{a}'] for b in [0, 1] for a in ['A', 'B']}
        require(all(p['param'] == n for p in ps.values()) and len({p['result_hash'] for p in ps.values()}) == 1,
                'eight-row complete kernel hashes differ')
        values.append((n, mean([ps[b, 'B']['per_call_nanos']/ps[b, 'A']['per_call_nanos'] for b in [0, 1]]),
                       sum(p['below_signal_floor'] for p in ps.values())))
    mq = []
    for label, r in results[:2]:
        index = {(v['case'], v['block'], v['arm']): v for v in r['meta']['samples']}
        process, candidate = [], []
        for block in [0, 1]:
            a, b = [index['mq10-f2', block, arm] for arm in ['A', 'B']]
            process.append(b['wall_nanos']/a['wall_nanos'])
            outputs = [cap.json(f'candidate/{label}/mq10-f2-b{block}-{arm}.stdout') for arm in ['A', 'B']]
            candidate.append(outputs[1]['candidateNanos']/outputs[0]['candidateNanos'])
        mq.append((mean(process), mean(candidate)))
    require('Conformance: all oracles passed.' in cap.text('full/oracles.log') and
            'ENOSPC truncated status file' in cap.json('full-status.json')[0]['recovery'] and
            'No space left on device' in cap.text('diagnostics/eight-gap-full-driver-disk-interruption.log'),
            'interrupted audit provenance differs')
    lines = ['## Unselected eight-row experiment', '',
        f'Prototype `{after["source_fingerprint"]}` uses 256-row tables for at least eight known reducers and 512 targets. '
        'It passed all twelve sanitized native variants and all nine project checks, including triangular masks, exact '
        'private allocations and a measured incomplete-group column bound. The corrected conservative bound includes '
        'unsuccessful group searches and keeps the physical cap.', '',
        'The first pass and sole unchanged repeat retain all 192 processes and 96 equal paired complete bases/statistics. '
        'No further unchanged full-system repeat is collected.', '',
        '| Pass | Process B/A | Family balanced B/A | Min / median / max |', '|---|---:|---:|---|']
    for label, r in results:
        a = r['recorded']
        lines.append(f'| {label} | {a["geomean"]:.6f} | {a["family_balanced_geomean"]:.6f} | '
                     f'{a["minimum"]:.6f} / {a["median"]:.6f} / {a["maximum"]:.6f} |')
    lines += ['', f'MQ10 process ratios are {mq[0][0]:.6f} / {mq[1][0]:.6f}; candidate ratios '
        f'{mq[0][1]:.6f} / {mq[1][1]:.6f}. Both passes regress on that input. Aggregating three MQ sizes hides '
        'this regression. The experiment remains unselected; its implementation is retained only in the source capsule.', '',
        '| n | Eight-row policy / four-row kernel time | Below-signal flags |', '|---:|---:|---:|']
    lines += [f'| {n} | {ratio:.6f} | {flags} |' for n, ratio, flags in values]
    lines += ['', 'Only n=512 selects eight-row tables in this kernel. Its modest decrease has two signal flags. '
        'No unchanged kernel repeat was taken. Build/oracle check durations are unavailable; success is supported '
        'by complete source-bound logs. All nine required project checks have successful complete outputs. Failure '
        'diagnostics are retained in the raw capsule.', '', f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '']
    return '\n'.join(lines)+'\n'
