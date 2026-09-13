#!/usr/bin/env python3
"""Render the retained modular determinant comparator exports as Markdown."""
import argparse
import json
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('inputs', nargs='+', type=Path)
    args = parser.parse_args()
    datasets = [(p, json.loads(p.read_text())) for p in args.inputs]
    lines = [
        '# Bounded modular determinant baseline', '',
        'This report measures the ordinary bounded CRT determinant from milestones 1–2. '
        'It makes no Phase-4 completion or divisor-route speed claim. Across all three '
        'families, the modular route is slower than Bareiss at every completed common rung; large modular '
        'calls reach the harness cap. Dixon and the determinant-divisor optimization '
        'are separate milestones.', '',
        'These fixed registrations are external-comparator anchors, not an empirical '
        'complexity attestation or an absolute-budget gate. Elimination performs '
        'cubic word arithmetic per image; reconstruction needs enough images to '
        'exceed twice the row/column Hadamard bound.', '',
        '## Inputs and timing protocol', '',
        '- `structured-determinant`: the shared Bareiss salt-71 tridiagonal fixture '
        'at 16, 24, 32, 48, 64, 96, 128, 192, 256, 320, 384 and 512.',
        '- `dense-random-determinant`: splitmix64 seed 10219, dimensions '
        '32, 64, 96, 128, 192 and 256, with centered 8-, 64- and 1024-bit entries.',
        '- `unimodular-determinant`: dense `I + u vᵀ`, with `u` all ones, '
        '`v` alternating ±2⁶⁴, and `vᵀu = 0`, so the determinant is one. '
        'Dimensions are 32, 64, 96, 128, 192 and 256. Negative determinant '
        'variants are covered by conformance.', '',
        'The three arms receive identical matrices. Matrix construction and FLINT '
        'request encoding precede the timed closures. The modular arm includes '
        'bound computation, finite prime supply, elimination and CRT, and rejects '
        'any Bareiss fallback. The comparator is FLINT fmpz_mat_det via python-flint, using the '
        'shared persistent subprocess protocol; JSON parsing and result transport '
        'remain included.', '',
        'Each arm has a discarded outer warmup, a discarded first invocation '
        'inside each child, and five fixed repeats with a 0.2-second auto-tuning '
        'floor. Adjacent modular/Bareiss/FLINT arms reverse order on alternate '
        'rungs. CPU placement uses a nonblocking lease on the shared host. Every '
        'completed export is retained; host load is recorded without filtering. The two '
        'structured dimension-16 observations differ by 2.4× in modular time, and '
        'their Hex/FLINT ratios differ by 65%. These are host-specific observations; '
        'rows in different datasets must not be treated as a controlled comparison, and '
        'the small-rung differences do not establish an algorithmic scaling trend. '
        'The listed source fingerprints cover selected files; the executable SHA-256 '
        'pins the complete compiled implementation, including the Bareiss comparator.', '',
        'The initial run used one Lean worker. A blocking stderr reader prevented '
        'the harness timer from running, so its completed timings can exceed the '
        'configured ten-second cap. Relinking the executable interrupted the '
        'Bareiss and FLINT child launches at dimension 256. The incomplete '
        'dimension-320 comparison was stopped before its combined export was written; '
        'its partial arm output is unavailable. The resumed run uses two workers '
        'on one CPU and an immutable executable copy; it repeats dimension 256 '
        'once and completes the remaining schedule. Both datasets are retained. '
        'A final collector check verifies per-arm checkpoints, so future interrupted '
        'comparisons preserve completed arms. Large determinant replies also exposed '
        'Python’s default 4300-digit conversion limit; the large-integers dataset '
        'repeats the affected dense 256/64 and 1024-bit range with '
        '`PYTHONINTMAXSTRDIGITS=0`. The original errors remain visible.', '',
        '`Hex / FLINT` means modular median divided by the FLINT median minus '
        'that dataset’s empty-protocol median; lower is faster. Raw medians are '
        'in seconds. The parameter b is the dense signed-entry width or the unimodular '
        'power-of-two exponent; it is unused for the fixed structured fixture. `cap` denotes a killed child batch, including setup and '
        'warmup; it is not a lower bound on the timed call alone. Ratios are '
        'omitted if an arm lacks all five successful repeats. No partial sample '
        'is silently promoted to a complete comparison.', '',
    ]
    for path, data in datasets:
        runs = data['runs']
        overhead = runs[0]['export']['results'][0]['median_nanos']
        env = runs[0]['export']['env']
        lines += [f'## {path.stem}', '',
                  f"Host `{env['hostname']}`, {env['cpu_model']}, CPU {data['cpu']}; "
                  f"Lean {env['lean_version']}, python-flint {data['versions']['python_flint']}. "
                  f"Protocol median: {overhead / 1000:.3f} µs.", '',
                  f"Load before: `{data['load_before']}`; after: `{data['load_after']}`. "
                  f"[Complete exports and source fingerprints](data/{path.name}).", '',
                  '| Family | n | b | Modular s | Bareiss s | FLINT s | Hex / FLINT |',
                  '|---|---:|---:|---:|---:|---:|---:|']
        for run in runs[1:]:
            results = run.get('export', {}).get('results', [])
            arms = {}
            for result in results:
                match = re.search(r'run(Modular|Bareiss|Flint)(\w+)N(\d+)B(\d+)$', result['function'])
                arm, family, n, bits = match.groups()
                arms[arm] = result
            if not arms:
                continue
            def cell(arm):
                if arm not in arms:
                    return '—'
                result = arms[arm]
                statuses = [p['status'] for p in result['points']]
                if all(s == 'ok' for s in statuses) and len(statuses) == 5:
                    return f"{result['median_nanos'] / 1e9:.3g}"
                if len(statuses) == 5 and all(s == 'killed_at_cap' for s in statuses):
                    return 'cap (5/5)'
                return f"{statuses.count('ok')}/5 ok"
            complete = len(arms) == 3 and all(
                len(r['points']) == 5 and all(p['status'] == 'ok' for p in r['points'])
                for r in arms.values())
            ratio = '—'
            if complete and arms['Flint']['median_nanos'] > overhead:
                ratio = f"{arms['Modular']['median_nanos'] / (arms['Flint']['median_nanos'] - overhead):.1f}×"
            hashes = {r['observed_hash'] for r in arms.values() if r['observed_hash'] is not None}
            if len(hashes) > 1 or any(not r['hashes_agree'] for r in arms.values()):
                raise ValueError(f'answer hash disagreement at {family}/{n}/{bits}')
            lines.append(f'| {family.lower()} | {n} | {bits} | {cell("Modular")} | '
                         f'{cell("Bareiss")} | {cell("Flint")} | {ratio} |')
        lines.append('')
    counts = json.loads((Path(__file__).resolve().parents[2] /
        'reports/data/hex-modular-matrix-image-counts.json').read_text())
    lines += ['## Bound image counts', '',
              'Conformance recovers each consumed prime-prefix length from the actual '
              'CRT modulus and checks that Hadamard uses no more images than the '
              'row-norm bound. [Recorded counts](data/hex-modular-matrix-image-counts.json).', '',
              '| Fixture | Row norm | Hadamard |', '|---|---:|---:|']
    lines += [f"| {c['case']} | {c['row_norm']} | {c['hadamard']} |" for c in counts]
    lines += ['',
        '## Attribution and verification', '',
        'A diagnostic `perf` profile at structured dimension 128 attributes '
        '18.75% of self samples to `lean_apply_2`, 8.75% to `lean_apply_1`, '
        '6.26% to the row-add closure and 4.60% to array construction. Allocation, '
        'reference counting and submatrix construction are also visible. This '
        'supports focusing future optimization on specialization and buffer '
        'operations; it does not establish their achievable speedup. The '
        'unpinned profile is separate from the comparison. Its output reports '
        '23 lost samples; no recorded samples were filtered.', '',
        '[Profile summary](data/hex-modular-matrix-profile.txt), '
        '[profile invocation export](data/hex-modular-matrix-profile.json), and '
        '[small smoke-anchor calibration](data/hex-modular-matrix-smoke.json). '
        'The three CI anchors pin the complete determinant-result hashes. '
        'All completed common comparator results agree by complete-result hash; '
        'small, singular, composite-modulus, bad-prime and forced-fallback '
        'cases are also checked by the conformance suite and FLINT fixtures.', '',
        'Reproduce with `lake build hexmodularmatrix_bench`, then '
        '`HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py <output.json>`. '
        'Render retained datasets with `scripts/bench/modmat_report.py`.', '',
    ]
    args.output.write_text('\n'.join(lines))


if __name__ == '__main__':
    main()
