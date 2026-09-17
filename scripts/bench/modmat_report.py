#!/usr/bin/env python3
"""Render retained Dixon and determinant comparator exports as Markdown."""
import argparse
import json
from pathlib import Path
import re


def complete(result):
    return result is not None and len(result['points']) == 5 and all(
        point['status'] == 'ok' for point in result['points'])


def cell(result):
    if result is None:
        return '—'
    statuses = [point['status'] for point in result['points']]
    if complete(result):
        return f"{result['median_nanos'] / 1e9:.4g}"
    if len(statuses) == 5 and all(s == 'killed_at_cap' for s in statuses):
        return 'cap (5/5)'
    return f"{statuses.count('ok')}/5 ok"


def ratio(numerator, denominator, overhead=0):
    if not complete(numerator) or not complete(denominator):
        return '—'
    adjusted = denominator['median_nanos'] - overhead
    return f"{numerator['median_nanos'] / adjusted:.2f}×" if adjusted > 0 else '—'


def table(data):
    mode = data.get('mode', 'baseline')
    overhead = data['runs'][0]['export']['results'][0]['median_nanos']
    if mode in ('baseline', 'divisor'):
        lines = ['| Family | n | bits | Divisor s | Ordinary CRT s | Bareiss s | FLINT s | Bareiss / divisor | Divisor / FLINT |',
                 '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
        pattern = r'run(Divisor|Dispatch|Modular|Bareiss|Flint)(\w+)N(\d+)B(\d+)$'
    elif mode == 'solve':
        lines = ['| Operation | n | Hex s | FLINT s | Hex / FLINT |', '|---|---:|---:|---:|---:|']
        pattern = r'run(Decomp|Solve|FlintSolve)(Integral|Rational)?N(\d+)$'
    else:
        lines = ['| n | RHS count | Reused s | Independent s | Independent / reused |',
                 '|---:|---:|---:|---:|---:|']
        pattern = r'run(Repeated|Independent)N(\d+)R(\d+)$'
    for run in data['runs'][1:]:
        arms = {}
        groups = None
        for result in run.get('export', {}).get('results', []):
            match = re.search(pattern, result['function'])
            if not match:
                raise ValueError(f"unrecognised registration: {result['function']}")
            arm, *groups = match.groups()
            arms[arm] = result
        if not arms:
            continue
        hashes = {r['observed_hash'] for r in arms.values() if r['observed_hash'] is not None}
        if len(hashes) > 1 or any(not r['hashes_agree'] for r in arms.values()):
            raise ValueError(f'answer hash disagreement at {groups}')
        get = arms.get
        if mode in ('baseline', 'divisor'):
            family, n, bits = groups
            lines.append(f'| {family.lower()} | {n} | {bits} | {cell(get("Divisor"))} | '
                         f'{cell(get("Modular"))} | {cell(get("Bareiss"))} | {cell(get("Flint"))} | '
                         f'{ratio(get("Bareiss"), get("Divisor"))} | '
                         f'{ratio(get("Divisor"), get("Flint"), overhead)} |')
        elif mode == 'solve':
            kind, n = groups
            operation = kind.lower() if kind else 'decomposition'
            value = get('Solve') if kind else get('Decomp')
            lines.append(f'| {operation} | {n} | {cell(value)} | {cell(get("FlintSolve"))} | '
                         f'{ratio(value, get("FlintSolve"), overhead)} |')
        else:
            n, r = groups
            lines.append(f'| {n} | {r} | {cell(get("Repeated"))} | {cell(get("Independent"))} | '
                         f'{ratio(get("Independent"), get("Repeated"))} |')
    return lines


def dispatch_table(data):
    overhead = data['runs'][0]['export']['results'][0]['median_nanos']
    lines = ['### Public determinant dispatcher', '',
             '| n | Selected route | Public s | FLINT s | Public / FLINT |',
             '|---:|---|---:|---:|---:|']
    for run in data['runs'][1:]:
        arms = {}
        n = None
        for result in run.get('export', {}).get('results', []):
            match = re.search(r'run(Dispatch|Flint|Bareiss)StructuredN(\d+)B8$', result['function'])
            if match:
                arm, n = match.groups()
                arms[arm] = result
        d, f, b = (arms.get(a) for a in ('Dispatch', 'Flint', 'Bareiss'))
        if d is None:
            continue
        if complete(d) and complete(f) and f['median_nanos'] > overhead:
            if d['median_nanos'] > 5 * (f['median_nanos'] - overhead):
                raise ValueError(f'public dispatcher exceeds 5× FLINT at n={n}')
        if n == '512' and complete(d) and complete(b):
            if b['median_nanos'] < 4 * d['median_nanos']:
                raise ValueError('public dispatcher misses 4× Bareiss at n=512')
        route = 'Bareiss' if int(n) < 192 else 'divisor'
        lines.append(f'| {n} | {route} | {cell(d)} | {cell(f)} | {ratio(d, f, overhead)} |')
    return lines + ['', 'Every complete structured rung with a positive adjusted FLINT median '
                    'meets the 5× public-entry-point threshold. The forced divisor rows above '
                    'also expose its fixed cost below the crossover.', '']


def attribution(root):
    prefix = 'hex-modular-matrix-divisor-'
    stage_path = root / 'reports/data' / (prefix + 'stages-final.json')
    stage = json.loads(stage_path.read_text())
    values = {k: int(v) for k, v in re.findall(r'(\w+)=(\d+)', stage['stdout'])}
    profile_path = root / 'reports/data' / (prefix + 'profile-final.txt')
    profile = profile_path.read_text()
    samples = re.search(r'# Samples: (\d+)', profile).group(1)
    lost = re.search(r'# Total Lost Samples: (\d+)', profile).group(1)
    symbols = re.findall(r'^\s*([\d.]+)%.*\[.\] (.+)$', profile, re.M)[:5]
    lines = ['## Attribution', '',
        f"The dimension-512 diagnostic uses {values['digits']} lifting digits. Its reduced "
        f"denominator has {values['den_bits']} bits, leaving a {values['cofactor_bound_bits']}-bit "
        f"cofactor bound and a {values['modulus_bits']}-bit CRT modulus. Decomposition took "
        f"{values['decomp_ns']/1e6:.1f} ms, solve/reconstruction {values['solve_ns']/1e6:.1f} ms, "
        f"and cofactor reconstruction {values['cofactor_ns']/1e6:.1f} ms. "
        f'[Stage output and host context](data/{stage_path.name}). '
        'These separate diagnostic timings do not replace the repeated comparator medians.', '',
        f"The auxiliary bound computation took {values['bound_ns']/1e6:.1f} ms; generating "
        f"{values['prime_count']} primes took {values['supply_ns']/1e6:.1f} ms. The existing "
        'prime generator tests candidates by full trial division through their square root. '
        'This contributes a fixed cost on small matrices. The production route first probes '
        'one prime and sizes the cofactor prefix from its bound, so it need not pay for the '
        'whole auxiliary supply.', '',
        f'A pinned profile retained {samples} samples with {lost} reported lost. '
        'Its five largest self-sample entries are:', '',
        '| Self samples | Symbol |', '|---:|---|']
    lines += [f'| {pct}% | `{symbol}` |' for pct, symbol in symbols]
    lines += ['', f'[Profile](data/{profile_path.name}), '
        f'[invocation and host](data/{prefix}profile-final-host.json), '
        f'[benchmark export](data/{prefix}profile-final.json).', '',
        '## Bound image counts', '',
        'The ordinary CRT conformance fixtures retain the row-norm and Hadamard bound '
        'comparison. Counts include the terminating image. '
        '[Raw counts](data/hex-modular-matrix-image-counts.json).', '',
        '| Case | Row norm | Hadamard |', '|---|---:|---:|']
    counts = json.loads((root / 'reports/data/hex-modular-matrix-image-counts.json').read_text())
    lines += [f"| {v['case']} | {v['row_norm']} | {v['hadamard']} |" for v in counts]
    return lines + ['']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('inputs', nargs='+', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    lines = [
        '# Dixon solve and determinant divisor', '',
        'The implementation reuses a checked modular inverse for p-adic lifting, '
        'reconstructs and reduces a common-denominator solution, and checks the integer '
        'equation. The determinant route reconstructs the cofactor after extracting the '
        'reduced denominator as a determinant divisor. The tables below measure that '
        'route against ordinary CRT, Bareiss, and FLINT, and attribute single and repeated solves.', '',
        '## Protocol and inputs', '',
        '- Structured determinant: the shared salt-71 tridiagonal fixture, dimensions '
        '16, 24, 32, 48, 64, 96, 128, 192, 256, 320, 384, 512.',
        '- Dense determinant: splitmix64 seed 10219, signed entry widths 8, 64, 1024; '
        'dimensions 32, 64, 96, 128, 192, 256.',
        '- Unimodular determinant: dense `I + u vᵀ`, `u = 1`, alternating '
        '`v = ±2⁶⁴`, hence determinant one. This is the divisor’s worst case.',
        '- Single solve: dense 8-bit seed 10220 matrices at the same six dimensions. '
        'Integral RHS is `A C`; rational RHS is `C`, with `C[i,j] = (i + 3j) % 17 - 8`. '
        'The inverse is prepared outside the timed `solveWith` call; decomposition has its own arm.',
        '- Repeated solve: `r = 1, 8, n`. Reused timing includes one decomposition '
        'and `solveMatWith`; independent timing includes `r` complete `solve?` calls. '
        'Both use the rational RHS and return the same common-denominator checksum.', '',
        'Closed memoised fixture values are forced by discarded warmups. Matrix construction, '
        'RHS construction, and FLINT JSON input-tree construction are outside timed calls. Determinant '
        'arms include bound computation, prime search, elimination, and reconstruction; '
        'a fallback makes the forced modular/divisor benchmark fail. Seed 10220 selects the '
        'divisor RHS. FLINT uses a persistent python-flint process; serialization, parsing, and '
        'transport remain timed. Its determinant comparator '
        'gates the public structured dispatcher at 5× on every complete eligible rung; `fmpq_mat_solve` is informational '
        'and includes its own decomposition, unlike the separate Hex lifting arm.', '',
        'Each registration has five fixed repeats, a 0.2-second tuning floor, and discarded '
        'outer and inner warmups. Adjacent arms reverse order on alternate rungs. Each '
        'collector leases an automatically selected CPU and uses two Lean workers pinned '
        'there. Host activity is recorded without filtering. Immutable executable copies '
        'and source hashes identify each run; different datasets are not a controlled '
        'before/after comparison.', '',
        'Medians are seconds. FLINT ratios subtract the same dataset’s empty-protocol median '
        'from the FLINT denominator. `cap` describes a killed child batch, including setup '
        'and warmup; it is not a lower bound on one timed call. Ratios require five successful '
        'repeats in both arms. These fixed comparator anchors do not attest an empirical '
        'complexity fit. The generic algorithm uses cubic modular elimination, quadratic '
        'matrix-vector work per lifting digit, and one elimination per cofactor image; '
        'zero skipping and sparse residual products benefit the structured fixture.', '',
    ]
    # The headline is derived only from a complete same-run comparison.
    for path in args.inputs:
        data = json.loads(path.read_text())
        if data.get('mode') != 'divisor':
            continue
        for run in data['runs'][1:]:
            arms = {r['function'].split('.')[-1]: r
                    for r in run.get('export', {}).get('results', [])}
            d = arms.get('runDivisorStructuredN512B8')
            b = arms.get('runBareissStructuredN512B8')
            f = arms.get('runFlintStructuredN512B8')
            if complete(d) and complete(b) and complete(f):
                overhead = data['runs'][0]['export']['results'][0]['median_nanos']
                lines[4:4] = [
                    f'Dimension 512: divisor {cell(d)} s, Bareiss {cell(b)} s '
                    f'({ratio(b, d)} speedup), FLINT {cell(f)} s '
                    f'({ratio(d, f, overhead)} divisor/FLINT). The required 4× Bareiss '
                    'threshold is met. The structured crossover is dimension 192; the '
                    'total `detViaDivisor` wrapper uses Bareiss below it, while these '
                    'main tables force each route at every rung. A separate table measures the public wrapper.', '']
                if b['median_nanos'] < 4 * d['median_nanos']:
                    raise ValueError('the required structured determinant speedup is not met')
    for path in args.inputs:
        data = json.loads(path.read_text())
        first = data['runs'][0]['export']
        env = first['env']
        overhead = first['results'][0]['median_nanos']
        lines += [f'## {path.stem}', '',
                  f"Host `{env['hostname']}`, {env['cpu_model']}, CPU {data['cpu']}; "
                  f"Lean {env['lean_version']}, python-flint {data['versions']['python_flint']}. "
                  f"Protocol median {overhead / 1000:.3f} µs.", '',
                  f"Load before `{data['load_before']}`; after `{data.get('load_after', 'running')}`. "
                  f'[Raw exports and fingerprints](data/{path.name}).', '']
        lines += table(data) + ['']
        if data.get('mode') == 'divisor' and any(
                'runDispatch' in r['function'] for run in data['runs'][1:]
                for r in run.get('export', {}).get('results', [])):
            lines += dispatch_table(data)
    prepared_path = root / 'reports/data/hex-modular-matrix-divisor-prepared.json'
    lines += ['## Earlier prepared comparison including ordinary CRT', '',
              'This retained schedule measures all four forced arms together. It precedes '
              'the single-check divisor path and lifting-modulus hoist; ordinary CRT is unchanged. '
              'Ratios below use only arms within this schedule. '
              f'[Raw exports and fingerprints](data/{prepared_path.name}).', '']
    lines += table(json.loads(prepared_path.read_text())) + ['']
    lines += attribution(root)
    lines += [
        '## Correctness and retained measurements', '',
        'The full build and conformance suite verify single and multiple RHS solutions, '
        'normalisation, lifting congruences, strict digit bounds, zero-dimensional cases, '
        'composite moduli, unlucky initial primes, seeds, and forced exhaustion. FLINT checks '
        '159 complete answers. Eight CI smoke anchors pin output hashes. Every completed '
        'common comparator result is checked for hash agreement by this report generator.', '',
        'The reduction regression supplies `y = 3, d = 6` to the production cofactor route '
        'for `A = [2], b = [1]`. It must reduce to denominator two. Removing reduction from '
        'that route makes the assertion fail; the mutation was built locally. The prime '
        'reuse test checks the resulting CRT modulus, and a modulus sharing a factor with '
        'the reduced denominator is rejected before its determinant image is computed.', '',
        'Earlier implementation measurements and profiles are retained below. The initial '
        'Gauss–Jordan pass cleared above each pivot immediately, destroying upper-factor '
        'sparsity. Forward elimination followed by backward clearing, determinant-only '
        'cofactor images, cached inverse rows, sparse integer products, and shorter prime '
        'prefixes remove that overhead. These observations motivated changes; their ratios '
        'are not controlled before/after evidence.', '',
        'The earlier `divisor-final`, `solve`, and `repeated` datasets used functions whose '
        'pure preparation was moved into timed calls by Lean arity expansion. They therefore '
        'include fixture construction; `solve` also includes decomposition. They are retained '
        'as end-to-end diagnostics, not presented as separate `solveWith` costs. Early stage '
        'files’ `bound_ns` and `supply_ns` were similarly affected by code motion and are not '
        'used for attribution. The corrected stage diagnostic forces these values before '
        'reading the clock. The `prepared` datasets precede the single-check divisor path '
        'and hoisted lifting modulus. Their ordinary-CRT measurements remain applicable '
        'because those subsequent changes affect only Dixon. The final `measured` schedule '
        'omits that unchanged arm; its full measurements are retained in the prepared export.', '',
    ]
    selected = {p.resolve() for p in args.inputs}
    for path in sorted((root / 'reports/data').glob('hex-modular-matrix-*.json')):
        if path.resolve() not in selected:
            lines.append(f'- [{path.stem}](data/{path.name})')
    lines += ['',
        'Reproduce: `lake build hexmodularmatrix_bench`, then '
        '`HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py '
        '<output.json> --mode divisor` (or `solve`, `repeated`). Render selected exports '
        'with `python3 scripts/bench/modmat_report.py <report.md> <exports...>`.', '',
    ]
    args.output.write_text('\n'.join(lines))


if __name__ == '__main__':
    main()
