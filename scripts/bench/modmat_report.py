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
        pattern = r'run(Divisor|Modular|Bareiss|Flint)(\w+)N(\d+)B(\d+)$'
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
        'The completed dimension-512 comparator run records 0.279 s for the divisor, '
        '1.263 s for Bareiss (4.52× faster), and 0.153 s for FLINT (1.83× slower after '
        'protocol adjustment). [Raw comparison](data/hex-modular-matrix-divisor-prefix-512.json). '
        'That run includes fixture construction. The prepared-input schedule below '
        'isolates algorithm cost and is retained separately. The structured crossover '
        'is dimension 192; the total `detViaDivisor` wrapper uses Bareiss below it, '
        'while the benchmarks force each route at every rung.', '',
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
        'RHS construction, and FLINT request encoding are outside timed calls. Determinant '
        'arms include bound computation, prime search, elimination, and reconstruction; '
        'a fallback makes the forced modular/divisor benchmark fail. Seed 10220 selects the '
        'divisor RHS. FLINT uses a persistent python-flint process. Its determinant comparator '
        'is gating under the SPEC’s first-measurement policy; `fmpq_mat_solve` is informational '
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
    lines += [
        '## Attribution', '',
        'The final dimension-512 diagnostic uses 67 lifting digits. Its reduced '
        'denominator has 882 bits, leaving a 143-bit cofactor bound and five 31-bit '
        'images (155-bit CRT modulus). Decomposition took 79 ms, solve/reconstruction '
        '92 ms, and cofactor reconstruction 93 ms in that diagnostic. '
        '[Stage output and host context](data/hex-modular-matrix-divisor-prepared-stages.json). '
        'These separate diagnostic timings do not replace the repeated comparator medians.', '',
        'A pinned profile of the prepared divisor arm attributes 11.03% of self samples '
        'to closure application, 8.81% to reference-count cleanup, 8.07% to modular '
        'multiplication, 6.67% to array push, and 5.96% to the modular dot-product loop. '
        'It retained 211 samples with none reported lost. '
        '[Profile](data/hex-modular-matrix-divisor-prepared-profile.txt), '
        '[invocation and host](data/hex-modular-matrix-divisor-profile-host.json), '
        '[benchmark export](data/hex-modular-matrix-divisor-prepared-profile.json). '
        'The small-rung FLINT 5× target is missed: prime search and checked '
        'decomposition impose fixed costs. Under the SPEC’s first-measurement policy '
        'this is a recorded finding; it is not hidden by timing Bareiss in the divisor arm.', '',
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
        'reading the clock.', '',
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
