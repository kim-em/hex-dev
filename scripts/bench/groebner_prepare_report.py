#!/usr/bin/env python3
"""Verify retained batched monomial preparation samples and render their report."""
import argparse
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_tables_report import checks
from scripts.bench.groebner_trie_report import mean, require, source


FUNCTIONS = ['monomialProducts', 'productWide', 'productMisses']
SIZES = [256, 1024, 4096]


def kernels(cap, before, after, identity):
    status = cap.json('candidate/kernel-status.json')
    require(status['identity'] == identity and status['threads'] == 1 and
            status['manifest'] == {'A': before, 'B': after} and
            status['binary_sha256'] == status['binary_sha256_after'] ==
            {a: m['binary_sha256']['bench'] for a, m in [('A', before), ('B', after)]},
            'kernel executable binding differs')
    expected = [f'complexity/{f}/{a}' for f in FUNCTIONS for a in ['A', 'B']] + [
        f'matched/{f}/b{b}-{n}-{a}' for b in [0, 1] for f in FUNCTIONS for n in SIZES
        for a in (['A', 'B'] if b == 0 else ['B', 'A'])]
    rows = status['samples']
    require([r['label'] for r in rows] == expected and len({r['cpu'] for r in rows}) == 1,
            'kernel schedule or CPU differs')
    digest = cap.json('digest/status.json')
    require(digest['exit_code'] == 0 and digest['kind'] == 'products' and
            digest['source_commit'] == identity['source_commit'] and
            digest['sizes'] == [0, 1, 63, 64, 65, 256, 512, 1024, 2048, 4096] and
            cap.text('digest/run.stderr') == '', 'independent digest checks differ')
    digests = digest['digests']
    require(len(digests) == 30 and {line.rsplit(',', 1)[0]: int(line.rsplit(',', 1)[1])
            for line in cap.text('digest/run.stdout').splitlines()} == digests,
            'independent digest output differs')
    points = {}
    for row in rows:
        label, cmd = row['label'], row['command']
        function = label.split('/')[1]
        require(row['exit_code'] in [0, 2] and
                'Hex.Groebner.Bench.' + function in cmd and
                cmd[cmd.index('--target-inner-nanos')+1] == '4000000000' and
                cmd[cmd.index('--max-seconds-per-call')+1] == '20', 'kernel command differs')
        result = cap.json('candidate/kernels/' + label + '/result.json')['results'][0]
        require(result['config']['target_inner_nanos'] == 4000000000,
                'inner target was truncated')
        ps = result['points']
        require(all(p['status'] == 'ok' and
                    int(p['result_hash'], 16) == digests[f'{function},{p["param"]}'] for p in ps),
                'invalid complete kernel result')
        require(int(cap.text('candidate/kernels/' + label + '/rss')) > 0, 'kernel RSS missing')
        if label.startswith('complexity/'):
            require([(p['trial_index'], p['param']) for p in ps] ==
                    [(t, n) for t in range(3) for n in [256, 512, 1024, 2048, 4096]],
                    'trial-major complexity schedule differs')
        else:
            require(len(ps) == 1, 'matched point count differs')
            points[label] = ps[0]
    values = []
    for f in FUNCTIONS:
        for n in SIZES:
            ps = {(b, a): points[f'matched/{f}/b{b}-{n}-{a}'] for b in [0, 1] for a in ['A', 'B']}
            require(all(p['param'] == n for p in ps.values()), 'matched parameter differs')
            values.append((f, n, mean([ps[b, 'B']['per_call_nanos']/ps[b, 'A']['per_call_nanos']
                                      for b in [0, 1]]), sum(p['below_signal_floor'] for p in ps.values())))
    return values, rows[0]['cpu']


def render(cap, before, after, records, values, cpu):
    lines = ['# Batched monomial preparation', '',
        'The native product planner prepares independent monomials together, keeping their FNV accumulators '
        'in parallel while preserving exact hashes, collision comparisons, stable identifiers, output bytes '
        'and logical charges. Preparation reserves its full coordinate work before traversal. Scratch stays '
        'below 32 KiB, native work stays within 4096 units, and refusal preserves the input table for scalar continuation.', '',
        f'Baseline `{before["source_fingerprint"]}`; candidate `{after["source_fingerprint"]}`. '
        'The measured runtime delta is confined to `HexGroebner/ffi/monomial_hit.c`. Native compiler '
        'Clang 21.1.8, generated-C compiler SDK Clang 23.1.0, toolchain, native flags and benchmark inputs '
        'match between arms. Complete compiler identities and host context are retained in the capsule.', '',
        '## Isolated kernels', '',
        f'CPU {cpu}, one algorithm thread, four-second inner targets, three fixed trial-major complexity '
        'trials, then adjacent AB/BA matched samples. Preparation is excluded; product lookup, any insertion, '
        'validation and result hashing are included. The hit kernels consume complete support/workspace results; '
        'the insertion kernel also consumes every arena, metadata and index byte. Independently compiled '
        'checks validate all three functions against scalar results at ten sizes, including slice boundaries.', '',
        '| Kernel | n | New / previous time | Below-signal flags |', '|---|---:|---:|---:|']
    lines += [f'| {f} | {n} | {ratio:.6f} | {flags} |' for f, n, ratio, flags in values]
    lines += ['', '`monomialProducts` uses three variables and existing products; `productWide` uses 22 '
        'variables and shorter adaptive slices. `productMisses` lacks the last product of each complete '
        '64-term slice. These fixed workloads do not establish an equal full-system improvement.', '',
        '## Full-system observations', '',
        'Each pass alternates adjacent AB/BA pairs on one leased CPU, with one algorithm thread, degree '
        'scheduling, grevlex and complete reduced output. F₂ enables binary pivots in both arms; prime '
        'controls use p = 32003 and 2147483647 with binary pivots disabled. Every completed sample, outlier, '
        'failure and RSS observation is retained. The repeat is the sole unchanged repeat.', '',
        '| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |',
        '|---|---:|---:|---:|---:|---|---|']
    for label, result in records:
        a, m = result['recorded'], result['meta']
        lines.append(f'| {label} | {m["cpu"]} | {a["geomean"]:.6f} | '
            f'{a["family_balanced_geomean"]:.6f} | {result["candidate"]:.6f} | '
            f'{a["minimum"]:.6f} / {a["median"]:.6f} / {a["maximum"]:.6f} | '
            f'{a["peak_rss_kib"]["A"]} / {a["peak_rss_kib"]["B"]} |')
    lines += ['', 'All 192 processes completed, with all 96 paired complete bases and every logical statistic '
        'equal. The full-system aggregates do not establish an overall gain or performance leadership. '
        'These small diagnostic suites do not satisfy the SPEC’s leadership acceptance suite. Candidate '
        'production returns unchecked candidates; certificate generation, independent native verification '
        'and kernel checking remain separate and are excluded from these timing ratios.', '',
        '| Family | F₂ first / repeat B/A | Prime first / repeat B/A |', '|---|---|---|']
    for family in records[0][1]['recorded']['per_family']:
        def pair(indices):
            return ' / '.join(f'{records[i][1]["recorded"]["per_family"][family]:.6f}' for i in indices)
        prime = pair([2, 3]) if family in records[2][1]['recorded']['per_family'] else 'not in prime suite'
        lines.append(f'| {family} | {pair([0, 1])} | {prime} |')
    lines += ['', '## Verification and reproduction', '',
        'All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include '
        '567 unique SymPy and 567 Singular reduced-basis comparisons, malformed inputs/certificates, '
        'overflow, work exhaustion, native/portable comparisons, downstream kernel replay and axiom audits. '
        'The native harness checks full product-table snapshots, aliases, collisions and refusal at the '
        '4096-work boundary. The committed sources, check manifests, complete logs, inputs, raw samples '
        'and collector programs are bound by per-file SHA-256 hashes.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '', '```bash',
        'python3 scripts/bench/groebner_prepare_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-prepare.md --check --current', '```', '',
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '']
    return '\n'.join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--check', action='store_true')
    p.add_argument('--current', action='store_true')
    args = p.parse_args()
    cap = Capsule(args.archive)
    before, after = source(cap, 'baseline'), source(cap, 'candidate')
    a, b = listing(before['source_manifest']), listing(after['source_manifest'])
    require(set(a) == set(b) and {k for k in a if a[k] != b[k]} ==
            {'HexGroebner/ffi/monomial_hit.c'}, 'runtime delta differs')
    require(before['compilers'] == after['compilers'] and
            before['native_options'] == after['native_options'], 'compiler controls differ')
    identity = checks(cap, after, True)
    if args.current:
        current = source_identity()
        require(all(current[k] == identity[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current sources/checks differ')
    records = [(label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag}))
               for label, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                                          ('prime-control', 14, None), ('prime-control-repeat', 14, None)]]
    values, cpu = kernels(cap, before, after, identity)
    text = render(cap, before, after, records, values, cpu)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified complete outputs, counters, source/check manifests, compiler/ELF bindings and raw samples.')


if __name__ == '__main__':
    main()
