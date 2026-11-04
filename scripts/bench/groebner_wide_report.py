#!/usr/bin/env python3
"""Check and reproduce the larger packed F2 matrix-frame observations."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_prepare_report import compiler_name
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_tables_report import checks
from scripts.bench.groebner_trie_report import require, source


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
    require(set(a) == set(b) and {n for n in a if a[n] != b[n]} ==
            {'HexGroebner/EliminationKernel.lean', 'HexGroebner/ffi/matrix_eliminate.c'},
            'packed frame runtime delta differs')
    require(before['compilers'] == after['compilers'] and
            before['native_options'] == after['native_options'], 'compiler controls differ')
    identity = checks(cap, after, True)
    if args.current:
        current = source_identity()
        require(all(current[k] == identity[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current source/checks differ')
    records = [(label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag}))
               for label, count, flag in [('f2-false', 10, 'true'), ('prime-control', 14, None),
                                          ('hard-cyclic9-f2', 1, 'true')]]
    hard = records[2][1]
    for label, result in records:
        meta = result['meta']
        for row in meta['samples']:
            name = f'{row["case"]}-b{row["block"]}-{row["arm"]}.stdout'
            require(cap.json('candidate/'+label+'/'+name)['batchSize'] == 1024,
                    'batch size differs from the library default')
    lines = ['# Larger packed F₂ matrix frames', '',
        'The optional packed F₂ route has separate ceilings of 131072 columns, 131072 known reducers and 4096 targets, subject to joint work and byte bounds. '
        'The previous limits were 16384/16384/1024. Its conservative logical-work limit is 2³⁸ '
        'and its packing/scalar/word-visit limit is 2³⁴, previously 2³² and 2²⁸. Complete private '
        'bit rows, metadata, projected targets and the reusable sixteen-row table must fit the '
        'parent packed-byte allowance. Every accepted result has the exact portable rows, sugars '
        'and counters; unsupported or refused frames retain the reference continuation.', '',
        'Leading-column validation has a fixed 16384-byte bitmap and initializes only '
        '`ceil(columns/8)` bytes. The field and monomial-order contracts are unchanged. These '
        'are ordinary F₂ polynomial rings, including squares; no Boolean quotient relations are added.', '',
        f'Baseline `{before["source_fingerprint"]}`; candidate `{after["source_fingerprint"]}`. '
        'Only the matching Lean admission guards and native matrix source change in the runtime '
        f'manifest. Native compiler `{compiler_name(after, "native")}`, generated-C compiler '
        f'`{compiler_name(after, "lean")}` (SDK), compiler options, inputs and controls match.', '',
        '## Matched observations', '',
        'Each campaign leases one CPU, uses one algorithm thread and runs adjacent AB then BA pairs. '
        'All use degree scheduling, grevlex, batch size 1024, complete reduced output and explicit '
        'binary-pivot controls. Binary pivots are enabled in both F₂ arms; the historical `f2-false` cohort label does not describe that policy. The library defaults this option to `false`, so default users see no change. Every completed sample, outlier, failure and RSS observation is retained. '
        'No unchanged repeat is included. These comparisons measure candidate production through '
        'final interreduction and output. Parsing, launch and initialization are included in process '
        'time; certificate generation, independent native verification and kernel checking are separate.', '',
        '| Cohort | CPU | Process B/A | Family balanced B/A | Candidate B/A | Pair min / median / max | Peak RSS A / B (KiB) |',
        '|---|---:|---:|---:|---:|---|---|']
    for label, result in records:
        r, m = result['recorded'], result['meta']
        lines.append(f'| {label} | {m["cpu"]} | {r["geomean"]:.6f} | '
            f'{r["family_balanced_geomean"]:.6f} | {result["candidate"]:.6f} | '
            f'{r["minimum"]:.6f} / {r["median"]:.6f} / {r["maximum"]:.6f} | '
            f'{r["peak_rss_kib"]["A"]} / {r["peak_rss_kib"]["B"]} |')
    h = hard['recorded']
    lines += ['', f'All 100 processes complete, with 50 equal complete-basis pairs and identical logical '
        f'statistics. Cyclic-9 over F₂ has process B/A {h["geomean"]:.6f}, a '
        f'{100*(1-h["geomean"]):.1f}% reduction on these two pairs. Peak RSS rises from '
        f'{h["peak_rss_kib"]["A"]} to {h["peak_rss_kib"]["B"]} KiB '
        f'({h["peak_rss_kib"]["B"]/h["peak_rss_kib"]["A"]:.2f}×). '
        'Additional private packing is a plausible source of the higher memory usage, rather than a measured attribution. The moderate F₂ and '
        'prime-control observations do not establish a broad speedup.', '',
        '| Development family | F₂ process B/A | Prime-control process B/A |', '|---|---:|---:|']
    for family, value in records[0][1]['recorded']['per_family'].items():
        prime = records[1][1]['recorded']['per_family'].get(family)
        lines.append(f'| {family} | {value:.6f} | '+(f'{prime:.6f}' if prime else 'not in prime suite')+' |')
    lines += ['', 'The Cyclic-9 focus addresses a public hard case with matrices beyond the former '
        'native geometry and motivated the cap selection. It is an in-sample case also present in the primary fixed corpus. It is reported separately from the development suites. These observations '
        'are not a completed fixed-corpus evaluation, a held-out result or an external-comparator '
        'leadership claim. Ratios from different implementation stages are not multiplied.', '',
        'The moderate cohorts use a 16 GiB packed-payload allowance. The focused Cyclic-9 run uses 2⁵⁰ bytes, under the common 8 GiB process address-space limit. These are benchmark limits, rather than the library default of 256 MiB; large frames may decline and continue portably at that default. The two focused pairs do not establish default-budget performance.', '',
        '## Correctness and replay', '',
        'All twelve Clang/GCC ASan/UBSan variants and all nine project gates pass, including '
        'the executable/theory build, 567 independent SymPy and 567 Singular reduced-basis comparisons, '
        'both 1134-case driver checks, native/portable comparisons, downstream kernel replay, '
        'axiom audits, benchmark verification, DAG, phase and release-manifest checks.', '',
        'Conformance exercises each maximum dimension and its next value, nonempty rows at '
        'columns 65536 and 131072, shared targets, independent targets, malformed rows, large '
        'sugar labels and parent budget refusals. The logical-bound example attains 2³⁸; one '
        'extra entry exceeds it by 4098. Physical-bound examples have 2³⁴−2 and 2³⁴+1 visits. '
        'Both sides of the former physical boundary remain accepted. The portable models are '
        'also evaluated during the Lean build. No new axiom or `native_decide` is introduced.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`. Source and check manifests, '
        'compiler inputs, collector programs, full logs, outputs and raw samples have individual '
        'SHA-256 bindings.', '', '```bash', 'python3 scripts/bench/groebner_wide_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-wide.md --check', '```', '',
        'Add `--current` when replaying against the measured runtime/check source snapshot. '
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '']
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified packed F2 frames: complete bases, counters, source/check/compiler bindings and samples.')


if __name__ == '__main__':
    main()
