#!/usr/bin/env python3
"""Verify the retained packed F2 pivot allocation experiment."""
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
    require(set(a) == set(b) and {path for path in a if a[path] != b[path]} ==
            {'HexGroebner/ffi/matrix_eliminate.c'},
            'packed F2 pivot runtime delta differs')
    require(before['compilers'] == after['compilers'] and
            before['native_options'] == after['native_options'], 'compiler controls differ')
    identity = checks(cap, after, True)
    if args.current:
        current = source_identity()
        require(all(current[k] == identity[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current source/checks differ')
    records = [(label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag}))
               for label, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                                          ('prime-control', 14, None), ('prime-control-repeat', 14, None)]]
    lines = ['# Reuse existing packed F₂ pivot rows', '',
        'Packed F₂ elimination reads sparse pivot columns from the existing pivot row. '
        'It omits a temporary native pivot wrapper and its duplicate array entry for each '
        'installed pivot. The private bit rows and metadata, sparse/word/table projection '
        'choices, canonical output, immutable aliases and logical work counters are unchanged. '
        'Ordinary prime-field scans retain their native pivot wrappers.', '',
        f'Baseline `{before["source_fingerprint"]}`; candidate `{after["source_fingerprint"]}`. '
        'Only the native matrix elimination source changes in the runtime manifest. '
        f'Native compiler `{compiler_name(after, "native")}`, generated-C compiler '
        f'`{compiler_name(after, "lean")}` (SDK), native flags and benchmark inputs match between arms.', '',
        '## Matched full-system observations', '',
        'Each sweep leases one CPU and uses one algorithm thread. Adjacent pairs alternate AB/BA. '
        'Every completed sample, outlier, failure and RSS observation is retained. The second pass '
        'is the sole unchanged repeat; no further unchanged repeat is collected. F₂ enables binary '
        'pivots in both arms; prime controls disable them at p = 32003 and 2147483647. All use degree '
        'scheduling, grevlex and complete reduced output.', '',
        '| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |',
        '|---|---:|---:|---:|---:|---|---|']
    for label, result in records:
        r, m = result['recorded'], result['meta']
        lines.append(f'| {label} | {m["cpu"]} | {r["geomean"]:.6f} | '
            f'{r["family_balanced_geomean"]:.6f} | {result["candidate"]:.6f} | '
            f'{r["minimum"]:.6f} / {r["median"]:.6f} / {r["maximum"]:.6f} | '
            f'{r["peak_rss_kib"]["A"]} / {r["peak_rss_kib"]["B"]} |')
    lines += ['', 'All 192 processes completed. All 96 paired complete reduced bases and every logical '
        f'statistic agree. The F₂ process ratios are {records[0][1]["recorded"]["geomean"]:.6f} and '
        f'{records[1][1]["recorded"]["geomean"]:.6f}; both passes show a modest reduction '
        'on this development suite. They do not establish performance leadership. Per-family differences, including '
        'small-system regressions, remain visible below. Candidate production returns unchecked '
        'candidates; certification, independent native verification and kernel checking are separate '
        'checks excluded from these timing ratios.', '',
        '| Family | F₂ first / repeat process B/A | Prime first / repeat process B/A |', '|---|---|---|']
    for family in records[0][1]['recorded']['per_family']:
        def pair(indices):
            return ' / '.join(f'{records[i][1]["recorded"]["per_family"][family]:.6f}' for i in indices)
        prime = pair([2, 3]) if family in records[2][1]['recorded']['per_family'] else 'not in prime suite'
        lines.append(f'| {family} | {pair([0, 1])} | {prime} |')
    lines += ['', 'These diagnostic suites are development inputs, not the SPEC’s balanced, held-out '
        'leadership corpus. No fresh external-comparator result is inferred for this implementation, '
        'and ratios from separate stages are not multiplied.', '',
        '## Correctness and replay', '',
        'All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include '
        '567 unique SymPy and 567 Singular reduced-basis comparisons, both 1134-case driver checks, '
        'native/portable comparisons, downstream kernel replay, axiom audits and bench verification.', '',
        'The existing compiled conformance covers shared input snapshots, sparse and word '
        'updates, known-pivot projection, high pivot indices, malformed rows and exact '
        'budget/refusal boundaries. All native paths agree with their portable models. '
        'The change retains each row in the existing pivot array throughout the frame; '
        'sparse reads borrow that row without retaining another wrapper. Source/check '
        'manifests, complete logs, collector programs and every raw sample are bound by '
        'per-file SHA-256 hashes.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '', '```bash',
        'python3 scripts/bench/groebner_pivot_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-pivots.md --check', '```', '',
        'Add `--current` when replaying against the measured runtime/check source snapshot. '
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '']
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified packed F2 pivot reuse: complete bases, all counters, source/check/compiler bindings and samples.')


if __name__ == '__main__':
    main()
