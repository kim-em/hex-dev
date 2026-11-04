#!/usr/bin/env python3
"""Verify source-pointer preparation against the preceding batched provider."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_prepare_report import kernels, render
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
    require(set(a) == set(b) and {k for k in a if a[k] != b[k]} ==
            {'HexGroebner/ffi/monomial_hit.c'} and before['compilers'] == after['compilers'] and
            before['native_options'] == after['native_options'], 'pointer experiment controls differ')
    identity = checks(cap, after, True)
    if args.current:
        current = source_identity()
        require(all(current[k] == identity[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current source/checks differ')
    records = [(label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag}))
               for label, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                                          ('prime-control', 14, None), ('prime-control-repeat', 14, None)]]
    values, cpu = kernels(cap, before, after, identity, digest_commit=before['commit'])
    text = render(cap, before, after, records, values, cpu)
    start = text.index('The native product planner')
    end = text.index('\n\nBaseline', start)
    text = text[:start] + ('The native planner validates each source identifier and precomputes its row pointer '
        'before coordinate traversal. This removes repeated row-index multiplications from the inner loop. '
        'The private pointer array stays within the existing 32 KiB scratch bound. Exact hashes, collision '
        'comparisons, output bytes, work charges, overflow checks and atomic refusal are unchanged. '
        'The independently compiled digest checks use the preceding provider and validate every matched '
        'and complexity result of both arms against its successful scalar comparison.') + text[end:]
    text = text.replace('# Batched monomial preparation', '# Precomputed source rows in monomial preparation', 1)
    text = text.replace('groebner_prepare_report.py', 'groebner_pointer_report.py')
    text = text.replace('hexgroebner-prepare.md', 'hexgroebner-pointers.md')
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified pointer preparation, complete results, counters, source/check/compiler bindings and samples.')


if __name__ == '__main__':
    main()
