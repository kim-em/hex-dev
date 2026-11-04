#!/usr/bin/env python3
"""Verify the retained F2 full-basis comparison after batched preparation."""
import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_comparator_report import msolve
from scripts.bench.groebner_prepare_report import compiler_name
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
    manifest = source(cap, 'candidate')
    identity = checks(cap, manifest, True)
    if args.current:
        current = source_identity()
        require(all(current[k] == identity[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current source/checks differ')
    families = dict(cyclic=2, kat=2, eco=2, noon=2, reimer=2, minrank=2,
                    **{'dense-quadratic': 2, 'mq': 6})
    result, meta = msolve(cap, 'candidate', expected_families=families, moduli={2})
    require(meta['requested_scheduling']['A'] == 'degree' and
            meta['requested_dense_pivots']['A'] == 'false' and
            meta['requested_binary_pivots']['A'] == 'true', 'Hex policy differs')
    for row in meta['samples']:
        if row['arm'] == 'A':
            command = row['command']
            require(command[command.index('--dense-pivots')+1] == 'false', 'dense policy differs')
            output = cap.json(f'candidate/msolve/{row["case"]}-b{row["block"]}-A.stdout')
            inp = cap.json(f'candidate/msolve/inputs/{row["case"]}.json')
            require(output['p'] == inp['p'] == 2 and output['variables'] == inp['variables'] and
                    output['order'] == inp['order'] == 'grevlex' and output['scheduling'] == 'degree' and
                    output['binaryPivots'] and not output.get('densePivots', False) and
                    int(output['randomState']) == 0, 'candidate contract differs')
    largest = sorted(result['per_family'].items(), key=lambda pair: pair[1], reverse=True)[:2]
    gaps = ' and '.join(f'`{family}` ({ratio:.6f}×)' for family, ratio in largest)
    lines = ['# F₂ comparator gap after batched preparation', '',
        f'The frozen implementation `{manifest["source_fingerprint"]}` remains slower than pinned msolve '
        f'overall on this diagnostic suite: process geometric mean {result["geomean"]:.6f}×, '
        f'equal-family geometric mean {result["family_balanced_geomean"]:.6f}×. '
        f'The largest family ratios are {gaps}. These observations do not establish '
        'performance leadership or identify a necessary language/runtime change. '
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '',
        f'CPU {meta["cpu"]}, one algorithm thread, adjacent AB/BA comparisons. All forty processes '
        'completed and all twenty paired complete reduced bases agree. Inputs use ordinary F₂, '
        'grevlex and explicit degree scheduling for Hex; msolve uses full reduced output (`-g 2`), '
        'linear algebra mode 2 and one thread. This is the first observation of this implementation '
        'against this comparator. No unchanged repeat is collected.', '',
        'Both arms use the same GNU time wrapper for peak RSS. Process time includes launch, initialization, '
        'parsing, computation and complete output. Candidate production returns unchecked candidates. '
        'Certificate generation, independent final verification and kernel replay remain distinct and '
        'are excluded from these timing ratios. This ten-case diagnostic suite does not satisfy the '
        'SPEC’s field coverage, balanced/held-out suite or fastest-open-source acceptance requirements.', '',
        f'Hex native C uses `{compiler_name(manifest, "native")}`; generated C uses '
        f'`{compiler_name(manifest, "lean")}` (SDK). The comparator is msolve '
        f'commit `{meta["msolve_commit"]}`, built using Clang 23.1.3 with `-O3 -march=native`. '
        'The source state, engine/shared-library and executable digests, recorded compile commands, '
        'toolchain and ISA context are retained. Compiler/tuning differences are part of this measured gap.', '',
        '| Process Hex / msolve | Equal-family Hex / msolve | Min / median / max | Peak RSS Hex / msolve (KiB) |',
        '|---:|---:|---|---|',
        f'| {result["geomean"]:.6f} | {result["family_balanced_geomean"]:.6f} | '
        f'{result["minimum"]:.6f} / {result["median"]:.6f} / {result["maximum"]:.6f} | '
        f'{result["peak_rss_kib"]["A"]} / {result["peak_rss_kib"]["B"]} |', '',
        '| Family | Hex / msolve process time |', '|---|---:|']
    lines += [f'| {family} | {ratio:.6f} |' for family, ratio in result['per_family'].items()]
    lines += ['', 'Every completed sample, outlier, full output, resource failure and memory observation is '
        'retained. There were no failed or timed-out processes. The capsule also binds the implementation '
        'to all twelve Clang/GCC ASan/UBSan variants and all nine project checks, including independent '
        'basis oracles and downstream kernel replay. Timing ratios from different implementation stages '
        'are not multiplied to infer cumulative gains.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '', '```bash',
        'python3 scripts/bench/groebner_prepare_comparator.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-prepare-msolve.md --check', '```', '']
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified all twenty complete bases, source/check bindings and compiler/engine/executable provenance.')


if __name__ == '__main__':
    main()
