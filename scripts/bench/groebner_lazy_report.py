#!/usr/bin/env python3
"""Replay lazy packed-pivot comparisons and their verification snapshots."""
import argparse
import hashlib
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


def stage(cap, repeated=False):
    before, after = source(cap, 'baseline'), source(cap, 'candidate')
    a, b = listing(before['source_manifest']), listing(after['source_manifest'])
    require(set(a) == set(b) and {p for p in a if a[p] != b[p]} ==
            {'HexGroebner/ffi/matrix_eliminate.c'}, 'lazy runtime delta differs')
    require(before['compilers'] == after['compilers'] and
            before['native_options'] == after['native_options'], 'compiler controls differ')
    identity = checks(cap, after, True)
    probe = cap.text('checks-sources/scripts/ci/check_groebner_matrix.py')
    require('#define HEX_GROEBNER_BINARY_POISON 1' in probe, 'poisoned storage was not tested')
    records = []
    cohorts = [('f2-true', 10, 'true'), ('prime-control', 14, None), ('hard-cyclic9-f2', 1, 'true')]
    if repeated:
        cohorts.append(('hard-cyclic9-f2-repeat', 1, 'true'))
    for label, count, flag in cohorts:
        result = sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag})
        for row in result['meta']['samples']:
            name = f'{row["case"]}-b{row["block"]}-{row["arm"]}.stdout'
            require(cap.json('candidate/'+label+'/'+name)['batchSize'] == 1024,
                    'batch size differs from the library default')
        records.append((label, result))
    return before, after, identity, records


def audited(cap, measured, measured_cap):
    current = source(cap, 'audit')
    a, b = listing(measured['source_manifest']), listing(current['source_manifest'])
    require(set(a) == set(b) and {p for p in a if a[p] != b[p]} == {'lakefile.lean'},
            'configuration refresh changed implementation sources')
    old, new = listing(measured_cap.text('checks.manifest')), listing(cap.text('checks.manifest'))
    require(set(old) == set(new) and {p for p in old if old[p] != new[p]} == {'.github/workflows/ci.yml'},
            'configuration refresh changed verification sources')
    require(current['binary_sha256'] == measured['binary_sha256'] and
            current['compilers'] == measured['compilers'] and
            current['native_options'] == measured['native_options'],
            'configuration refresh changed executables or compiler controls')
    return current, checks(cap, current, True)


DOC_OLD = 'chunks with identical rows, provenance and counters. Untraced native 64-bit calls first\ntry a complete frame bounded by 4096 columns, 1024 reducers, 64 targets and\n`2^20` work. Explicit `binaryPivots` over F2 permits 16384 columns, 16384\nreducers and 1024 targets, bounded by `2^32` logical work and `2^28` physical\nvisits. Private bitmap and metadata bytes additionally fit the packed-byte allowance.'
DOC_NEW = 'chunks with identical rows, provenance and counters. Untraced native 64-bit calls first\ntry a complete frame under `Elimination.fits`, which specifies separate dimension\nceilings and joint work bounds for ordinary and explicitly requested packed F2\nframes. Private bitmap and metadata bytes additionally fit the packed-byte allowance.'


def documented(cap, before, before_cap):
    current = source(cap, 'documentation')
    a, b = listing(before['source_manifest']), listing(current['source_manifest'])
    path = 'HexGroebner/Elimination.lean'
    require(set(a) == set(b) and {p for p in a if a[p] != b[p]} == {path},
            'documentation audit changed more than the entry-point source')
    prior = before_cap.text('audit/root-sources/'+path)
    require(prior.count(DOC_OLD) == 1 and
            cap.text('documentation/root-sources/'+path) == prior.replace(DOC_OLD, DOC_NEW, 1),
            'entry-point change is not exactly the bounds documentation')
    require(current['binary_sha256'] == before['binary_sha256'] and
            current['compilers'] == before['compilers'] and
            current['native_options'] == before['native_options'],
            'documentation changed executable bytes or compiler controls')
    identity = cap.json('identity.json')
    require(cap.text('checks.manifest') == before_cap.text('checks.manifest') and
            identity['source_fingerprint'] == current['source_fingerprint'] and
            identity['source_manifest_sha256'] == hashlib.sha256(current['source_manifest'].encode()).hexdigest() and
            identity['checks_manifest_sha256'] == hashlib.sha256(cap.read('checks.manifest')).hexdigest() and
            identity['checks_fingerprint'] == identity['checks_manifest_sha256'][:12],
            'documentation identity or unchanged checks differ')
    return current, identity


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['archive', 'initial', 'report']:
        parser.add_argument('--'+name, type=Path, required=True)
    parser.add_argument('--audit', type=Path)
    parser.add_argument('--docs', type=Path)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--current', action='store_true')
    args = parser.parse_args()
    initial, final = Capsule(args.initial), Capsule(args.archive)
    old_before, old_after, _, old = stage(initial)
    before, after, identity, records = stage(final, True)
    require(before == old_before, 'stages have different baselines')
    require('mixed frames did not skip sparse packed-row initialization' in
            final.text('checks-sources/scripts/ci/check_groebner_matrix.py'),
            'final sparse-row initialization assertion missing')
    audit = Capsule(args.audit) if args.audit else None
    current_manifest = after
    if audit:
        current_manifest, identity = audited(audit, after, final)
    docs = Capsule(args.docs) if args.docs else None
    if docs:
        require(audit is not None, 'documentation audit requires the configuration audit')
        current_manifest, identity = documented(docs, current_manifest, audit)
    if args.current:
        current = source_identity()
        require(all(current[k] == identity[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current source/checks differ')
    lines = ['# Lazy packed F₂ pivot initialization', '',
        'Packed F₂ pivots initialize their private row only when dense enough to use word XOR. '
        'Sparse pivots use their existing immutable column lists. One shared native density predicate '
        'guards initialization, scans, projection and four-row tables. Tables require every byte of a '
        'dense row to initialize, including words outside its support. The accumulator initializes '
        'separately. Complete virtual scratch reservation, portable admission, exact results and all '
        'logical counters are unchanged. Allocator behaviour determines how much resident memory is saved.', '',
        'The option remains disabled by default. These are ordinary F₂ polynomials, without Boolean '
        'quotient relations. Existing allocation failure and late byte-refusal costs remain; '
        'the packed-payload allowance does not bound total heap memory.', '',
        f'Baseline `{before["source_fingerprint"]}`; initial lazy version `{old_after["source_fingerprint"]}`; '
        f'final shared-predicate version `{after["source_fingerprint"]}`. Each changes only the native '
        'matrix source relative to the baseline runtime manifest. Native compiler '
        f'`{compiler_name(after, "native")}`, generated-C compiler `{compiler_name(after, "lean")}` '
        '(SDK), compiler flags and inputs match.', '',
        '## Matched observations', '',
        'The initial stage retains 100 completed processes / 50 equal complete-basis pairs, and the final stage retains 104 / 52. Both have identical '
        'logical statistics. Comparisons use one leased CPU, one algorithm thread, adjacent AB then BA, '
        'degree scheduling, grevlex, batch size 1024 and complete monic reduced output. Binary pivots '
        'are enabled in both F₂ arms. Moderate cohorts use a 16 GiB packed-payload allowance; the '
        'Cyclic-9 focus uses 2⁵⁰ bytes under an 8 GiB process address-space limit. These are benchmark '
        'budgets rather than the library default of 256 MiB. All completed samples and RSS observations '
        'are retained. The final focused comparison was inconclusive, so one unchanged Cyclic-9 repeat is included; there is no further unchanged repeat.', '',
        'The Cyclic-9 input also occurs in the primary fixed corpus and motivated the larger-frame '
        'work. It is an in-sample diagnostic, reported separately from the development cohorts. '
        'Process time includes initialization, parsing, candidate production, final interreduction '
        'and complete output. Certificate generation, independent native certification and kernel '
        'checking are separate.', '',
        '| Stage / cohort | CPU | Process B/A | Family balanced B/A | Candidate B/A | Pair min / max | Peak RSS A / B (KiB) |',
        '|---|---:|---:|---:|---:|---|---|']
    for name, rows in [('initial', old), ('final', records)]:
        for label, result in rows:
            r = result['recorded']
            lines.append(f'| {name} / {label} | {result["meta"]["cpu"]} | {r["geomean"]:.6f} | '
                f'{r["family_balanced_geomean"]:.6f} | {result["candidate"]:.6f} | '
                f'{r["minimum"]:.6f} / {r["maximum"]:.6f} | '
                f'{r["peak_rss_kib"]["A"]} / {r["peak_rss_kib"]["B"]} |')
    focused = (records[2][1]['recorded']['geomean']*records[3][1]['recorded']['geomean'])**0.5
    lines += ['', f'The final focused result across all four pairs has process B/A {focused:.6f}.', '', 'These observations do not establish a broad speedup, fixed-corpus completion, '
        'held-out performance or an external-comparator milestone. Ratios from successive '
        'implementation stages are not multiplied.', '',
        '## Correctness and replay', '',
        'Both stages pass all twelve Clang/GCC ASan/UBSan variants and all nine project gates, '
        'including executable/theory builds, 567 SymPy and 567 Singular basis comparisons, '
        'both 1134-case driver checks, downstream kernel replay, axiom audits and project '
        'DAG/phase/release checks. Every native variant fills private row storage with 0xa5 '
        'before explicit initialization. Final tests also assert that mixed frames initialize '
        'strictly fewer packed rows than installed pivots, exercise a nonempty table-saving '
        'straddle at 2³⁴−2 / 2³⁴+1, and project dense rows at the highest full and partial word. '
        'Runtime-seeded probes avoid initialization-time evaluation; their sugar labels remain '
        'bounded even for seeds above 2⁶³.', '',
        f'Initial capsule `{initial.path.name}`: SHA-256 `{initial.sha256}`. '
        f'Final capsule `{final.path.name}`: SHA-256 `{final.sha256}`. '
        'They bind full source/check manifests, compiler inputs, raw samples and complete logs. '
        'Earlier failed setup/check attempts remain diagnostic records.', '', '```bash',
        'python3 scripts/bench/groebner_lazy_report.py \\',
        f'  --initial reports/bench-results/raw/{initial.path.name} \\',
        f'  --archive reports/bench-results/raw/{final.path.name} \\',
        '  --report reports/bench-results/hexgroebner-lazy-pivots.md --check', '```', '',
        'Add `--current` for the measured final runtime/check snapshot. '
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '']
    if audit:
        section = ['', '## Current configuration audit', '',
            f'Configuration-audited runtime `{source(audit, "audit")["source_fingerprint"]}` changes only the Lake '
            'registrations for unrelated RCF modules relative to the measured final snapshot. '
            'The only verification-manifest change is CI disk reclamation. All three freshly '
            'frozen compute/reference/bench executables have exactly the measured SHA-256 hashes; '
            'compiler controls match. All twelve native sanitizer variants and all nine project '
            'gates pass on this current snapshot.', '',
            f'Audit capsule `{audit.path.name}`: SHA-256 `{audit.sha256}`. No timing sample is '
            'replaced or inferred from the configuration update.', '']
        # The audit argument binds --current to the configuration used now.
        pos = lines.index('```bash')
        lines[pos:pos] = section
        pos = lines.index('  --report reports/bench-results/hexgroebner-lazy-pivots.md --check')
        lines.insert(pos, f'  --audit reports/bench-results/raw/{audit.path.name} '+chr(92))
    if docs:
        section = ['', '## Public documentation audit', '',
            f'Documentation-audited runtime `{current_manifest["source_fingerprint"]}` changes only '
            'the public elimination comment to refer to `Elimination.fits`. The exact comment '
            'replacement is checked; all executable definitions and verification sources are '
            'unchanged. A fresh isolated build produces the same three executable SHA-256 hashes. '
            'No timing or test result is replaced or relabelled.', '',
            f'Documentation capsule `{docs.path.name}`: SHA-256 `{docs.sha256}`.', '']
        pos = lines.index('```bash')
        lines[pos:pos] = section
        pos = lines.index('  --report reports/bench-results/hexgroebner-lazy-pivots.md --check')
        lines.insert(pos, f'  --docs reports/bench-results/raw/{docs.path.name} '+chr(92))
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified lazy packed pivots: both source/check snapshots and all 204 process samples.')


if __name__ == '__main__':
    main()
