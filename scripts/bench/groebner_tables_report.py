#!/usr/bin/env python3
"""Verify retained known-pivot projection evidence and regenerate its report."""
import argparse
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_binary_guards import blobs
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_tables_extra import study
from scripts.bench.groebner_tables_review import validate
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_trie_report import mean, require, source


def checks(cap, manifest, native=False):
    identity = cap.json('identity.json')
    require(identity['source_fingerprint'] == manifest['source_fingerprint'] and
            identity['source_manifest_sha256'] == hashlib.sha256(manifest['source_manifest'].encode()).hexdigest(),
            'check runtime differs')
    text = cap.text('checks.manifest')
    require(hashlib.sha256(text.encode()).hexdigest() == identity['checks_manifest_sha256'] and
            identity['checks_manifest_sha256'][:12] == identity['checks_fingerprint'], 'check manifest differs')
    blobs(cap, text, 'checks-sources/')
    if native:
        groups = [('native-status.json', ['clang', 'gcc']), ('full-status.json',
                  ['build', 'oracles', 'driver', 'bench', 'dag', 'phase4', 'manifest', 'headers', 'lines'])]
        rows = cap.json('native-status.json')
        require(all(r['sanitize'] == ['address', 'undefined'] and r['variants'] ==
                    ['Native', 'AVX2', 'AVX2Remainder', 'Scalar', 'Remainder', 'ScalarRemainder'] for r in rows),
                'native variant coverage differs')
        require('clang version 23.1.3' in cap.text('native-clang.log') and
                '16.2.0' in cap.text('native-gcc.log'), 'sanitizer compilers differ')
        require('567 unique reduced bases match SymPy' in cap.text('full/oracles.log') and
                '567 reduced bases match Singular' in cap.text('full/oracles.log'), 'basis oracles differ')
    else:
        groups = [('status.json', ['bench', 'dag', 'phase4', 'manifest', 'headers', 'lines'])]
    for path, names in groups:
        rows = cap.json(path)
        require([r['name'] for r in rows] == names and all(r['exit_code'] == 0 and
                all(r[k] == v for k, v in identity.items()) for r in rows), 'failed or stale gate')
    return identity


def kernels(cap, manifest, identity):
    status = cap.json('bench/kernel-status.json')
    require(status['identity'] == identity and status['threads'] == 1 and
            status['manifest'] == {'A': manifest, 'B': manifest} and
            status['binary_sha256'] == status['binary_sha256_after'] ==
            {a: manifest['binary_sha256']['bench'] for a in ['A', 'B']}, 'kernel executable differs')
    rows = status['samples']
    require(len(rows) == 18 and len({r['cpu'] for r in rows}) == 1, 'kernel coverage/CPU differs')
    sizes = [64, 128, 256, 512]
    expected = [(f'complexity/knownProjection/{a}', a) for a in ['A', 'B']] + [
        (f'matched/knownProjection/b{b}-{n}-{a}', a) for b in [0, 1] for n in sizes
        for a in (['A', 'B'] if b == 0 else ['B', 'A'])]
    require([(r['label'], r['arm']) for r in rows] == expected, 'kernel AB/BA schedule differs')
    points = {}
    for row in rows:
        label, arm, command = row['label'], row['arm'], row['command']
        require(row['exit_code'] in [0, 2] and 'Hex.Groebner.Bench.' +
                ('projectionSparse' if arm == 'A' else 'binaryProjection') in command and
                command[command.index('--target-inner-nanos')+1] == '4000000000', 'kernel controls differ')
        result = cap.json('bench/kernels/' + label + '/result.json')['results'][0]
        ps = result['points']
        require(all(p['status'] == 'ok' and p['result_hash'] is not None for p in ps), 'kernel point failed')
        require(int(cap.text('bench/kernels/' + label + '/rss')) > 0, 'missing kernel RSS')
        if label.startswith('complexity/'):
            require(command[command.index('--outer-trials')+1] == '3' and
                    [(p['trial_index'], p['param']) for p in ps] == [(t, n) for t in range(3) for n in sizes],
                    'trial-major complexity schedule differs')
        else:
            require(command[command.index('--outer-trials')+1] == '1' and len(ps) == 1, 'matched point differs')
            points[label] = ps[0]
    out = []
    for n in sizes:
        ps = {(b, a): points[f'matched/knownProjection/b{b}-{n}-{a}'] for b in [0, 1] for a in ['A', 'B']}
        require(all(p['param'] == n for p in ps.values()) and
                len({p['result_hash'] for p in ps.values()}) == 1, 'complete kernel outputs differ')
        out.append((n, mean([ps[b, 'B']['per_call_nanos']/ps[b, 'A']['per_call_nanos'] for b in [0, 1]]),
                    sum(p['below_signal_floor'] for p in ps.values())))
    require(all(flags == 0 for _, _, flags in out), "unflagged kernel contains a signal flag")
    return out, status


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['archive', 'bench', 'eight', 'review', 'report']:
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--check', action='store_true')
    p.add_argument('--current', action='store_true')
    args = p.parse_args()
    cap, bench = Capsule(args.archive), Capsule(args.bench)
    before, after, latest = source(cap, 'baseline'), source(cap, 'candidate'), source(bench, 'bench')
    runtime_id, latest_id = checks(cap, after, True), checks(bench, latest)
    require(runtime_id['checks_manifest_sha256'] == latest_id['checks_manifest_sha256'], 'bench changed runtime checks')
    old, new = listing(after['source_manifest']), listing(latest['source_manifest'])
    changed = {path for path in set(old) | set(new) if old.get(path) != new.get(path)}
    require(changed == {'bench/HexGroebner/Bench.lean', 'bench/HexGroebner/Bench/Projection.lean', 'lakefile.lean'},
            'more than the benchmark changed')
    require(all(after['binary_sha256'][k] == latest['binary_sha256'][k] for k in ['compute', 'compute-reference']) and
            before['compilers'] == after['compilers'] == latest['compilers'] and
            before['native_options'] == after['native_options'] == latest['native_options'], 'driver/compiler binding differs')
    review = Capsule(args.review)
    review_text, final_id = validate(review, latest, bench, checks)
    if args.current:
        current = source_identity()
        require(all(current[k] == final_id[k] for k in ['source_fingerprint', 'source_manifest_sha256',
                    'checks_fingerprint', 'checks_manifest_sha256']), 'current source/checks differ')
    records = []
    for label, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                               ('prime-control', 14, None), ('prime-control-repeat', 14, None)]:
        records.append((label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag})))
    values, status = kernels(bench, latest, latest_id)
    independent = bench.json('independent/status.json')
    require(independent['source_commit'] == latest_id['source_commit'] and independent['seeds'] == [0, 1] and
            independent['sizes'] == [64, 65, 128, 129, 256, 257, 512, 513] and
            independent['exit_codes'] == [0, 0], 'independent benchmark checks differ')
    for seed in [0, 1]:
        require(bench.text(f'independent/run-{seed}.stderr') == '' and
                bench.text(f'independent/run-{seed}.stdout').count('all eight counters passed') == 4,
                'independent benchmark check failed')
    eight = Capsule(args.eight)
    extra = study(eight, latest, checks)
    text = render(cap, bench, before, after, latest, records, values, status)
    text = text.replace("## Verification and reproduction", extra+"## Verification and reproduction", 1)
    text = text.replace("## Known-pivot benchmark", review_text+"## Packed versus sparse reference", 1)
    text = text.replace("  --report reports/bench-results/hexgroebner-tables.md",
                        "  --review reports/bench-results/raw/"+review.path.name+" \\\n  --report reports/bench-results/hexgroebner-tables.md", 1)
    text = text.replace("  --report reports/bench-results/hexgroebner-tables.md",
                        "  --eight reports/bench-results/raw/"+eight.path.name+" \\\n  --report reports/bench-results/hexgroebner-tables.md", 1)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified complete outputs, all counters, source/check snapshots, compiler/ELF bindings and raw samples.')


def render(cap, bench, before, after, latest, records, values, status):
    lines = ['# Packed F₂ known-pivot projection', '',
        'The selected provider uses four-row known-pivot projection. Direct packed-before/after and packed-versus-sparse '
        'comparisons are reported separately. Full-system results are mixed and do not establish overall performance leadership. '
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '',
        'Projection visits known pivots in column order before target-pivot installation. Groups of four dense known pivots '
        'use sixteen exact XOR combinations. Triangular pivot decisions retain the sparse provider’s source charges, reduction counts '
        'and maximum source sugar even when combinations cancel. Sparse pivots interrupt groups. Ordinary F₂ polynomial semantics apply.', '',
        'The opt-in binary provider keeps its 2^28 physical and 2^32 logical call bounds. Admission accounts for the actual dense '
        'groups; tests cover all 64 triangular four-pivot patterns and all sixteen incoming masks, sparse interruptions, '
        'payloads of all five private buffers and sharp physical/logical boundaries. Default binary policy is unchanged.', '',
        '## Matched full-system observations', '',
        f'Baseline `{before["source_fingerprint"]}`; tables `{after["source_fingerprint"]}`. Each pass alternates adjacent AB/BA '
        'pairs on one leased CPU with one algorithm thread. The repeat is the sole unchanged repeat. F₂ uses binary pivots in both arms; '
        'prime controls disable them in both arms (p = 32003 and 2147483647). All use degree scheduling and grevlex. '
        'Every one of the 192 processes completed; all 96 paired complete reduced bases and every logical statistic agree. '
        'Candidate production yields unchecked candidates. Certification, independent verification and kernel replay are separate correctness checks, '
        'and are excluded from these timing ratios.', '',
        '| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |',
        '|---|---:|---:|---:|---:|---|---|']
    for label, r in records:
        a = r['recorded']
        lines.append(f'| {label} | {r["meta"]["cpu"]} | {a["geomean"]:.6f} | {a["family_balanced_geomean"]:.6f} | '
                     f'{r["candidate"]:.6f} | {a["minimum"]:.6f} / {a["median"]:.6f} / {a["maximum"]:.6f} | '
                     f'{a["peak_rss_kib"]["A"]} / {a["peak_rss_kib"]["B"]} |')
    first, repeat = [r['recorded'] for _, r in records[:2]]
    lines += ['', f'Whole-process F₂ peak RSS is {100*(first["peak_rss_kib"]["B"]/first["peak_rss_kib"]["A"]-1):.2f}% and '
        f'{100*(repeat["peak_rss_kib"]["B"]/repeat["peak_rss_kib"]["A"]-1):.2f}% higher in these two passes. '
        'These observations include runtime/allocator memory and do not isolate the private buffers. '
        'The unchanged prime-route aggregate ratios also vary between '
        f'{records[2][1]["recorded"]["geomean"]:.6f} and {records[3][1]["recorded"]["geomean"]:.6f}; '
        'the F₂ results do not establish an overall speedup.', '',
        '| Family | F₂ first / repeat process B/A | Prime first / repeat process B/A |', '|---|---|---|']
    data = [r['recorded']['per_family'] for _, r in records]
    for family in data[0]:
        prime = f'{data[2][family]:.6f} / {data[3][family]:.6f}' if family in data[2] else 'not in prime suite'
        lines.append(f'| {family} | {data[0][family]:.6f} / {data[1][family]:.6f} | {prime} |')
    lines += ['', 'Startup outliers, host activity, all completed samples and RSS records are retained. The MQ family ratios are below one in both passes, '
        'while the family-balanced first pass regresses. The small opt-in suite is diagnostic, not the SPEC’s leadership acceptance suite.', '',
        '## Known-pivot benchmark', '',
        f'Benchmark snapshot `{latest["source_fingerprint"]}` adds exactly three benchmark/registration files to the tested runtime. '
        'Both computation executables are byte-identical to the full-system snapshot. '
        f'Native compiler {latest["compilers"]["native"]["version"].splitlines()[0]}, Lean toolchain {latest["toolchain"]}, '
        'native options and compiler digests match both full-system arms. Exact compiler, host and ISA context is in the manifests.', '',
        'For n known rows in 2n columns, the leading block is the identity and tails are deterministic dense vectors. Each of n targets '
        'is the sum of the known rows plus a distinct free-column unit. The projected targets are therefore independently known. '
        'Every target selects every known head: this is a deliberately favorable table workload. Preparation is excluded; '
        'validation, table construction, elimination, independent unit checks and complete row/sugar/counter hashing are included. '
        'The sparse comparison uses the reference provider with bounded native phases; it is not a fully portable executable.', '',
        f'One CPU lease (CPU {status["samples"][0]["cpu"]}), one thread, four-second inner targets, three fixed trial-major complexity trials '
        'and adjacent matched AB/BA comparisons. No below-signal flags occurred in matched samples.', '',
        '| n | Packed / sparse time | Below-signal flags |', '|---:|---:|---:|']
    for n, ratio, flags in values:
        lines.append(f'| {n} | {ratio:.6f} | {flags} |')
    lines += ['', 'Independent compiled checks also cover 64/65, 128/129, 256/257 and 512/513, including known rank, '
        'all independent target units, pivot flags, sugars and all eight counters. All complete benchmark result hashes agree between providers.', '',
        '## Verification and reproduction', '',
        'The most recent published [msolve comparisons](hexgroebner-binary.md) concern an earlier packed runtime: '
        'Hex/msolve family-balanced process ratios were 2.199843 and 1.907506. The present runtime has not demonstrated '
        'the SPEC’s fastest-open-source milestone. Ratios from these different campaigns cannot be chained.', '',
        'The runtime snapshot passed all twelve Clang/GCC ASan/UBSan native variants and all nine required project checks: build, '
        'independent oracles, driver checks, fast benchmark check, DAG, phase 4, release manifest, headers and line counts. '
        'Oracles compare 567 bases each with SymPy and Singular, with driver and downstream kernel replay/axiom checks in the retained logs. '
        'The later benchmark-only snapshot passed six benchmark/source checks and the independent compiled checks; its runtime/check source and computation ELF bindings are verified separately.', '',
        'Raw capsules contain source/check blobs, per-file SHA-256 manifests, commands, all samples and retained failures. '
        'Frozen executables and perf data stay in the local measurement store; executable hashes are retained in the capsules.', '',
        f'- `{cap.path.name}`: SHA-256 `{cap.sha256}`.',
        f'- `{bench.path.name}`: SHA-256 `{bench.sha256}`.', '',
        '```sh', 'python3 scripts/bench/groebner_tables_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        f'  --bench reports/bench-results/raw/{bench.path.name} \\',
        '  --report reports/bench-results/hexgroebner-tables.md --check --current', '```', '']
    return '\n'.join(lines)


if __name__ == '__main__':
    main()
