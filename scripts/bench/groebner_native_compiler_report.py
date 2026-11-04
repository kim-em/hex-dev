#!/usr/bin/env python3
"""Verify the fully audited native compiler profile on the pointer runtime."""
import argparse
import hashlib
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_binary_guards import blobs
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_prepare_report import compiler_name
from scripts.bench.groebner_trie_report import require, source


def gates(cap, after):
    identity, native = cap.json('identity.json'), cap.json('native-identity.json')
    text = cap.text('checks.manifest')
    require(identity['source_fingerprint'] == after['source_fingerprint'] and
            identity['source_manifest_sha256'] == hashlib.sha256(after['source_manifest'].encode()).hexdigest() and
            identity['checks_manifest_sha256'] == hashlib.sha256(text.encode()).hexdigest() and
            all(identity[k] == native[k] for k in identity if k != 'source_commit'),
            'compiler-profile check identities differ')
    blobs(cap, text, 'checks-sources/')
    rows = cap.json('native-status.json')
    require([r['name'] for r in rows] == ['clang', 'gcc'] and all(r['exit_code'] == 0 and
            all(r[k] == v for k, v in native.items()) and r['sanitize'] == ['address', 'undefined'] and
            r['variants'] == ['Native', 'AVX2', 'AVX2Remainder', 'Scalar', 'Remainder', 'ScalarRemainder']
            for r in rows), 'native variant coverage differs')
    full, config = cap.json('full-status.json'), cap.json('configuration.json')
    require([r['name'] for r in full] == ['build', 'oracles', 'driver', 'bench', 'dag', 'phase4',
            'manifest', 'headers', 'lines'] and all(r['exit_code'] == 0 and
            all(r[k] == v for k, v in identity.items()) and r['configuration'] == config for r in full),
            'compiler project coverage differs')
    require(config['hexGroebnerCC'] == after['native_options']['hexGroebnerCC'],
            'audited compiler configuration differs')
    for path, digest in config['wrapper_sha256'].items():
        p = PurePosixPath(path)
        require(hashlib.sha256(cap.read('profile-inputs/'+p.parent.name+'/'+p.name)).hexdigest() == digest,
                'compiler-routing input differs')
    witness = cap.json('driver-identity.json')
    expected = {k: after['binary_sha256'][k] for k in ['compute', 'compute-reference']}
    require(witness['identity'] == identity and witness['after_full_gates'] and
            witness['binary_sha256'] == expected and
            witness['full_status_sha256'] == hashlib.sha256(cap.read('full-status.json')).hexdigest() and
            witness['configuration_sha256'] == hashlib.sha256(cap.read('configuration.json')).hexdigest(),
            'final driver identity audit differs')
    names = {'row_update.o', 'monomial_hit.o', 'matrix_state.o', 'matrix_eliminate.o', 'matrix_scan.o'}
    for row in full:
        objects = row['native_objects']
        require({PurePosixPath(o['path']).name for o in objects} == names and
                all('clang version 23.1.3' in o['compiler_comment'] for o in objects) and
                {PurePosixPath(o['path']).name: o['sha256'] for o in objects} ==
                witness['native_objects_sha256'], 'native objects changed compiler or contents')
    require('567 unique reduced bases match SymPy' in cap.text('full/oracles.log') and
            '567 reduced bases match Singular' in cap.text('full/oracles.log') and
            '"-target-cpu" "x86-64"' in cap.text('diagnostics/pointers-clang23-target.stderr'),
            'oracle coverage or effective CPU differs')
    require("clang version 21.1.8" in cap.text('diagnostics/pointers-clang23-full.log') and
            'AssertionError' in cap.text('diagnostics/pointers-clang23-full.log'),
            'initial compiler-routing failure was not retained')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    cap = Capsule(args.archive)
    before, after = source(cap, 'baseline'), source(cap, 'candidate')
    require(before['source_manifest'] == after['source_manifest'] and
            before['compilers']['lean'] == after['compilers']['lean'] and
            before['compilers']['other_native'] == after['compilers']['other_native'],
            'more than the Groebner native compiler changed')
    require('clang version 21.1.8' in before['compilers']['native']['version'] and
            'clang version 23.1.3' in after['compilers']['native']['version'], 'compiler versions differ')
    gates(cap, after)
    records = [(label, sweep(cap, 'candidate/'+label, before, after, count, {'A': flag, 'B': flag}))
               for label, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                                          ('prime-control', 14, None), ('prime-control-repeat', 14, None)]]
    lines = ['# Audited Groebner native compiler profile', '',
        f'The same runtime `{after["source_fingerprint"]}` is built with native '
        f'`{compiler_name(before, "native")}` and `{compiler_name(after, "native")}`. '
        f'Other native libraries retain `{compiler_name(after, "other_native")}` and generated C '
        f'retains `{compiler_name(after, "lean")}` (SDK). The effective target is generic x86-64, '
        'with no native-CPU tuning flag. This profile has a complete source-bound correctness audit; '
        'it does not establish an overall F₂ performance gain or leadership.', '',
        'All 192 processes completed. All 96 paired complete reduced bases and every logical statistic '
        'agree. Each sweep leases one CPU, uses one algorithm thread, alternates adjacent AB/BA pairs '
        'and retains every completed sample, outlier, failure and RSS observation. The repeat is the '
        'sole unchanged repeat. Inputs use degree scheduling and grevlex. F₂ enables binary pivots in '
        'both arms; prime controls disable them at p = 32003 and 2147483647.', '',
        '| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |',
        '|---|---:|---:|---:|---:|---|---|']
    for label, result in records:
        r, m = result['recorded'], result['meta']
        lines.append(f'| {label} | {m["cpu"]} | {r["geomean"]:.6f} | '
            f'{r["family_balanced_geomean"]:.6f} | {result["candidate"]:.6f} | '
            f'{r["minimum"]:.6f} / {r["median"]:.6f} / {r["maximum"]:.6f} | '
            f'{r["peak_rss_kib"]["A"]} / {r["peak_rss_kib"]["B"]} |')
    lines += ['', '| Family | F₂ first / repeat B/A | Prime first / repeat B/A |', '|---|---|---|']
    for family in records[0][1]['recorded']['per_family']:
        def pair(indices):
            return ' / '.join(f'{records[i][1]["recorded"]["per_family"][family]:.6f}' for i in indices)
        prime = pair([2, 3]) if family in records[2][1]['recorded']['per_family'] else 'not in prime suite'
        lines.append(f'| {family} | {pair([0, 1])} | {prime} |')
    lines += ['', 'Candidate production returns unchecked candidates. Certificate generation, independent '
        'native verification and kernel checking remain separate and are excluded from timing. These '
        'development inputs are not the SPEC’s balanced, held-out leadership suite. This profile does '
        'not demonstrate a necessary language/runtime limitation. The library’s host-compiler default '
        'is unchanged; the native compiler remains explicitly configurable.', '',
        '## Configuration and correctness audit', '',
        'All twelve Clang/GCC ASan/UBSan variants cover the identical runtime/check source. All nine '
        'project gates also passed under the measured compiler configuration, including the independent '
        'basis oracles, both driver corpora, native/portable comparisons and downstream kernel replay. '
        'The audit verifies the compiler stamp and exact object hash of all five Groebner C objects '
        'after every gate. The driver executables match the frozen timed binaries after the complete '
        'audit; the collector asserts this identity at every gate.', '',
        'An initial audit caught downstream builds reverting to the host compiler. Its failed object '
        'stamp check and complete logs are retained. The successful audit routes the five Groebner '
        'kernel sources through Clang 23 even when a downstream project selects the dependency’s '
        'default `cc`; other native sources keep Clang 21. Both routing wrappers, the Lake configuration, '
        'their hashes and all object/executable identity records are retained. No timing is inferred '
        'from these correctness runs.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '', '```bash',
        'python3 scripts/bench/groebner_native_compiler_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-native-compiler.md --check', '```', '',
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '']
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified compiler profile: complete bases/counters, all nine gates, native object and driver identities.')


if __name__ == '__main__':
    main()
