#!/usr/bin/env python3
"""Reproduce retained unselected F4 implementation/compiler experiments."""
import argparse
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_binary_guards import blobs
from scripts.bench.groebner_binary_report import sweep
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_tables_report import checks
from scripts.bench.groebner_trie_report import require, source


class View:
    def __init__(self, cap, prefix):
        self.cap, self.prefix = cap, prefix + '/'

    def read(self, path):
        return self.cap.read(self.prefix + path)

    def text(self, path):
        return self.cap.text(self.prefix + path)

    def json(self, path):
        return self.cap.json(self.prefix + path)


def compiler_checks(cap, after):
    identity, text = cap.json('identity.json'), cap.text('checks.manifest')
    require(identity['source_fingerprint'] == after['source_fingerprint'] and
            identity['source_manifest_sha256'] == hashlib.sha256(after['source_manifest'].encode()).hexdigest() and
            identity['checks_manifest_sha256'] == hashlib.sha256(text.encode()).hexdigest(),
            'compiler check sources differ')
    blobs(cap, text, 'checks-sources/')
    rows = cap.json('native-status.json')
    require(len(rows) == 1 and rows[0]['name'] == 'clang-tuned' and
            rows[0]['exit_code'] == 0 and all(rows[0][k] == v for k, v in identity.items()) and
            rows[0]['sanitize'] == ['address', 'undefined'] and rows[0]['variants'] ==
            ['Native', 'AVX2', 'AVX2Remainder', 'Scalar', 'Remainder', 'ScalarRemainder'],
            'compiler native coverage differs')
    require('clang version 23.1.3' in cap.text('native-clang-tuned.log'), 'compiler version differs')


def insertion_kernels(cap):
    before, after = source(cap, 'insertion-before'), source(cap, 'insertion-after')
    digest = cap.json('insertion-digests/status.json')
    require(digest['exit_code'] == 0 and digest['source_commit'] == after['commit'] and
            digest['kind'] == 'insertions' and cap.text('insertion-digests/run.stderr') == '',
            'insertion digest checks differ')
    for suffix in ['', '-long']:
        status = cap.json('insertion-after/kernel' + suffix + '-status.json')
        require(status['manifest'] == {'A': before, 'B': after} and status['threads'] == 1 and
                status['binary_sha256'] == status['binary_sha256_after'] ==
                {a: m['binary_sha256']['bench'] for a, m in [('A', before), ('B', after)]},
                'insertion executable binding differs')
        rows = status['samples']
        matched = [r for r in rows if r['label'].startswith('matched/')]
        require([r['label'] for r in matched] == [
                f'matched/productInsertions/b{b}-{n}-{a}' for b in [0, 1] for n in [64, 256, 1024, 4096]
                for a in (['A', 'B'] if b == 0 else ['B', 'A'])], 'insertion AB/BA schedule differs')
        complexity = {}
        for row in rows:
            require(row['exit_code'] in [0, 2], 'insertion kernel failed')
            result = cap.json('insertion-after/kernels' + suffix + '/' + row['label'] + '/result.json')['results'][0]
            require(result['config']['max_seconds_per_call'] == 1 and
                    result['config']['target_inner_nanos'] < 1000000000 and all(
                    p['status'] == 'ok' and p['result_hash'] is not None
                    for p in result['points']), 'insertion cap or complete result differs')
            if row['label'].startswith('matched/'):
                require(len(result['points']) == 1 and result['points'][0]['below_signal_floor'],
                        'insertion signal flag differs')
                point = result['points'][0]
                require(int(point['result_hash'], 16) == digest['digests'][str(point['param'])],
                        'matched insertion digest differs')
            else:
                complexity[row['arm']] = [(p['trial_index'], p['param'], p['result_hash'])
                                          for p in result['points']]
        if not suffix:
            require(set(complexity) == {'A', 'B'} and complexity['A'] == complexity['B'],
                    'insertion complexity outputs differ')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    cap = Capsule(args.archive)
    before = source(cap, 'baseline')
    require(before['source_fingerprint'] == '294f219094cd', 'baseline differs')
    lines = ['# Unselected F4 optimizations and compiler profiles', '',
        'These independent experiments do not establish overall performance leadership. Their implementations '
        'and compiler profiles remain unselected. Every completed sample, outlier, failure, source snapshot '
        'and command is retained. Each full-system experiment has a first pass and its sole unchanged repeat; '
        'no further unchanged repeat is collected.', '',
        'The baseline is the four-row packed provider `294f219094cd`, using native Clang 21.1.8 and '
        'SDK Clang 23.1.0 for generated C. All comparisons use degree scheduling, grevlex, complete reduced '
        'bases, one leased CPU per sweep and one algorithm thread. Adjacent comparisons alternate AB/BA. '
        'F₂ enables binary pivots in both arms; the prime controls disable them at p = 32003 and 2147483647. '
        'Each experiment retains 192 completed processes and 96 equal paired complete bases and logical statistics. '
        'Candidate timings exclude certificate generation, independent native verification and kernel checking.', '']
    descriptions = {
        'overlay': ('Exact hash overlay for virtual insertion buckets',
            'A 128-slot exact-key overlay replaces linear searches among the at-most-64 virtual insertion '
            'buckets. Exact key comparisons resolve secondary collisions; a directed test exercises 39 such '
            'collisions. The existing atomic refusal and 4096-work contracts remain in force.'),
        'lazy': ('Lazy four-row XOR combinations',
            'Four-row groups construct only combinations selected by targets, caching dependencies in the '
            'existing private table. Logical charges, sugar labels, bounded admission and workspace sizes '
            'remain unchanged. Directed tests check actual construction and group-use counters.'),
        'clang23': ('Clang 23 with generic x86-64',
            'Only the native C compiler changes to Clang 23.1.3. The requested -march=native was stripped '
            'by the Nix wrapper: retained effective-target diagnostics identify x86-64. These results are '
            'therefore labelled generic, and do not measure native CPU tuning.'),
        'native-cpu': ('Clang 23 with znver5 tuning',
            'The native C wrapper explicitly disables Nix’s native-target stripping and uses Clang 23.1.3 '
            'with -march=native. The effective-target diagnostic identifies znver5. Generated C retains the '
            'SDK compiler. This compares a combined compiler/ISA profile with the generic baseline.')}
    for label, (title, description) in descriptions.items():
        view = View(cap, label)
        after = source(view, 'candidate')
        a, b = listing(before['source_manifest']), listing(after['source_manifest'])
        changed = {k for k in set(a) | set(b) if a.get(k) != b.get(k)}
        if label in ['overlay', 'lazy']:
            checks(view, after, True)
            require(set(a) == set(b) and changed == {'HexGroebner/ffi/' +
                    ('monomial_hit.c' if label == 'overlay' else 'matrix_eliminate.c')} and
                    before['compilers'] == after['compilers'] and
                    before['native_options'] == after['native_options'], 'implementation controls differ')
        else:
            compiler_checks(view, after)
            require(a == b and before['compilers']['lean'] == after['compilers']['lean'],
                    'compiler profile changed sources or generated-C compiler')
        lines += ['## ' + title, '', description, '',
            f'Runtime `{after["source_fingerprint"]}`. ' +
            ('All twelve Clang/GCC sanitized variants and all nine project checks passed.'
             if label in ['overlay', 'lazy'] else
             'All six Clang ASan/UBSan variants passed for this profile. The nine project checks were '
             'run for the unchanged source under the baseline configuration; no complete project audit '
             'under this alternative compiler profile is claimed.'), '',
            '| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max |',
            '|---|---:|---:|---:|---:|---|']
        for name, count, flag in [('f2-false', 10, 'true'), ('f2-false-repeat', 10, 'true'),
                                  ('prime-control', 14, None), ('prime-control-repeat', 14, None)]:
            r = sweep(view, 'candidate/' + name, before, after, count, {'A': flag, 'B': flag})
            v, m = r['recorded'], r['meta']
            lines.append(f'| {name} | {m["cpu"]} | {v["geomean"]:.6f} | '
                f'{v["family_balanced_geomean"]:.6f} | {r["candidate"]:.6f} | '
                f'{v["minimum"]:.6f} / {v["median"]:.6f} / {v["maximum"]:.6f} |')
        lines.append('')
    owners = cap.json('ownership/status.json')['observations']
    require(len(owners) == 10 and all(r['exit_code'] == 0 and r['complete_basis_and_stats_equal'] and
            all(int(v) == 0 for v in r['counters'][4:]) for r in owners), 'ownership diagnostic differs')
    insertion_kernels(cap)
    lines += ['## Diagnostic limits', '',
        'The insertion-overlay kernel’s first pass and sole longer-target repeat both remained clamped '
        'by the benchmark’s one-second per-call cap. All sixteen matched samples in each pass had '
        'signal flags. All records are retained; independently compiled checks validate the complete '
        'result hashes at every matched size. '
        'no kernel speed claim is made from those passes.', '',
        'A separate non-timed ownership probe observed all ten F₂ cases. Complete outputs and logical '
        'statistics matched the frozen provider. Accepted inserting calls forced no shared table, arena '
        'or workspace copies. This rules out that particular copy hypothesis on these inputs; it does '
        'not rule out allocation or copying elsewhere. Four adjacent AB/BA user-cycle profiles of the '
        'packed providers are retained as diagnostics, without timing or acceptance claims.', '',
        'The compiler experiments do not close the measured comparator gap or demonstrate that Lean '
        'language/runtime changes are necessary. The small suites do not meet the SPEC’s leadership '
        'acceptance requirements. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '',
        f'Raw capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`.', '', '```bash',
        'python3 scripts/bench/groebner_unselected_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-unselected.md --check', '```', '']
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified source/check/compiler bindings and all 384 paired complete bases/statistics.')


if __name__ == '__main__':
    main()
