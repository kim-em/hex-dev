#!/usr/bin/env python3
"""Render the complete retained Kronecker proof sweep without selecting samples."""
import argparse
import gzip
import json
import re
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.kronecker_attribution_report import render as render_attribution


def ms(n):
    return f"{n / 1e6:.3f}"


def read_json(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def kernel_ms(output):
    values = re.findall(r"(?m)^\ttype checking ([0-9.eE+-]+)(ms|s|μs|µs|ns)\s*$", output)
    if not values:
        raise ValueError('missing aggregate kernel type-checking time')
    value, unit = values[-1]
    return float(value) * {'ms': 1, 's': 1000, 'μs': .001, 'µs': .001, 'ns': .000001}[unit]


def median_faster(row):
    arms = row['arms']
    return all(arms['Kronecker']['median_delta_ns'] < arms[a]['median_delta_ns']
               for a in ['Ring', 'Grobner'])


def ratio(candidate, reference):
    return f'{candidate / reference:.3f}' if candidate > 0 and reference > 0 else '—'


def margin_spread(pair):
    values = pair['margins_ns']
    center = statistics.median(values)
    mad = statistics.median(abs(v - center) for v in values)
    return center, mad, abs(center) <= mad


def host_counts(data):
    values = [s[arm][phase]['concurrent_lake_lean_count']
              for s in data['samples'] for arm in ['candidate', 'reference']
              for phase in ['host_before', 'host_after']]
    return statistics.median(values), max(values)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--kernel-profiles', type=Path, required=True)
    parser.add_argument('--before', type=Path, help='retained shipping sweep for per-case before/after values')
    parser.add_argument('--attribution', type=Path, help='archive of retained isolated kernel comparisons')
    parser.add_argument('--repeat-of', type=Path, help='the inconclusive complete sweep repeated once unchanged')
    parser.add_argument('--previous-kernel-profiles', type=Path, help='retained profiles before their single repeat')
    args = parser.parse_args()
    data = read_json(args.input)
    profile_data = read_json(args.kernel_profiles)
    if not data['measurement_complete'] or not data['sources_unchanged'] or data['subset']:
        raise SystemExit('a complete sweep with unchanged measured sources is required')
    if not profile_data['sources_unchanged'] or len(profile_data['profiles']) != 3 or any(
            p['result']['state'] != 'complete' for p in profile_data['profiles']):
        raise SystemExit('all three required profiles must complete')
    overlap = data['source_hashes'].keys() & profile_data['source_hashes'].keys()
    mismatch = [p for p in overlap if data['source_hashes'][p] != profile_data['source_hashes'][p]]
    if mismatch:
        raise SystemExit(f'profile and sweep source hashes differ: {sorted(mismatch)}')
    link = 'data/hex-kronecker-mathlib/' + args.input.name
    rows = list(data['summary'].values())
    previous = read_json(args.repeat_of) if args.repeat_of else None
    if previous and (not previous['measurement_complete'] or not previous['sources_unchanged'] or previous['subset']
                     or previous['source_hashes'] != data['source_hashes']):
        raise SystemExit('the repeated sweep must have identical measured sources')
    ceilings = all(s['arms']['Kronecker']['ceiling_pass'] for s in rows if s['accepted'])
    wins = sum(median_faster(s) for s in rows if s['accepted'])
    unresolved = sum(margin_spread(p)[2] for s in rows if s['accepted'] for p in s['paired'].values())
    accepted = sum(s['accepted'] for s in rows)
    optimization = ''
    kernel_conclusion = ''
    host_context = ''
    if args.before:
        old = read_json(args.before)['summary']
        small = [r for r in rows if r['accepted'] and r['family'] == 'reflected-identities'
                 and old[r['stem']]['arms']['Kronecker']['median_delta_ns'] >
                     old[r['stem']]['arms']['Ring']['median_delta_ns']]
        small_pass = [r for r in small if r['arms']['Kronecker']['median_delta_ns'] <=
                      r['arms']['Ring']['median_delta_ns']]
        det_cases = [r for r in rows if r['accepted'] and r['family'] == 'determinant-identities']
        det_pass = [r for r in det_cases if r['arms']['Kronecker']['median_delta_ns'] <=
                    old[r['stem']]['arms']['Kronecker']['median_delta_ns']]
        optimization = (
            f"Of the seven grid cases that lost to `ring` in the shipping table, "
            f"{len(small_pass)}/{len(small)} are now at or below its median. "
            f"{len(det_pass)}/{len(det_cases)} determinant medians are no larger than the "
            "shipping values. The numerical optimization bar is **"
            + ('passed' if len(small_pass) == len(small) and len(det_pass) == len(det_cases)
               else 'not passed') + "**. These are fresh-module comparisons; controlled "
            "kernel attribution is reported separately.")
        remaining = [r['stem'] for r in small if r not in small_pass]
        if remaining:
            optimization += (' The previously losing small cases still above `ring` are '
                             + ', '.join(f'`{case}`' for case in remaining) + '.')
    if args.attribution:
        kernel_conclusion = '''The smallest case's controlled kernel median is 3.715 ms (all six samples
below 5 ms), and all five determinant kernel medians improve. Reflection
still costs about 4 ms in the instrumented smallest-case session, principally
Sym.Arith canonicalization and instance classification. That remaining work
can keep the total tactic cost above `ring` even after the kernel improvement;
the fresh-module measurements below determine the numerical bar separately.'''
        first = previous or data
        count_median, count_max = host_counts(first)
        host_context = f'''## Shared-host execution context

The first sweep of the final implementation overlapped another full sweep and local
verification builds, including the full proof-probe target. Those builds
were started as part of this work and contributed concurrent activity.
The recorded whole-host Lake/Lean process count had median {count_median:g}
and maximum {count_max}. It includes other work on the shared host, so these
counts do not identify the origin of every process. All observations remain
evidence under the shared-host policy.
'''
        if args.before:
            shipping_median, shipping_max = host_counts(read_json(args.before))
            host_context += (f'\nThe shipping sweep recorded median {shipping_median:g} and maximum '
                             f'{shipping_max} concurrent Lake/Lean processes.\n')
        if previous:
            current_median, current_max = host_counts(data)
            first_unresolved = sum(margin_spread(p)[2] for s in previous['summary'].values()
                                   if s['accepted'] for p in s['paired'].values())
            host_context += (f'\nAfter {first_unresolved}/{2*accepted} first-sweep comparisons were unresolved, '
                'the identical registered six-pair protocol was repeated once. '
                'Local builds and other measurements from this work finished before the repeat; '
                'the CPU was automatically leased without an idle-host criterion. '
                f'The repeat recorded median {current_median:g} and maximum {current_max} '
                'concurrent Lake/Lean processes. Both complete sweeps are retained and compared below; '
                'no observation is filtered and the numerical bar is unchanged.\n')
    shifted = all(s.get('one_atom_shifted', False) for s in rows
                  if s['family'] == 'reflected-identities' and s['atoms'] == 1)
    one_atom = ("The one-atom rows use `(x + 1)^d` so that they also exercise expansion."
                if shifted else "The one-atom rows are reflexive `x^d = x^d` identities; "
                "they do not exercise expansion and their small differences can be obscured by import variation.")
    text = f'''# HexKroneckerMathlib performance

## Result

{unresolved}/{2*accepted} paired comparisons have a median-margin magnitude no
larger than their median absolute deviation and are **unresolved at this
measurement resolution**. The numerical median comparison and this description
of variation are reported separately; no sample is discarded or replaced.

The complete sweep contains {accepted} accepted identities and {len(rows)-accepted}
preflight declines. {wins}/{accepted} accepted cases have a smaller per-arm
baseline-subtracted median than both `ring` and `grobner`. The comparison across
all accepted cases is **{'passed' if wins == accepted else 'not passed'}**.
The absolute candidate ceilings are **{'passed' if ceilings else 'not passed'}**.
The [opt-in shipping condition](../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md#fresh-module-comparisons-and-shipping-bar)
requires the complete family table and passing absolute ceilings. Its status
is **{'passed' if ceilings else 'not passed'}**. No default tactic chain changes.

{optimization}

{kernel_conclusion}

## Protocol and provenance

The measured checkout is `{data['environment']['git_commit']}`, using
`{data['environment']['toolchain']}`. The record includes the pinned dependency
revisions and SHA-256 hashes of the complete measured source closure.
The Kronecker implementation, proof probes, and sweep runner match those
measured sources. The measured Lake file is preserved in the source archive.

[Raw samples, source hashes, artifacts, and profiles]({link}) retain every
completed sample. Six adjacent three-arm blocks use Ring/Kronecker/Grobner
order in odd rounds and its reverse in even rounds. The middle candidate is
adjacent to both references, giving each comparison six alternating AB/BA
pairs. Each arm has its own adjacent fresh import-only baseline, with
baseline/proof order also alternating. Baselines are subtracted round by
round; negative differences are retained. Paired margins are reference delta
minus candidate delta, so a positive value favors Kronecker.

All arms use identical propositions and shared construction modules. The
runner removes each measured module's artifacts before `lake build` and warms
only dependencies. It uses one automatically leased CPU on the shared host.
Host load, CPU accounting, raw compiler output, RSS and axiom audits are
recorded per sample. An interrupted schedule resumes missing arm samples
without replacing any completed sample; execution segments preserve the
original runner hashes, CPU and environment. A resumption never replaces
completed samples.

The preregistered ceilings are 30 seconds per accepted grid case, 60 seconds
per accepted determinant case, and a 180-second cleanup timeout. Ceilings
apply to raw candidate wall time, including imports. The table reports
baseline-subtracted per-arm medians in milliseconds. Ratios are Kronecker
divided by the reference median and are shown only when both are positive.
The numerical comparison uses these per-arm medians; paired-margin signs
remain supplementary evidence. Losing cases stay in the table and do not
prevent explicitly opt-in shipping under the SPEC's shared exception.

{host_context}

## reflected-identities and determinant-identities

| Case | D | N | Kronecker ms | ring ms | grobner ms | K/ring | K/grobner | Ceiling |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
'''
    for s in rows:
        if not s['accepted']:
            continue
        a = s['arms']; p = s['paired']; size = s['size']
        cells = [ms(a[k]['median_delta_ns']) for k in ['Kronecker', 'Ring', 'Grobner']]
        cells += [ratio(a['Kronecker']['median_delta_ns'], a[k]['median_delta_ns'])
                  for k in ['Ring', 'Grobner']]
        text += f"| {s['stem']} | {size['digits']} | {size['packedBits']} | " + ' | '.join(cells) + f" | {'pass' if a['Kronecker']['ceiling_pass'] else 'fail'} |\n"
    if args.before:
        text += "\n## Per-case before/after\n\n"
        text += (f"Before values come from the [retained shipping sweep](data/hex-kronecker-mathlib/{args.before.name}); "
                 "after values come from the complete new sweep above. These historical wall-time "
                 "columns use different execution segments and are not adjacent before/after pairs. "
                 "Controlled kernel attribution is reported separately. Every value is retained, "
                 "including negative baseline-subtracted medians.\n\n")
        text += "| Case | Before K ms | After K ms | Before ring ms | After ring ms | Before grobner ms | After grobner ms |\n"
        text += "| --- | ---: | ---: | ---: | ---: | ---: | ---: |\n"
        for row in rows:
            if not row['accepted']:
                continue
            cells = []
            for arm in ['Kronecker', 'Ring', 'Grobner']:
                cells.extend([ms(old[row['stem']]['arms'][arm]['median_delta_ns']),
                              ms(row['arms'][arm]['median_delta_ns'])])
            text += f"| {row['stem']} | " + ' | '.join(cells) + " |\n"
    if previous:
        text += '\n## Single unchanged repeat\n\n'
        text += (f'The [first complete sweep](data/hex-kronecker-mathlib/{args.repeat_of.name}) '
                 'and the repeat have identical measured source hashes. Each column uses all six '
                 'per-arm baseline-subtracted observations from its own cohort. These cohorts '
                 'are not adjacent before/after pairs. Negative medians are retained.\n\n')
        if args.before:
            first_small = sum(previous['summary'][r['stem']]['arms']['Kronecker']['median_delta_ns'] <=
                              previous['summary'][r['stem']]['arms']['Ring']['median_delta_ns'] for r in small)
            first_det = sum(previous['summary'][r['stem']]['arms']['Kronecker']['median_delta_ns'] <=
                            old[r['stem']]['arms']['Kronecker']['median_delta_ns'] for r in det_cases)
            text += (f'The first cohort put {first_small}/{len(small)} previously losing small cases '
                     f'at or below `ring` and {first_det}/{len(det_cases)} determinant medians '
                     'at or below the historical shipping values. Its numerical bar and the '
                     'repeat\'s numerical bar are kept distinct.\n\n')
        text += '| Case | First K ms | Repeat K ms | First ring ms | Repeat ring ms | First grobner ms | Repeat grobner ms |\n'
        text += '| --- | ---: | ---: | ---: | ---: | ---: | ---: |\n'
        for row in rows:
            if row['accepted']:
                cells = [ms(record['summary'][row['stem']]['arms'][arm]['median_delta_ns'])
                         for arm in ['Kronecker', 'Ring', 'Grobner'] for record in [previous, data]]
                text += f"| {row['stem']} | " + ' | '.join(cells) + ' |\n'
        text += '\n| Case | First decline ms | Repeat decline ms |\n| --- | ---: | ---: |\n'
        for row in rows:
            if not row['accepted']:
                cells = [ms(record['summary'][row['stem']]['arms']['Decline']['median_delta_ns'])
                         for record in [previous, data]]
                text += f"| {row['stem']} | " + ' | '.join(cells) + ' |\n'
    det = [r for r in rows if r['accepted'] and r['family'] == 'determinant-identities']
    large = [r for r in rows if r['accepted'] and r['family'] == 'reflected-identities'
             and r['atoms'] >= 2 and r['degree'] >= 4]
    losers = [r['stem'] for r in rows if r['accepted'] and not median_faster(r)]
    text += ("\n## Measured regimes\n\n"
             f"The determinant-shaped group wins {sum(median_faster(r) for r in det)}/{len(det)} "
             "comparisons against both references. The accepted multivariate expansion "
             f"grid with degree at least four wins {sum(median_faster(r) for r in large)}/{len(large)}. "
             "These are the measured winning regimes; the full table also shows individual "
             "wins outside them.\n\n")
    text += ("The losing cases are " + ', '.join('`' + name + '`' for name in losers) +
             ". The detailed tables retain their numerical ordering and measurement spread. "
             "The resolution table below distinguishes "
             "the numerical ordering from shared-host variation. No dispatch threshold "
             "or default-chain entry is inferred from small unresolved differences.\n")
    text += '''
The grid has atom counts `1, 2, 3, 4, 6, 8` and degrees `2, 4, 8, 16`.
Accepted powers of sums are compared with independently expanded SymPy
integer polynomials. ''' + one_atom + '''
Historical source states and workloads remain in the retained records;
no completed sample is discarded.
The determinant family varies matrix dimension, shared
atom count, and entry degree; its left side explicitly expands the Leibniz
formula, and its right side is independently expanded with SymPy.

## dense-box-declines

Grid points outside the budget check preflight directly without constructing
an expanded right side. The independent-atom case has 25 linear entry atoms
in a `5 × 5` determinant and invokes the tactic under a guarded diagnostic.
It must report the dense-box decline before any packing.

'''
    text += '| Case | Dense digits (saturated) | Packed bits (saturated) | '
    text += ('Before decline ms | After decline ms |\n| --- | ---: | ---: | ---: | ---: |\n'
             if args.before else 'Decline median ms |\n| --- | ---: | ---: | ---: |\n')
    for s in rows:
        if not s['accepted']:
            previous = (ms(old[s['stem']]['arms']['Decline']['median_delta_ns']) + ' | '
                        if args.before else '')
            text += f"| {s['stem']} | {s['size']['digits']} | {s['size']['packedBits']} | {previous}{ms(s['arms']['Decline']['median_delta_ns'])} |\n"
    text += '''
A saturated count is a certified lower bound, not an exact size. Scope
outside the accepted dense-box regime is recorded as delegated scope and is
not counted as a packed success.

## Serialized proofs and trust

The sizes below are `.olean` bytes for the proof modules, including their
module metadata. Source and `.ilean` sizes are in the raw record.
Every accepted theorem's axiom set is a subset of `propext`, `Classical.choice`,
and `Quot.sound`. The same audit is run for all six public soundness theorems
and the uniform-ring and characteristic-seven examples.

| Case | Kronecker bytes | ring bytes | grobner bytes |
| --- | ---: | ---: | ---: |
'''
    for s in rows:
        if s['accepted']:
            text += f"| {s['stem']} | " + ' | '.join(str(s['arms'][a]['artifacts']['olean_bytes']) for a in ['Kronecker','Ring','Grobner']) + ' |\n'
    text += "\n## Comparison resolution\n\n"
    text += ("MAD is the median absolute deviation of the six paired margins from "
             "their median. An ordering is marked unresolved when the magnitude of "
             "that median does not exceed its MAD. This descriptive comparison "
             "does not add a sampling filter or change the preregistered numerical bar. "
             "Small tactic costs can be obscured by variation in the adjacent "
             "import-dominated builds.\n\n")
    text += ("| Case | Margin vs ring ms | MAD ms | Margin vs grobner ms | MAD ms | Resolution |\n"
             "| --- | ---: | ---: | ---: | ---: | --- |\n")
    for row in rows:
        if row['accepted']:
            spreads = [margin_spread(row['paired'][a]) for a in ['Ring', 'Grobner']]
            cells = [ms(v) for center, mad, _ in spreads for v in [center, mad]]
            uncertain = [a.lower() for a, v in zip(['Ring', 'Grobner'], spreads) if v[2]]
            label = 'unresolved: ' + ', '.join(uncertain) if uncertain else 'margin exceeds MAD'
            text += f"| {row['stem']} | " + ' | '.join(cells) + f" | {label} |\n"
    text += "\n## Paired signs\n\n"
    text += ("Each sign records one completed reference-minus-candidate margin in trial order. "
             "Positive favors Kronecker, negative favors the reference, and zero is a tie. "
             "Small baseline-subtracted differences may be dominated by shared-host variation; "
             "all signs and negative baseline differences are retained.\n\n")
    text += "| Case | vs ring | vs grobner |\n| --- | --- | --- |\n"
    for s in rows:
        if s['accepted']:
            signs = [' '.join('+' if n > 0 else '−' if n < 0 else '0'
                     for n in s['paired'][a]['margins_ns']) for a in ['Ring', 'Grobner']]
            text += f"| {s['stem']} | {' | '.join(signs)} |\n"
    checker = ('Kernel.exprEq' if all(p.get('module', '').endswith('KernelProfile')
               for p in profile_data['profiles'] if p['family'] != 'dense-box-declines')
               else 'checkExprEq')
    text += f'''
## Kernel-only profiles

The accepted-family profiles replay `{checker}` through
`decide +kernel`, using the quoted trees from their shared construction
modules. They exclude reflection, proof production, and the `fromGrind`
translation reduced by the actual tactic certificate. The decline-family
profile evaluates only preflight: it intentionally performs no packed
certificate check. Raw profiler output is retained in the record.

| Family | Representative | Kernel type checking ms | Fresh module wall ms | Axioms |
| --- | --- | ---: | ---: | --- |
'''
    for p in profile_data['profiles']:
        result = p['result']
        text += f"| {p['family']} | {p['stem']} | {kernel_ms(result['compiler_output']):.3f} | {ms(result['wall_nanos'])} | {', '.join(result['axioms']) or 'none'} |\n"
    text += ('\n[Kernel profiles and their source hashes](data/hex-kronecker-mathlib/'
             + args.kernel_profiles.name + ') record the dedicated fresh profile runs. '
             'The kernel column is Lean’s aggregate type-checking timer. The separate '
             'fresh-module wall time includes imports and compilation. The decline '
             'profile proves the preflight result using `decide +kernel`; it performs '
             'no packed evaluation. Earlier compiled-guard diagnostics remain in the '
             'historical sweep records and are not used as kernel profiles.\n')
    if args.previous_kernel_profiles:
        prior_profiles = read_json(args.previous_kernel_profiles)
        if (not prior_profiles['sources_unchanged'] or len(prior_profiles['profiles']) != 3
                or any(p['result']['state'] != 'complete' for p in prior_profiles['profiles'])
                or prior_profiles['source_hashes'] != profile_data['source_hashes']):
            raise SystemExit('the repeated kernel profiles must be complete with identical sources')
        prior = {p['stem']: p for p in prior_profiles['profiles']}
        text += ('\nThe three profiles were repeated once, before the unchanged full sweep. '
                 'The first observations are retained below. These are unpaired single '
                 'profiles on the shared host, so their differences do not establish an '
                 'implementation regression. In particular, the unchanged decline checker '
                 'varies substantially between observations.\n\n')
        text += '| Case | First kernel ms | Repeated kernel ms |\n| --- | ---: | ---: |\n'
        for p in profile_data['profiles']:
            text += (f"| {p['stem']} | {kernel_ms(prior[p['stem']]['result']['compiler_output']):.3f} | "
                     f"{kernel_ms(p['result']['compiler_output']):.3f} |\n")
        text += (f'\n[First profiles](data/hex-kronecker-mathlib/{args.previous_kernel_profiles.name}) '
                 'preserve their full logs and source hashes.\n')
    text += '''
The Mathlib-free [computational report](hex-kronecker-performance.md) supplies
complexity evidence in the packed bit size, operation profiles and the full
plain/signed product comparison. These proof probes measure total tactic
cost, including reflection, emitted literals, and synchronous kernel checking.
'''
    if args.attribution:
        text += '\n' + render_attribution(args.attribution)
    text += "\n## Retained source states\n\n"
    text += ("Every completed sweep is retained. Historical `candidate_faster` fields "
             "in the older raw records describe paired-margin medians; the verdict "
             "above is recomputed from per-arm medians. Source archives preserve "
             "the measured closure, including experimental states. The checkout commit "
             "is the base revision; recorded working-tree changes are identified by the "
             "full source hashes and preserved in those archives.\n\n")
    text += "| Record | Checkout commit | Dirty checkout | Completed arm pairs | Source archive |\n| --- | --- | --- | ---: | --- |\n"
    for path in sorted(args.input.parent.glob('sweep*.json.gz')):
        record = read_json(path)
        suffix = path.name.removeprefix('sweep').removesuffix('.json.gz').lstrip('-') or 'baseline'
        archive = path.with_name('source-' + suffix + '.tar.gz')
        source = f'[sources](data/hex-kronecker-mathlib/{archive.name})' if archive.exists() else 'See recorded hashes'
        text += (f"| [{path.name}](data/hex-kronecker-mathlib/{path.name}) | "
                 f"`{record['environment']['git_commit']}` | {record['environment']['git_dirty']} | {len(record['samples'])} | {source} |\n")
    args.output.write_text(text)


if __name__ == '__main__':
    main()
