#!/usr/bin/env python3
"""Render the complete retained Kronecker proof sweep without selecting samples."""
import argparse
import gzip
import json
import re
from pathlib import Path


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--kernel-profiles', type=Path, required=True)
    args = parser.parse_args()
    data = read_json(args.input)
    profile_data = read_json(args.kernel_profiles)
    if not data['measurement_complete'] or not data['sources_unchanged'] or data['subset']:
        raise SystemExit('a complete sweep with unchanged measured sources is required')
    if not profile_data['sources_unchanged'] or len(profile_data['profiles']) != 3 or any(
            p['result']['state'] != 'complete' for p in profile_data['profiles']):
        raise SystemExit('all three required profiles must complete')
    link = 'data/hex-kronecker-mathlib/' + args.input.name
    rows = list(data['summary'].values())
    ceilings = all(s['arms']['Kronecker']['ceiling_pass'] for s in rows if s['accepted'])
    wins = sum(all(p['candidate_faster'] for p in s['paired'].values()) for s in rows if s['accepted'])
    accepted = sum(s['accepted'] for s in rows)
    text = f'''# HexKroneckerMathlib performance

## Result

The complete sweep contains {accepted} accepted identities and {len(rows)-accepted}
preflight declines. {wins}/{accepted} accepted cases have a positive paired
median margin against both `ring` and `grobner`. The per-case runtime bar is
**{'passed' if wins == accepted else 'not passed'}**. The absolute candidate ceilings are
**{'passed' if ceilings else 'not passed'}**. No default tactic chain changes.

## Protocol and provenance

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
original runner hashes, CPU and environment. This is not an unchanged rerun.

The preregistered ceilings are 30 seconds per accepted grid case, 60 seconds
per accepted determinant case, and a 180-second cleanup timeout. Ceilings
apply to raw candidate wall time, including imports. The table reports
baseline-subtracted medians in milliseconds, and paired median margins.

## reflected-identities and determinant-identities

| Case | D | N | Kronecker ms | ring ms | grobner ms | Margin vs ring ms | Margin vs grobner ms | Ceiling |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
'''
    for s in rows:
        if not s['accepted']:
            continue
        a = s['arms']; p = s['paired']; size = s['size']
        cells = [ms(a[k]['median_delta_ns']) for k in ['Kronecker', 'Ring', 'Grobner']]
        cells += [ms(p[k]['median_margin_ns']) for k in ['Ring', 'Grobner']]
        text += f"| {s['stem']} | {size['digits']} | {size['packedBits']} | " + ' | '.join(cells) + f" | {'pass' if a['Kronecker']['ceiling_pass'] else 'fail'} |\n"
    text += '''
The grid has atom counts `1, 2, 3, 4, 6, 8` and degrees `2, 4, 8, 16`.
Accepted powers of sums are compared with independently expanded SymPy
integer polynomials. The determinant family varies matrix dimension, shared
atom count, and entry degree; its left side explicitly expands the Leibniz
formula, and its right side is independently expanded with SymPy.

## dense-box-declines

Grid points outside the budget check preflight directly without constructing
an expanded right side. The independent-atom case has 25 linear entry atoms
in a `5 × 5` determinant and invokes the tactic under a guarded diagnostic.
It must report the dense-box decline before any packing.

| Case | Dense digits (saturated) | Packed bits (saturated) | Decline median ms |
| --- | ---: | ---: | ---: |
'''
    for s in rows:
        if not s['accepted']:
            text += f"| {s['stem']} | {s['size']['digits']} | {s['size']['packedBits']} | {ms(s['arms']['Decline']['median_delta_ns'])} |\n"
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
    text += '''
## Kernel-only profiles

The accepted-family profiles replay `checkExprEq = true` through
`decide +kernel`, using the quoted trees from their shared construction
modules. They exclude reflection and proof production. The decline-family
profile evaluates only preflight: it intentionally performs no packed
certificate check. Raw profiler output is retained in the record.

| Family | Representative | Kernel type checking ms | Fresh module wall ms | Axioms |
| --- | --- | ---: | ---: | --- |
'''
    for p in profile_data['profiles']:
        result = p['result']
        text += f"| {p['family']} | {p['stem']} | {kernel_ms(result['compiler_output']):.3f} | {ms(result['wall_nanos'])} | {', '.join(result['axioms'])} |\n"
    text += ('\n[Kernel profiles and their source hashes](data/hex-kronecker-mathlib/'
             + args.kernel_profiles.name + ') record the dedicated fresh profile runs. '
             'The kernel column is Lean’s aggregate type-checking timer. The separate '
             'fresh-module wall time includes imports and compilation. The decline '
             'profile proves the preflight result using `decide +kernel`; it performs '
             'no packed evaluation. Earlier compiled-guard diagnostics remain in the '
             'historical sweep records and are not used as kernel profiles.\n')
    text += '''
The Mathlib-free [computational report](hex-kronecker-performance.md) supplies
complexity evidence in the packed bit size, operation profiles and the full
plain/signed product comparison. These proof probes measure total tactic
cost, including reflection, emitted literals, and synchronous kernel checking.
'''
    args.output.write_text(text)


if __name__ == '__main__':
    main()
