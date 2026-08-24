# Phase 3/4 exit criteria for correspondence-only mathlib layers

## Accomplished

Defined a **correspondence-only mathlib layer** as a `mathlib: true`
library advertising zero operations in either Phase-4 evidence track,
and gave it written exit criteria.

- `PLAN/Phase3.md`, new `### Correspondence-only mathlib layers`: no
  `conformance/HexFooMathlib/Conformance.lean` and no `HexConformance`
  glob naming it; the PR audits whatever checks the layer carried and
  cites the coverage living in the named computational owners, with
  bridge-only conversion and index-helper checks deleted rather than
  migrated; `lake build HexFooMathlib` green; `done_through` bumped in
  the same PR.
- `PLAN/Phase4.md`, new `### Correspondence-only mathlib layers`: no
  bench targets (`SPEC/benchmarking.md §Mathlib-free benches`), an
  external-comparator absence declared with the new
  `correspondence-only-layer` reason naming the computational owners,
  no `phase4` block, and no required headline report. The deliverables,
  the compiled-track criteria, and the empty-Concerns criterion do not
  apply. The exemption is narrow: compiled-only, proof-only, and mixed
  libraries all take ordinary track assignment, and a declared
  `proof_probes` root normally puts a library outside the exemption.
- `SPEC/benchmarking.md`: added `correspondence-only-layer` as a sixth
  comparator-absence reason, since the other five are scoped to a bench
  target and this class has none; widened the absence-declaration
  lead-in to cover a library with no bench target at all; exempted such
  a layer from the headline-report requirement.
- `SPEC/testing.md`: corrected the two places that still promised these
  layers a `core` conformance profile, both now distinguishing a
  correspondence-only layer from a Mathlib-importing library that owns
  a runtime.

## Current frontier

The policy now matches what `scripts/conformance_targets.py` enforces
and what HexHenselMathlib, HexGFqMathlib, and HexModArithMathlib
actually did on their way to `done_through: 7`. No script or Lean
change was needed.

## Next step

`HexPolyFpMathlib` can record Phase 3 and Phase 4 against these
criteria. Its SPEC spells the comparator-absence reason
`proof-only-layer`, as do `HexGF2Mathlib`'s and `HexGFqMathlib`'s; all
three move to `correspondence-only-layer` and gain their owner names
(`hex-gf2` and `hex-gfq-field` for HexGF2Mathlib). Separately,
`scripts/check_phase4.py` exempts every `mathlib: true` library with no
`phase4` block and no report, without checking correspondence-only
status; a follow-up issue proposes an explicit classification the
validators can key off.

## Blockers

None.
