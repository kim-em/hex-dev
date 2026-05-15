## Current state

Two PRs landed on 2026-05-15 extending the public `Hex.Factorization`
API on `HexBerlekampZassenhaus/Basic.lean` for directive #2637, neither
of which has a review issue:

- PR #4276 (`feat: prove factorization packing invariants`, closed
  #4275, +200 lines).
- PR #4281 (`Expose public factorization multiplicity wrappers`,
  closed #4278, +84 lines).

Both modify the same `HexBerlekampZassenhaus/Basic.lean` public-API
surface that downstream `Factorization`-capstone issues (#3970,
#3969, #3987, #4008, etc.) will consume, so cross-PR consistency
matters. The directive #2637 strengthens `factor`'s contract to
return a `Factorization` record with explicit `(polynomial,
multiplicity)` pairs; these PRs land the first batch of public
wrappers exposing multiplicity-positive and pairwise-distinct-key
facts derived from the existing `factorizationOfFactors` collector
proofs.

## Deliverables

1. Review PR #4276 and PR #4281 together as one cohesive public
   `Factorization` API surface. Verify:
   - The added wrappers (`factorWithBound_entry_multiplicity_pos`,
     `factorWithBound_pairwise_first`, `factor_entry_multiplicity_pos`,
     `factor_pairwise_first`, plus the packing invariants from
     #4276) state facts in the public-API shape downstream
     capstones can consume without unfolding fast/slow internals.
   - Wrapper names match the existing `factorizationOfFactors`
     convention and the SPEC's `Factorization` field vocabulary.
   - Statements are minimal (no overgeneralisation) and reuse the
     existing collector-level proofs rather than duplicating
     casework.
2. Confirm both PRs preserve the Mathlib-free boundary of
   `HexBerlekampZassenhaus/Basic.lean` (no new Mathlib imports,
   no executable factorisation behavior change).
3. Leave a GitHub review on each PR — approve if correct, or
   record concrete findings as comments. If the public surface
   would benefit from a follow-up consolidation issue (e.g. a
   missing wrapper that downstream capstones still need), open
   a separate issue and link it; do not push changes to either
   PR's branch.

## Library placement

Paths under review: `HexBerlekampZassenhaus/Basic.lean`.

SPEC: `SPEC/Libraries/hex-berlekamp-zassenhaus.md` defines the
`Factorization` record and its public contract. Wrapper theorems
about packing invariants and per-entry multiplicity/pairwise-key
shape belong in `HexBerlekampZassenhaus/Basic.lean`'s
Mathlib-free side; their Mathlib-side consumers live in
`HexBerlekampZassenhausMathlib/Basic.lean`.

Placement checks:

- Does this belong to the library named by the SPEC? Yes — the
  public `Factorization` API is `HexBerlekampZassenhaus`'s
  responsibility per directive #2637.
- Does it import a bridge layer into a Mathlib-free library?
  Should not; verify no new `import Mathlib...` or
  `HexBerlekampZassenhausMathlib...` lines.
- Does it change executable behavior? Should not — both PRs
  describe themselves as proof-only wrappers over existing
  collector proofs.
- Does it modify immutable SPEC or roadmap files? Should not.

## Context

Read:

- PR #4276 and its closed issue #4275 (packing invariants).
- PR #4281 and its closed issue #4278 (multiplicity wrappers).
- Directive #2637 (umbrella `Factorization` API).
- `SPEC/Libraries/hex-berlekamp-zassenhaus.md`'s
  `Factorization` record section.
- `HexBerlekampZassenhaus/Basic.lean` around
  `factorizationOfFactors`, the new wrapper names listed in
  Deliverable 1, and the
  `factorWithBound` / `factor` public entry points.
- Downstream blocked capstones #3970, #3969, #3987, #4008 —
  spot-check that their stated obligations can use the new
  wrappers without further plumbing.

## Verification

- Inspect both PR diffs for spec alignment and downstream
  usability.
- `lake build HexBerlekampZassenhaus.Basic` and
  `lake build HexBerlekampZassenhaus` from the merged tip both
  succeed (re-verify locally if needed).
- `python3 scripts/check_dag.py` passes from the merged tip.
- No new `axiom`, `native_decide`, `TODO`, `FIXME`, or
  theorem-level `sorry` in the merged diffs.
- GitHub reviews posted on both PRs.

## Out of scope

- Implementing additional `Factorization` API wrappers
  (separate follow-up issue if Deliverable 3 surfaces a gap).
- Discharging downstream capstone obligations (#3970, #3969,
  #3987, #4008).
- Editing `SPEC/`, top-level `PLAN.md`, or top-level
  `AGENTS.md`.
- Re-reviewing PRs that already have closed review issues
  (#4280 → #4283; #4279 → #4284).
