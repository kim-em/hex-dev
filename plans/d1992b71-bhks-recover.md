## Current state

The BHKS van Hoeij CLD recovery pipeline in `HexBerlekampZassenhaus/Basic.lean`
now has all of its individual stages:

- `bhksLatticeBasis` (CLD lattice basis builder, #2603/#2609);
- `bhksProjectedRows` (LLL + Gram-Schmidt cut + projection to first `r`
  indicator coordinates, #2608/#2611);
- `bhksIndicatorCandidate?` (indicator vector → centred-residue lift →
  exact-division verification, #2612/#2615);
- equivalence-class indicator extraction from projected rows via RREF
  (#2614, in flight).

What is still missing is a single executable glue function that runs the
full recovery procedure end-to-end and returns `Option (Array ZPoly)`,
plus the wiring that lets `factorFastCoreWithBound` actually return `some`
when recovery succeeds. Today `factorFastCoreWithBound` is a precision
loop that always returns `none` even after the helpers are in place.

This issue covers only the executable glue function. The
`factorFastCoreWithBound` wiring is intentionally a separate later issue
because it changes public `factorFast` behavior and pairs with conformance
review.

depends-on: #2614

## Deliverables

1. In `HexBerlekampZassenhaus/Basic.lean`, add an executable
   `bhksRecover? : (f : ZPoly) (d : LiftData) → Option (Array ZPoly)` that
   wires the existing pipeline together for a fixed Hensel precision:
   build `bhksLatticeBasis` from `d.liftedFactors`, run
   `bhksProjectedRows`, run the equivalence-class extractor from #2614,
   call `bhksIndicatorCandidate?` for each indicator, and accept the run
   only when every candidate verifies and the accepted-factor product
   equals `f`.
2. Return `none` for any of: empty/degenerate projected-row output,
   trivial single equivalence class covering all factors, missing or
   non-`{0,1}` indicator vectors, an indicator whose candidate fails
   exact division, or a successful set of candidates whose product does
   not reproduce `f` (up to the existing centred-lift and content
   handling already used by `bhksIndicatorCandidate?`).
3. Add `#guard` examples covering at least: a small fixture where
   `bhksRecover?` returns `some` matching the slow-path factorisation
   (e.g. reuse a small fixture already used by `cldGuardF`/the existing
   indicator guards), a degenerate fixture where projected rows give no
   nontrivial classes and the helper returns `none`, and a fixture where
   the indicator is well-formed but exact division fails (force `none`).

## Library placement

- File path: `HexBerlekampZassenhaus/Basic.lean`.
- SPEC section: `SPEC/Libraries/hex-berlekamp-zassenhaus.md` "Recovery
  procedure (BHKS Step 7 + Lemma 3.3)" pins the LLL → cut → projection →
  RREF + equivalence-class identification → reconstruction-and-verification
  pipeline. SPEC pitfalls 2 and 5 require explicit verification before
  accepting candidates and `lc(f) · ∏ g_i^{w_i}` reconstruction with
  content removal — both already handled inside
  `bhksIndicatorCandidate?`.
- Q1: executable support for HO-1's fast recovery stage.
- Q2: no Mathlib bridge proof in this issue; this is executable plumbing.
- Q3: this is Hex-specific BZ recombination glue, not an upstream theorem.
- Q4: depends on #2614 for the equivalence-class indicator extractor; all
  other helpers are already in `Basic.lean`.

## Context

Read #2564 (HO-1 directive), #2612 (indicator candidate verifier), #2608
and #2614 (projected rows / equivalence-class extractor),
`SPEC/Libraries/hex-berlekamp-zassenhaus.md`, and the existing
`bhksIndicatorCandidate?`, `bhksProjectedRows`, `bhksLatticeBasis`, and
`factorFastCoreWithBound` definitions in `HexBerlekampZassenhaus/Basic.lean`.

Keep public `factor`, `factorFast`, `factorSlow`, and `factorWithBound`
behavior unchanged in this issue; the new helper must not be called from
`factorFastCoreWithBound` yet — that is a separate later issue (so any
existing conformance/cross-check that depends on `factorFast` returning
`none` for the BHKS path stays green).

## Verification

- `lake build HexBerlekampZassenhaus`
- `lake build HexBerlekampZassenhausMathlib`
- `python3 scripts/check_dag.py`
- `git diff --check`
- `rg -n '^axiom\b|native_decide|TODO|FIXME' HexBerlekampZassenhaus/Basic.lean`

## Out of scope

- Wiring `factorFastCoreWithBound` (or any other public `factorFast`
  surface) to return `some` from this helper.
- Adding the precision-doubling loop bookkeeping (mode-(a) versus mode-(b)
  failure distinction) — this issue is fixed-precision recovery only.
- Adding HO-2 adversarial fixtures, HO-3 benchmarks, or HO-4 termination
  proofs.
- Closing, relabeling, or rewriting any human-oversight issue.
- Group A/B/C bridge proof obligations.
