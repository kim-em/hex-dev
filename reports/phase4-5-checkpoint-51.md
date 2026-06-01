# Phase 4/5/6 checkpoint 51

Scope: checkpoint for merged work after summarize issue #5927, covering the
current HexPolyZMathlib, HexMatrixMathlib, HexLLL, HexModArith/HexGF2, and BZ
frontiers.

## Landed work

### HexPolyZMathlib Schur and Schmeisser

The Schmeisser route continued narrowing around exact-degree-two Schur kernels.

- #5963 proved the boundary Schur norm-square inequality.
- #5984 proved the closed disk Schur bound.
- #6009 added the structured two-pair exterior obstruction used by the
  degree-two interior cases.

Open PR #6019 now assembles the two-interior degree-two Schur kernel from the
ratio lemmas. If it lands, the next useful work is the blocked chain through
#5947, #5948, #5945, #5940, and then #5924. The downstream derivative and
Mahler comparison issues should remain blocked behind that exact-degree-two
route.

### HexMatrixMathlib determinant and Plucker bridges

The determinant bridge layer moved away from the stale Mathlib-free `nDet`
route and toward reusable bridge-layer Desnanot infrastructure.

- #5956 added determinant multiplication substrate as partial progress on the
  replacement determinant chain.
- #5985 added right-adjugate determinant substrate.
- #6007 exposed the cofactor Desnanot bridge in `HexMatrixMathlib`.

The old Mathlib-free Plucker assembly issue #5848 is stale: #5912 was closed
for replan, and the live final assembly now belongs to the bridge-layer chain
#5998 -> #5999 -> #6006 -> #6012 -> #6015 -> #6021. Until that chain lands,
the Gram-Schmidt consumer issues #5805 and #5655 should stay blocked.

### HexLLL and Gram-Schmidt performance

The LLL benchmark front shifted from evidence gathering to a targeted
implementation-performance fix.

- #5969 refreshed the densified Lean/Isabelle comparator evidence.
- #6000 diagnosed the harsh-cubic crossover as exact-integer Gram-Schmidt
  construction cost, not fixture generation or benchmark-registration shape.

Open PR #6017 preserves Bareiss prefix rows for #5994. If it lands and improves
the harsh-cubic path, #6016 is the next continuation issue for exact-integer
operand reduction and comparator reruns.

### HexModArith, HexGF2, and Phase 6 API polish

Phase 6 polish landed across the mature Mathlib-free arithmetic layers.

- #5951 added the current convention that rendered human-facing artifacts must
  be visually inspected, not only regenerated or data-checked.
- #5972 reviewed the HexArith extended-GCD API.
- #5990 reviewed the ZMod64 API and identified narrow automation/extensionality
  follow-ups.
- #6001 reviewed the HexGF2 packed-polynomial API.
- #6002 added `MontResidue` Nat-representative extensionality.
- #6003 narrowed the inverse simp surface for `ZMod64`.
- #6008 added conservative HexGF2 packed-operation automation annotations.
- #6010 hid internal HexGF2 quotient-field helper surface while keeping the
  public field facts intact.

Open PR #6004 adds the remaining ZMod64 neutral-law simp coverage and includes
repair commits for downstream HexPolyFp fallout. New unclaimed reviews #6022
and #6023 are the next broad Phase 6 audit slices for HexPolyFp and
HexGFqField.

### BZ witness and fallback cleanup

The Berlekamp-Zassenhaus work continued replacing silent fallback behavior with
explicit witnesses.

- #5957 packaged the small-mod singleton branch substrate.
- #5962 packaged the slow-path Hensel substrate for factor irreducibility.
- #5986 made `choosePrimeData` fallback behavior explicit.

Open PR #6018 gates the BZ fast path on available prime data. The follow-up
#5980 remains blocked until #5979 lands, and the older HO directive issues
remain dependency-blocked rather than ready for direct implementation.

### HexPoly Phase 6 composition surface

The core polynomial API review and follow-ups improved the composition and
automation surface used by downstream finite-field polynomial code.

- #5973 reviewed the operation API.
- #5977 added conservative operation `grind` annotations.
- #5981 partially promoted compose scaffolding.
- #5993 promoted the compose power-sum skeleton after repair of downstream
  `HexPolyFp` integration.

This leaves the more specialized HexPolyFp API review in #6022 as the next
place to check whether the downstream finite-field polynomial layer can now
delete or hide any duplicate composition scaffolding.

## Current frontier

Open PRs:

- #6019, `HexPolyZMathlib: assemble two-interior degree-two Schur kernel from
  ratio lemmas`.
- #6018, `fix: gate BZ fast path on prime data`.
- #6017, `perf: preserve Bareiss prefix rows`.
- #6004, `feat: add ZMod64 neutral simp coverage`.
- #2656, draft SPEC PR for real roots and Sturm.

Ready unclaimed work:

- #6022, HexPolyFp Phase 6 API review.
- #6023, HexGFqField Phase 6 API review.

Blocked fronts:

- BZ headline directives #2564, #2567, and #2637 remain blocked by their
  prerequisite chains.
- The bridge-layer Plucker chain is blocked behind #5998 and successors, with
  #6021 as the final universal identity issue.
- The Schmeisser root-product chain is blocked behind the exact-degree-two
  Schur issues, starting with #5947/#5948 after #6019.
- HexLLL harsh-cubic continuation #6016 is blocked on #5994 / PR #6017.

## Recommended next actions

1. Let #6018 land before resuming #5980 or any BZ product/entry proof threading.
2. Continue the HexMatrixMathlib Plucker bridge chain in order; do not reopen
   the stale Mathlib-free #5848 route unless the bridge-layer plan changes.
3. If #6017 lands, rerun the harsh-cubic evidence before dispatching broader
   LLL performance work.
4. Keep Phase 6 polish narrow: finish #6004, then use #6022 and #6023 to file
   worker-sized API cleanup issues rather than umbrella implementation tasks.
5. Keep Schmeisser work on the degree-two path through #6019, #5947, #5948,
   #5945, #5940, and #5924 before reviving derivative-bound consumers.
