# HexManual recipes — HexRowReduce template (PR 2)

## Accomplished

- Added a `# Recipes` section to the HexRowReduce chapter with two
  executable+proof-side how-to pairs, in the mathlib-phrasebook style:
  - "find a basis for the kernel" / "prove a fact about the Mathlib
    kernel by running Hex" (rank via `rank_eq` + `decide +kernel`).
  - "test row-span membership" / "prove row-span membership in Mathlib"
    (`spanContains_iff_mem_span` + `decide +kernel`).
- Executable recipes build matrices with `#m[...]` (#8456) and show real
  results via `#eval` + checked `leanOutput`; proof-side recipes prove a
  *Mathlib* fact by running the executable through a bridge
  correspondence theorem and closing with `decide +kernel`.
- `decide +kernel` chosen over `decide_cbv`: both kernel-honest (axioms
  `propext, Classical.choice, Quot.sound`; no `native_decide`), but
  `decide +kernel` is ~40x faster (29-64ms vs 1.3-2.6s at 4x4/5x5) and
  needs no `maxHeartbeats` bump.
- The chapter now imports `HexRowReduceMathlib` (so it pulls Mathlib);
  the prose marks the executable -> Mathlib transition explicitly.
- Verified `decide +kernel` proof-side feasibility for the determinant
  (`det_eq`) and Bareiss (`bareiss_eq_mathlib_det`) chapters too.

## Current frontier

HexRowReduce is the complete recipe template (two pairs). Depends on
#8456 (`#m[...]` notation) and #8461 (the `#m[...]`-format Repr), both
unmerged. Built locally against #8456's notation.

## Next step

After #8456 + #8461 merge: rebase onto main, drop the locally-vendored
Notation.lean, refresh the matrix-grid `leanOutput`s to the new
`#m[...]` render format (build flags mismatches). Then replicate the
template across HexMatrix, HexDeterminant, HexBareiss, HexGF2, HexGFq,
HexLLL (executable-only where kernel reduction is too heavy). Then PR 3:
`PLAN/Phase7.md` + `SPEC/recipes.md`.

## Blockers

Recipes PR is a draft until #8456 and #8461 land.
