# foldl consolidation into a new HexBasic library

## Accomplished

Created `HexBasic`, a new lowest-level Mathlib-free library (depends only on
`Std`), as the home for general-purpose helpers that clearly belong upstream.

- `HexBasic/Fold.lean`: declares the four `Std.Associative` /
  `Std.LawfulIdentity` instances for `Lean.Grind.Semiring` **file-locally**
  (used only to prove the lemmas; not exported, so no global instance route is
  added for `Nat`/`Int` etc. in the bridge layers), then states the general
  `List.foldl` algebra the computational libraries reuse, in the `List`
  namespace with standard-library-aligned names. The accumulator-extraction
  and sum/prod bridges go through core's `List.foldl_assoc` /
  `List.foldl_map`. The only renamed-to-avoid-clash lemma is `foldl_const_step`
  (core/Mathlib use `List.foldl_const` for the unrelated iterate lemma).
  Lemmas: `foldl_congr`,
  `foldl_add_congr`, `foldl_mul_congr`, `foldl_const`,
  `foldl_add_eq_add_foldl`, `foldl_mul_eq_mul_foldl`, `foldl_add_eq_self`,
  `foldl_add_zero`, `foldl_add_mul_left(_zero)`, `foldl_add_mul_right_zero`,
  `foldl_add_add(_start)`, `foldl_add_comm` (Fubini), `foldl_add_perm`,
  `foldl_mul_perm`, `foldl_add_flatMap`, `foldl_add_single`, and the `Nat`
  bounds `le_foldl_add_self/of_mem`, `le_foldl_max_self/of_mem`.
- Moved `ListShim.lean` and `Vector/Modify.lean` from `HexMatrix` into
  `HexBasic` (both were `Std`-only in substance), rewiring `HexMatrix.Basic`,
  the `HexMatrix` umbrella, and `HexMatrix.Elementary`.

Consolidated duplicated copies onto the new API (builds verified green):

- `HexGF2/{Clmul,Multiply}.lean`: deleted two identical `foldl_keep`, use
  `List.foldl_const_step`.
- `HexPolyZ/Mignotte.lean`: deleted four `le_foldl_*` bounds, use the
  `List.le_foldl_*` versions.
- `HexLLL/Certificate.lean`: deleted `foldl_max_le_init` + `le_foldl_max`, use
  `List.le_foldl_max_of_mem`.

Wiring: `lean_lib HexBasic` in `lakefile.lean`; `HexBasic` root entry in
`libraries.yml` with `HexBasic` added to the deps of HexMatrix, HexGF2,
HexPolyZ, HexLLL. `scripts/check_dag.py` passes.

## Current frontier

HexBasic, HexGF2, HexPolyZ, HexMatrix build green standalone; full build
(incl. Mathlib bridge layers and HexLLL) in progress.

## Next step

Follow-up PRs (deliberately out of scope to keep this one reviewable):

- Migrate the matrix-tower `foldl_sum_*` family (HexMatrix/MatrixAlgebra,
  HexRowReduce/{Nullspace,Span}, HexMatrix/DotProduct, HexRowReduce/RowEchelon)
  onto the HexBasic API. ~50 call sites; the `Grind.Ring`-level keystones are
  already in place for it.
- Rename the determinant `foldl_det_*` zoo (HexDeterminant/Leibniz.lean +
  ~11 dependent files, ~160 call sites) to the HexBasic names; mechanical.
- Concrete-type product folds over `FpPoly`/`ZPoly` (Berlekamp/Hensel) need
  per-type `Std.Associative (· * ·)` instances first.
- Mathlib-side dedup of `foldl_finRange_eq_sum` (3 copies) and friends.
- Release wiring: add a `hex-basic` split repo to
  `scripts/release/{released.yml,synced.json}` before the next sync.

## Blockers

None.
