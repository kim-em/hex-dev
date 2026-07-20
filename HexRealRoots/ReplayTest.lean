/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- PLAIN `public import` only: NO `import all`. This module is the regression
-- lock for the `@[expose]` kernel-replay closure. Every `decide` below must
-- reduce in the kernel through the exposed bodies of `sturmChain`, `sturmCount`,
-- `rootCount`, `hasSquarefreeSturmChain`, `SturmChainCert`, and `orderedAdjacent`
-- alone. If a future edit drops an `@[expose]` (or reintroduces a `private` in
-- the closure), one of these `decide`s stops reducing and this module fails —
-- surfacing the regression that a downstream `module` consumer would hit.
public import HexRealRoots.Cert

/-!
Regression lock for the kernel-replay exposure.

The `isolate_roots` term elaborator in `HexRealRootsMathlib` reifies a Sturm
chain as a literal and discharges its certificates by `decide` against the
exposed closure, with a plain `import` (no `import all`). This module reproduces
that reduction discipline on small literal data, so the exposure cannot silently
regress.
-/
namespace Hex.ReplayTest

/-- The squarefree Sturm certificate reduces through the exposed closure. -/
example : ZPoly.hasSquarefreeSturmChain (DensePoly.ofCoeffs #[(-1 : Int), 0, 1]) := by
  decide

/-- A `sturmCount` value: `x² − 1` has one root in `(0, 2]` (the root at `1`).
Reduces without `import all`, unlike the same check stated in `Var.lean`. -/
example : sturmCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide)) = 1 := by
  decide

/-- A `rootCount` value: `x² − 1` has two real roots. -/
example : rootCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1]) = 2 := by
  decide

/-- A `SturmChainCert` instance: the literal chain `[x² − 1, x, 1]` is certified
as *the* Sturm chain of `x² − 1`, by coefficient-level checks that kernel-reduce
(no structural `Array` equality). -/
example : SturmChainCert (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    #[DensePoly.ofCoeffs #[(-1 : Int), 0, 1],
      DensePoly.ofCoeffs #[(0 : Int), 1],
      DensePoly.ofCoeffs #[(1 : Int)]] := by
  decide

/-- An `orderedAdjacent` check on literal isolation data: the two isolations of
`x² − 1`, `(−2, 0]` and `(0, 2]`, are adjacent-ordered (`0 ≤ 0`). The `count_one`
witnesses also reduce through the exposed `sturmCount`. -/
example : orderedAdjacent (p := DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    #[⟨DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 0) (by decide), by decide⟩,
      ⟨DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide), by decide⟩] = true := by
  decide

end Hex.ReplayTest
