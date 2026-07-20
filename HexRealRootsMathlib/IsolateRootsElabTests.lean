/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- PLAIN `public import` only: NO `import all`. The emitted `decide`s must reduce
-- in the kernel through the exposed count-check closure and the `SturmChainCert` /
-- `orderedAdjacent` certificates alone, exactly as a downstream `module` consumer
-- of the `isolate_roots` elaborator would see them.
public import HexRealRootsMathlib.IsolateRootsElab

public section

open Hex Polynomial HexRealRootsMathlib

namespace HexRealRootsMathlib.ElabTests

/-! ## `x⁴ − 2` -/

/-- `x⁴ − 2` as a `Hex.ZPoly`. -/
def x4m2 : ZPoly := DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1]

/-- Bare isolation of `x⁴ − 2` as a `ZPoly`. -/
noncomputable def iso_zpoly := isolate_roots x4m2

/-- `x⁴ − 2` over `Polynomial ℝ`, bare. -/
noncomputable def iso_real := isolate_roots (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2`, every root refined to width `2^(-20)`. -/
noncomputable def iso_w20 := isolate_roots (width := 2 ^ (-20 : ℤ)) (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2`, width `1/1000`. -/
noncomputable def iso_w1000 := isolate_roots (width := 1 / 1000) (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2`, width `10^(-2)`. -/
noncomputable def iso_w100 := isolate_roots (width := 10 ^ (-2 : ℤ)) (X ^ 4 - 2 : Polynomial ℝ)

/-! ## Coefficient rings -/

/-- Wilkinson-6 `∏_{i=1}^{6}(x − i)` over `Polynomial ℤ`. -/
noncomputable def iso_wilkinson :=
  isolate_roots ((X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) * (X - 6) : Polynomial ℤ)

/-- A `Polynomial ℚ` case: `2x² − 3x + 1 = (2x − 1)(x − 1)`. -/
noncomputable def iso_rat := isolate_roots (2 * X ^ 2 - 3 * X + 1 : Polynomial ℚ)

/-! ## Non-squarefree (exercises the core transport) -/

/-- `(x − 1)²(x − 3)` over `Polynomial ℤ`: two distinct real roots. -/
noncomputable def iso_nonsqfree :=
  isolate_roots ((X - 1) ^ 2 * (X - 3) : Polynomial ℤ)

/-! ## Nonzero constant -/

/-- A nonzero constant has no real roots: the empty isolation. -/
noncomputable def iso_const := isolate_roots (7 : Polynomial ℝ)

end HexRealRootsMathlib.ElabTests
