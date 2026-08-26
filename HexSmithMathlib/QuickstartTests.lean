/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSmithMathlib

open Hex Hex.Matrix

namespace HexSmithQuickstartTests

private def A : Matrix Int 2 2 := #m[2, 0; 0, 6]

#guard snf A == #m[2, 0; 0, 6]
#guard (invariantFactors A).toList == [2, 6]
#guard (abelianStructure A).torsionFactors == #[2, 6]
#guard (snfData A).left * A * (snfData A).right == snf A

open HexSmithMathlib

#check @smithNormalForm
#check @smithNormalForm_chain
#check @quotientEquiv

end HexSmithQuickstartTests
