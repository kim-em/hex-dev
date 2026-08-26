/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSmith

open Hex Hex.Matrix

namespace HexSmithQuickstartTests

private def A : Matrix Int 2 2 := #m[2, 0; 0, 6]

#eval (snf A).rows
#eval (invariantFactors A).toList
#eval abelianStructure A
#eval (snfData A).left

end HexSmithQuickstartTests
