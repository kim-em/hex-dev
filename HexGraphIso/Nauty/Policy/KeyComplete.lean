/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxCombine
public import HexGraphIso.Nauty.Policy.Result
import all HexGraphIso.Nauty.Policy.MaxCombine

public section

namespace Hex.GraphIso.Nauty.Engine

/-- The structured engine computes the full specification key for every
nonempty coloured graph. -/
theorem canonSpecKey_eq_tracedKey {n k : Nat} (G : Colored n k) (hn0 : 0 < n) :
    canonSpecKey G = tracedKey G := Max.key_eq G hn0 (Max.rules G 100)

end Hex.GraphIso.Nauty.Engine
