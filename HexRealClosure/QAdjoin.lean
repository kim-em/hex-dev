/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Element
public import HexNumberField.Convert

public section

namespace Hex.RealClosure.Root.Handle

/-- Pack fixed-field coordinates at this handle's selected real generator.
The generator is part of the input type, so coordinates from another root
cannot enter this context without a checked conversion. -/
@[expose] def packQAdjoin {context : Nat} {d : Root context} (h : Root.Handle d)
    (c : Hex.QAdjoin h.canonical.toAlgebraic) : Element d :=
  Element.ofPolyWith h c.coeffs

end Hex.RealClosure.Root.Handle
