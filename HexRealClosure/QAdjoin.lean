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
require a proof of generator identity before entering this context. -/
@[expose] def packQAdjoin {context : Nat} {d : Root context} (h : Root.Handle d)
    (c : Hex.QAdjoin h.canonical.toAlgebraic) : Element d :=
  Element.ofPolyWith h c.coeffs

/-- Pack coordinates when their generator is proved equal to this handle's
selected canonical root. -/
@[expose] def packQAdjoinOf {context : Nat} {d : Root context}
    {a : Hex.AlgebraicNumber} (h : Root.Handle d)
    (ha : a = h.canonical.toAlgebraic) (c : Hex.QAdjoin a) : Element d :=
  h.packQAdjoin (ha ▸ c)

end Hex.RealClosure.Root.Handle
