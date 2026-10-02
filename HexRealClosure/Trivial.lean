/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.CompleteRoots
public import HexRealClosure.Canonical

public section

namespace Hex.RealClosure.Trivial

/-- The existing real-algebraic backend's coefficient representation for a
rational polynomial, including the zero polynomial. -/
@[expose] def polynomial (p : DensePoly Rat) : RealAlgebraicPoly :=
  RealAlgebraicPoly.ofArray (p.toArray.map RealAlgebraicNumber.ofRat)

/-- Convert one generic rational root using the existing selected-root
conversion; point roots retain their rational value. -/
@[expose] def canonical {context : Nat} :
    Isolation.Root (Sturm.orderSign : Rat → Int) context → RealAlgebraicNumber
  | .point q => RealAlgebraicNumber.ofRat q
  | .selected descriptor => Hex.RealClosure.Root.toCanonical descriptor

/-- Retain the exact multiplicity when converting one generic root entry. -/
@[expose] def entry {context : Nat} (root : Roots.Entry (Sturm.orderSign : Rat → Int) context) : RealRootCount :=
  ⟨canonical root.root, root.multiplicity, root.positive⟩

/-- Convert the complete generic output, retaining `all`, order and labels. -/
@[expose] def output {context : Nat} : Roots.Output (Sturm.orderSign : Rat → Int) context → RealRootSet
  | .all => .all
  | .finite entries => .finite ((entries.map entry).toArray)

/-- The generic rational route after conversion to the existing canonical
real-algebraic carrier. The companion proves exact backend agreement. -/
@[expose] def roots (context : Nat) (p : DensePoly Rat) : RealRootSet :=
  output (Roots.roots Sturm.orderSign context p)

/-- Delegate comparison of converted roots to the existing real-algebraic
comparison. The companion identifies the generic checked comparison with it. -/
@[expose] def compare {context : Nat} (a b : Isolation.Root (Sturm.orderSign : Rat → Int) context) : Ordering :=
  RealAlgebraicNumber.compare (canonical a) (canonical b)

end Hex.RealClosure.Trivial
