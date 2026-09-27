/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Basic
public import HexRealAlgebraic.Roots

public section

namespace Hex.RealClosure

/-- Evaluate a rational polynomial with canonical real-algebraic arithmetic. -/
@[expose] def evalCanonical (p : DensePoly Rat) (x : Hex.RealAlgebraicNumber) :
    Hex.RealAlgebraicNumber :=
  DensePoly.evalCoeffList (p.toArray.toList.map Hex.RealAlgebraicNumber.ofRat) x

/-- Test the lower endpoint of the descriptor's open interval. -/
@[expose] def lowerMatches (lower : Endpoint Rat) (x : Hex.RealAlgebraicNumber) : Bool :=
  match lower with
  | .negInf => true
  | .finite q => decide (Hex.RealAlgebraicNumber.ofRat q < x)
  | .posInf => false

/-- Test the upper endpoint of the descriptor's open interval. -/
@[expose] def upperMatches (upper : Endpoint Rat) (x : Hex.RealAlgebraicNumber) : Bool :=
  match upper with
  | .posInf => true
  | .finite q => decide (x < Hex.RealAlgebraicNumber.ofRat q)
  | .negInf => false

/-- Check a canonical real algebraic number against the descriptor's interval
and its selected derivative signs. -/
@[expose] def Root.matches {context : Nat} (d : Root context)
    (x : Hex.RealAlgebraicNumber) : Bool :=
  lowerMatches d.raw.lower x && upperMatches d.raw.upper x &&
    decide (d.raw.queries.map (fun q => (evalCanonical q x).sign) = d.raw.signs)

/-- Search the independent canonical real-root list for the root selected by
the checked descriptor. -/
@[expose] def Root.canonical? {context : Nat} (d : Root context) :
    Option Hex.RealAlgebraicNumber :=
  ((Hex.ZPoly.clearDenominators d.raw.head).2.realAlgebraicRoots.toList).find? d.matches

/-- The checked descriptor selects one canonical real algebraic root. The
companion proves that the root-list search always succeeds. -/
@[expose] def Root.toCanonical {context : Nat} (d : Root context) :
    Hex.RealAlgebraicNumber :=
  d.canonical?.getD 0

/-- Evaluate a stored rational expression by canonical real-algebraic
arithmetic at its selected root. -/
@[expose] def Expression.toCanonical {context : Nat} {d : Root context}
    (a : Expression d) : Hex.RealAlgebraicNumber :=
  evalCanonical a.polynomial d.toCanonical

end Hex.RealClosure
