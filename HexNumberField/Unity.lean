/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.RootSelection
public section

/-! Roots of unity through integer binomial isolation and fixed-field powers. -/
namespace Hex.AlgebraicNumber
namespace Unity

/-- For even orders, the smaller binomial already contains the primitive root. -/
@[expose] def polynomial (n : Nat) : ZPoly :=
  if n % 2 = 0 then DensePoly.monomial (n / 2) 1 + DensePoly.C 1
  else DensePoly.monomial n 1 - DensePoly.C 1

/-- Select the upper root nearest to the positive real axis. -/
@[expose] def generator? (n : Nat) : Option AlgebraicNumber :=
  if n ≤ 1 then some 1
  else if n = 2 then some (-1)
  else if n = 4 then some I
  else do
    let roots ← RootSelection.integerRoots? (polynomial n)
    RootSelection.maximum? (roots.toList.filter (fun r => decide (r.side = .upper)))

/-- The standard positive primitive nth root; order zero is defined as one. -/
@[expose] def generator (n : Nat) : AlgebraicNumber :=
  match generator? n with
  | some a => a
  | none => Hex.panicWith 1 "AlgebraicNumber.rootOfUnity: root selection failed"

/-- Power in a single presentation, exactifying once at the end. -/
@[expose] def power (a : AlgebraicNumber) (k : Nat) : AlgebraicNumber :=
  (a.toQAdjoin ^ k).toAlgebraicNumber

end Unity

/-- The root of unity `exp (2*pi*I*q)`. The rational angle is reduced modulo one;
its reduced denominator is the exact order. General orders isolate an integer
binomial, select one primitive generator, and use fixed-field powers. -/
@[expose] def rootOfUnity (q : Rat) : AlgebraicNumber :=
  let n := q.den
  let k := (q.num % (n : Int)).toNat
  if k = 0 then 1
  else
    let a := Unity.generator n
    if k = 1 then a
    else if k + 1 = n then a.conj
    else Unity.power a k

end Hex.AlgebraicNumber
