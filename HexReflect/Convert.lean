/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly

@[expose] public section

/-!
Direct conversion of reflected commutative-ring syntax to `Hex.MvPoly`.

The conversion consumes `Lean.Grind.CommRing.Expr` directly. It normalizes
with `Expr.toPoly`, or with `Expr.toPolyC c` when characteristic evidence is
available, traverses the resulting `Lean.Grind.CommRing.Poly`, translates each
ordered variable and exponent to a `Hex.Mono n`, maps every integer
coefficient through the requested coefficient map, and builds the polynomial
with `Hex.MvPoly.ofTerms` under the requested monomial comparator. Every
variable bound is checked; an identifier outside the sealed size is reported
as `none` rather than reduced modulo the size.
-/

namespace Hex.Reflect

open Lean.Grind.CommRing

/-- Reflected commutative-ring syntax, shared with `Lean.Meta.Sym.Arith`. -/
abbrev RingExpr := Lean.Grind.CommRing.Expr

namespace RingExpr

/-- Number of reflected syntax nodes. -/
def size : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ | .var _ => 1
  | .neg a => size a + 1
  | .pow a _ => size a + 1
  | .add a b | .sub a b | .mul a b => size a + size b + 1

/-- Largest literal exponent. -/
def maxExponent : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ | .var _ => 0
  | .neg a => maxExponent a
  | .pow a k => Nat.max k (maxExponent a)
  | .add a b | .sub a b | .mul a b => Nat.max (maxExponent a) (maxExponent b)

/-- One more than the largest variable identifier, or zero without
variables. -/
def varBound : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ => 0
  | .var i => i + 1
  | .neg a => varBound a
  | .pow a _ => varBound a
  | .add a b | .sub a b | .mul a b => Nat.max (varBound a) (varBound b)

/-- An upper bound on the number of monomials produced by expansion,
saturating at `cap`. Sums add term counts, products multiply them, and a
literal power raises the count to that power. -/
def termBound (cap : Nat) : RingExpr → Nat
  | .num _ | .natCast _ | .intCast _ | .var _ => Nat.min 1 cap
  | .neg a => termBound cap a
  | .pow a k => Nat.min (termBound cap a ^ k) cap
  | .add a b | .sub a b => Nat.min (termBound cap a + termBound cap b) cap
  | .mul a b => Nat.min (termBound cap a * termBound cap b) cap

end RingExpr

/-- Translate an ordered Grind monomial into an exponent vector, checking
every variable against the sealed size `n`. -/
def monoOfMon? (n : Nat) : Mon → Option (Mono n)
  | .unit => some Mono.zero
  | .mult pw m =>
    if h : pw.x < n then
      (monoOfMon? n m).map fun rest => Mono.mul (Mono.scale pw.k (Mono.unit ⟨pw.x, h⟩)) rest
    else
      none

/-- Translate a Grind polynomial into a term list over exponent vectors,
checking every variable against the sealed size `n`. -/
def polyTerms? (n : Nat) : Poly → Option (List (Mono n × Int))
  | .num k => some (if k = 0 then [] else [(Mono.zero, k)])
  | .add k m p => do
    let mo ← monoOfMon? n m
    let rest ← polyTerms? n p
    return (mo, k) :: rest

/-- Normalize reflected syntax, modulo the characteristic when evidence is
available. -/
def normalize (char? : Option Nat) (e : RingExpr) : Poly :=
  match char? with
  | none => e.toPoly
  | some c => e.toPolyC c

/-- The term list of a reflected expression over a sealed environment of size
`n`. -/
def convertTerms? (n : Nat) (char? : Option Nat) (e : RingExpr) :
    Option (List (Mono n × Int)) :=
  polyTerms? n (normalize char? e)

/-- Build the polynomial from integer-coefficient terms through a coefficient
map, merging monomials that became equal and dropping coefficients mapped to
zero. -/
def ofIntTerms {n : Nat} {C : Type} [Zero C] [Add C] [BEq C] [LawfulBEq C]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (ofInt : Int → C) (ts : List (Mono n × Int)) : MvPoly n C cmp :=
  MvPoly.ofTerms (ts.map fun t => (t.1, ofInt t.2))

/-- Direct conversion of reflected syntax to a polynomial over a sealed
environment of size `n`. -/
def convert? {C : Type} [Zero C] [Add C] [BEq C] [LawfulBEq C]
    (n : Nat) (char? : Option Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (ofInt : Int → C) (e : RingExpr) : Option (MvPoly n C cmp) :=
  (convertTerms? n char? e).map (ofIntTerms ofInt)

/-- The largest absolute coefficient of a term list, in bits. -/
def coefficientBits {n : Nat} (ts : List (Mono n × Int)) : Nat :=
  ts.foldl (fun acc t => Nat.max acc (Nat.log2 t.2.natAbs + 1)) 0


end Hex.Reflect
