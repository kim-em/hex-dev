/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvGcd.Gcd
public meta import HexMvGcd.Prs
public meta import HexMvGcd.Squarefree
public meta import HexMvPoly.Ring
public import HexMvGcd.Squarefree
import all HexMvGcd.Squarefree
import all HexMvPoly.Structural
import all HexMvPoly.Basic
import all HexMvPoly.Ring
import all HexMvPoly.Query

public section

/-! Squarefree decisions and coefficient-cast coherence regressions. -/

namespace Hex.MvPoly

private theorem boundsThree : ZMod64.Bounds 3 :=
  ⟨by decide, by decide⟩
attribute [local instance] boundsThree

private theorem primeThree : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime (by decide)
attribute [local instance] primeThree

private abbrev F3P1 := MvPoly 1 (ZMod64 3) Mono.lex
private abbrev F3P2 := MvPoly 2 (ZMod64 3) Mono.lex

example : Hex.Fraction.NonzeroOne (ZMod64 3) := inferInstance
example : PerfectFrac (ZMod64 3) := inferInstance

example (p : F3P1) : isSquarefree p = true ↔ Squarefree p :=
  isSquarefree_iff p

#guard
  let x : F3P1 := X 0
  isSquarefree (x * (x + 1))

-- One partial derivative vanishes, while the other witnesses squarefreeness.
#guard
  let x : F3P2 := X 0
  let y : F3P2 := X 1
  isSquarefree (x ^ 3 + y)

#guard
  let x : F3P1 := X 0
  !isSquarefree ((x + 1) ^ 2)

#guard
  let x : F3P2 := X 0
  let y : F3P2 := X 1
  !isSquarefree ((x ^ 3 + y) ^ 2)

#guard !isSquarefree (0 : F3P1)

-- In characteristic three this is `(x + 1)^3`, and its derivative vanishes.
#guard
  let x : F3P1 := X 0
  !isSquarefree (x ^ 3 + 1)

namespace CastTests

section Generic

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
  [BEq R] [LawfulBEq R] [Dvd R] [BezoutOps R] [GcdProducer R]
  {n : Nat} {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]

omit [BEq R] [LawfulBEq R] [Dvd R] [BezoutOps R] [GcdProducer R] in
/-- An unrelated cast in the caller's scope cannot change differentiation. -/
theorem derivatives_cast (cast : NatCast R) (p : MvPoly n R cmp) :
    (letI : NatCast R := cast; derivatives p) = derivatives p := by
  rfl

/-- An unrelated cast cannot change the decision, radical, or decomposition. -/
theorem squarefree_cast [NatNoZero R] (cast : NatCast R) (p : MvPoly n R cmp) :
    (letI : NatCast R := cast; (isSquarefree p, radical p, sqfDecomp p)) =
      (isSquarefree p, radical p, sqfDecomp p) := by
  rfl

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [BezoutOps R]
    [GcdProducer R] in
/-- Characteristic zero refers to the ring's cast even under local shadowing. -/
theorem characteristic_cast [NatNoZero R] (cast : NatCast R) :
    letI : NatCast R := cast
    NatNoZero R := by
  infer_instance

end Generic

/- The shadowing casts below are deliberately inert for the squarefree API.
These checks must keep compiling and evaluating identically with them in scope. -/
@[expose, instance_reducible] def badIntCast : NatCast Int := ⟨fun _ => 1⟩
@[expose, instance_reducible] def badRatCast : NatCast Rat := ⟨fun _ => 1⟩

abbrev P := MvPoly 1 Int Mono.lex
abbrev Q := MvPoly 1 Rat Mono.lex

@[expose] def repeated : P := (X 0 + 1) * (X 0 + 1)

/-- The low-level derivative accepts a caller-selected cast. -/
theorem explicit_derivative :
    (letI : NatCast Int := badIntCast; derivative 0 repeated) = (X 0 + C 2 : P) := by
  decide +kernel

/-- Squarefree replay fixes the derivative's cast to the ring operations. -/
theorem ring_derivatives :
    (letI : NatCast Int := badIntCast; derivatives repeated) =
      [C 2 * X 0 + C 2] := by
  decide +kernel

/-- The repeated nonconstant divisor witnesses semantic failure of squarefreeness. -/
theorem not_squarefree : ¬ Squarefree repeated := by
  intro h
  have hd : (X 0 + 1 : P) * (X 0 + 1) ∣ repeated :=
    ⟨1, by simp only [repeated, one_mul]⟩
  have hc := h.2 (X 0 + 1) hd
  have hn : ¬ IsConst (X 0 + 1 : P) := by
    change (X 0 + 1 : P).vars ≠ []
    decide +kernel
  exact hn hc

#guard
  letI : NatCast Int := badIntCast
  !isSquarefree repeated && radical repeated == (X 0 + 1 : P)

#guard
  letI : NatCast Int := badIntCast
  let decomp := sqfDecomp repeated
  decomp.content == 1 && decomp.factors.length == 1 &&
    decomp.factors.all (fun f => f.factor == (X 0 + 1 : P) && f.multiplicity == 2)

#guard
  letI : NatCast Rat := badRatCast
  let p : Q := C (3 / 2) * ((X 0 + 1 : Q) ^ 3)
  let decomp := sqfDecomp p
  !isSquarefree p && radical p == (X 0 + 1 : Q) &&
    decomp.content == 3 / 2 && decomp.factors.length == 1 &&
    decomp.factors.all (fun f => f.factor == (X 0 + 1 : Q) && f.multiplicity == 3)

#guard
  letI : NatCast Int := badIntCast
  !isSquarefree (0 : P) && radical (0 : P) == 0 &&
    isSquarefree (C 6 : P) && radical (C 6 : P) == 1 &&
    (sqfDecomp (C 6 : P)).content == 6 && (sqfDecomp (C 6 : P)).factors.isEmpty

#guard
  letI : NatCast (ZMod64 3) := ⟨fun _ => 1⟩
  let x : F3P1 := X 0
  !isSquarefree (x ^ 3 + 1) && isSquarefree (x * (x + 1))

/-- A nonzero but unrelated cast cannot certify characteristic zero in F₃. -/
theorem no_characteristic_zero [ZMod64.Bounds 3] [ZMod64.PrimeModulus 3] :
    letI : NatCast (ZMod64 3) := ⟨fun _ => 1⟩
    ¬ NatNoZero (ZMod64 3) := by
  intro h
  have hn := h.natCast_ne_zero 3 (by decide)
  exact hn (ZMod64.natCast_self (p := 3))

-- Direct decomposition helpers also reject positive characteristic, even
-- when an unrelated cast sends every natural to a nonzero coefficient.
example : True := by
  letI : NatCast (ZMod64 3) := ⟨fun _ => 1⟩
  fail_if_success have _ := sqfOps (R := ZMod64 3) 1
  fail_if_success have _ := sqfStep (R := ZMod64 3) sqfBase
  fail_if_success have _ := yunLoop (R := ZMod64 3) (cmp := Mono.lex) (n := 1) 0 1 1 1 0 []
  trivial

/-- info: 'Hex.MvPoly.CastTests.squarefree_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms squarefree_cast

/-- info: 'Hex.MvPoly.CastTests.ring_derivatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ring_derivatives

/-- info: 'Hex.MvPoly.CastTests.not_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_squarefree

/-- info: 'Hex.MvPoly.CastTests.no_characteristic_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_characteristic_zero

end CastTests

namespace OrderRegression

abbrev P := MvPoly 3 Int Mono.grlex

/-- Recursive content normalization and the caller's monomial order may choose
different leading coefficients. The main-part unit must remain in the scalar
output so exact replay retains its sign. -/
def input : P :=
  let x : P := X 0
  let y : P := X 1
  let z : P := X 2
  polyNormalize ((y - z ^ 2) * (x + 1))

#guard
  let decomp := sqfDecomp input
  decomp.factors.foldl
    (fun acc factor => acc * factor.factor ^ factor.multiplicity)
    (C decomp.content) == input

end OrderRegression

/-- info: 'Hex.MvPoly.sqfDecomp_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqfDecomp_prod

/-- info: 'Hex.MvPoly.sqfDecomp_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqfDecomp_squarefree

/-- info: 'Hex.MvPoly.sqfDecomp_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqfDecomp_primitive

/-- info: 'Hex.MvPoly.sqfDecomp_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqfDecomp_coprime

/-- info: 'Hex.MvPoly.sqfDecomp_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqfDecomp_nonconstant

end Hex.MvPoly
