/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.ExactDiv

public section

/-!
The fraction field used internally by the Mathlib-free subresultant proof.

The executable resultant never constructs these values.  They provide the
classical quotient-field setting in which the Brown--Traub scale identities
can be proved before exact quotients are pulled back to the coefficient ring.
This module is retained as proof infrastructure: `SubresultantMinor` consumes
`ofCoeff` for its fraction-embedding image certificates, and the manual embeds
the quotient-pullback theorems (`div_pullback`, `divExp_exact`).
-/

namespace Hex

universe u

namespace Fraction

/-- The nontriviality needed to use `1` as a fraction denominator. Brown's
nonzero input hypothesis supplies this locally even though the lightweight
commutative-ring hierarchy itself permits the trivial ring. -/
class NonzeroOne (R : Type u) [Zero R] [One R] : Prop where
  one_ne_zero : (1 : R) ≠ 0

namespace NonzeroOne

/-- Any nonzero element of a commutative ring witnesses its nontriviality. -/
theorem of_ne_zero {R : Type u} [Lean.Grind.CommRing R] {a : R} (ha : a ≠ 0) :
    NonzeroOne R := by
  refine ⟨?_⟩
  intro hone
  apply ha
  calc
    a = a * 1 := (Lean.Grind.Semiring.mul_one a).symm
    _ = a * 0 := by rw [hone]
    _ = 0 := Lean.Grind.Semiring.mul_zero a

end NonzeroOne
end Fraction

/-- A numerator and a certified nonzero denominator. -/
structure Fraction.Rep (R : Type u) [Zero R] where
  num : R
  den : R
  den_ne : den ≠ 0

namespace Fraction.Rep

variable {R : Type u} [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]

/-- Cross-multiplication equivalence on fraction representatives. -/
@[expose]
def Rel (a b : Fraction.Rep R) : Prop :=
  a.num * b.den = b.num * a.den

omit [Div R] [ExactDivLaws R] in
/-- Cross-multiplication is reflexive. -/
theorem rel_refl (a : Fraction.Rep R) : Rel a a := by
  exact rfl

omit [Div R] [ExactDivLaws R] in
/-- Cross-multiplication is symmetric. -/
theorem rel_symm {a b : Fraction.Rep R} (h : Rel a b) : Rel b a := by
  exact h.symm

/-- Cross-multiplication is transitive; cancellation by the nonzero middle
denominator is where `ExactDivLaws` enters. -/
theorem rel_trans {a b c : Fraction.Rep R}
    (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  apply ExactDivLaws.mul_right_cancel b.den_ne
  unfold Rel at hab hbc
  calc
    a.num * c.den * b.den = (a.num * b.den) * c.den := by grind
    _ = (b.num * a.den) * c.den := by rw [hab]
    _ = (b.num * c.den) * a.den := by grind
    _ = (c.num * b.den) * a.den := by rw [hbc]
    _ = c.num * a.den * b.den := by grind

/-- Fraction representatives form a setoid under cross multiplication. -/
instance : Setoid (Fraction.Rep R) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- Cross-multiplication equivalence is decidable when coefficient equality
is. -/
instance [DecidableEq R] (a b : Fraction.Rep R) : Decidable (Rel a b) :=
  by
    unfold Rel
    infer_instance

/-- Product of two representatives. -/
def mul (a b : Fraction.Rep R) : Fraction.Rep R :=
  ⟨a.num * b.num, a.den * b.den,
    ExactDivLaws.mul_ne_zero a.den_ne b.den_ne⟩

/-- Sum of two representatives. -/
def add (a b : Fraction.Rep R) : Fraction.Rep R :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den,
    ExactDivLaws.mul_ne_zero a.den_ne b.den_ne⟩

/-- Additive inverse of a representative. -/
def neg (a : Fraction.Rep R) : Fraction.Rep R :=
  ⟨-a.num, a.den, a.den_ne⟩

/-- Representative products respect cross-multiplication equivalence. -/
theorem mul_rel {a b c d : Fraction.Rep R}
    (hac : Rel a c) (hbd : Rel b d) : Rel (mul a b) (mul c d) := by
  unfold Rel at hac hbd
  unfold Rel mul
  calc
    a.num * b.num * (c.den * d.den) =
        (a.num * c.den) * (b.num * d.den) := by grind
    _ = (c.num * a.den) * (d.num * b.den) := by rw [hac, hbd]
    _ = c.num * d.num * (a.den * b.den) := by grind

/-- Representative sums respect cross-multiplication equivalence. -/
theorem add_rel {a b c d : Fraction.Rep R}
    (hac : Rel a c) (hbd : Rel b d) : Rel (add a b) (add c d) := by
  unfold Rel at hac hbd
  unfold Rel add
  calc
    (a.num * b.den + b.num * a.den) * (c.den * d.den) =
        (a.num * c.den) * (b.den * d.den) +
          (b.num * d.den) * (a.den * c.den) := by grind
    _ = (c.num * a.den) * (b.den * d.den) +
          (d.num * b.den) * (a.den * c.den) := by rw [hac, hbd]
    _ = (c.num * d.den + d.num * c.den) * (a.den * b.den) := by grind

omit [Div R] [ExactDivLaws R] in
/-- Representative negation respects cross-multiplication equivalence. -/
theorem neg_rel {a b : Fraction.Rep R} (hab : Rel a b) :
    Rel (neg a) (neg b) := by
  unfold Rel at hab
  unfold Rel neg
  rw [Lean.Grind.Ring.neg_mul, Lean.Grind.Ring.neg_mul, hab]

end Fraction.Rep

/-- The quotient field of a commutative exact-division domain. -/
@[expose]
def Fraction (R : Type u) [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R] :=
  Quotient (Fraction.Rep.instSetoid (R := R))

namespace Fraction

variable {R : Type u} [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]

/-- Decidable equality inherited from cross multiplication of representatives. -/
instance [DecidableEq R] : DecidableEq (Fraction R) :=
  fun q₁ q₂ =>
    Quotient.recOnSubsingleton₂ q₁ q₂ fun a b =>
      if h : Fraction.Rep.Rel a b then
        isTrue (Quotient.sound h)
      else
        isFalse fun hab => h (Quotient.exact hab)

variable [NonzeroOne R]

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Inject a representative into its quotient. -/
@[expose]
def ofRep (a : Fraction.Rep R) : Fraction R :=
  Quotient.mk _ a

/-- Embed a coefficient as a fraction with denominator one. -/
@[expose]
def ofCoeff (a : R) : Fraction R :=
  ofRep ⟨a, 1, NonzeroOne.one_ne_zero⟩

omit [Div R] [ExactDivLaws R] in
private theorem one_ne_zero : (1 : R) ≠ 0 := by
  exact NonzeroOne.one_ne_zero

omit [NonzeroOne R] in
private theorem ofRep_eq {a b : Fraction.Rep R}
    (h : Fraction.Rep.Rel a b) : ofRep a = ofRep b :=
  Quotient.sound h

/-- Multiplication of fractions. -/
@[expose]
protected def mul : Fraction R → Fraction R → Fraction R :=
  Quotient.lift₂ (fun a b => ofRep (Fraction.Rep.mul a b)) (by
    intro a b c d hac hbd
    exact ofRep_eq (Fraction.Rep.mul_rel hac hbd))

/-- Addition of fractions. -/
@[expose]
protected def add : Fraction R → Fraction R → Fraction R :=
  Quotient.lift₂ (fun a b => ofRep (Fraction.Rep.add a b)) (by
    intro a b c d hac hbd
    exact ofRep_eq (Fraction.Rep.add_rel hac hbd))

/-- Negation of fractions. -/
@[expose]
protected def neg : Fraction R → Fraction R :=
  Quotient.lift (fun a => ofRep (Fraction.Rep.neg a)) (by
    intro a b hab
    exact ofRep_eq (Fraction.Rep.neg_rel hab))

/-- Zero is the embedded coefficient zero. -/
instance : Zero (Fraction R) := ⟨ofCoeff 0⟩
/-- One is the embedded coefficient one. -/
instance : One (Fraction R) := ⟨ofCoeff 1⟩
/-- Addition of fractions. -/
instance : Add (Fraction R) := ⟨Fraction.add⟩
/-- Multiplication of fractions. -/
instance : Mul (Fraction R) := ⟨Fraction.mul⟩
/-- Negation of fractions. -/
instance : Neg (Fraction R) := ⟨Fraction.neg⟩
/-- Subtraction of fractions, defined as addition of the negation. -/
instance : Sub (Fraction R) := ⟨fun a b => a + -b⟩

omit [NonzeroOne R] in
private theorem rep_eq (a b : Fraction.Rep R) (h : Fraction.Rep.Rel a b) :
    (ofRep a : Fraction R) = ofRep b :=
  Quotient.sound h

/-- Zero is a right additive identity. -/
theorem add_zero (a : Fraction R) : a + 0 = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.add
      simp only [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero,
        Lean.Grind.Semiring.mul_one]

omit [NonzeroOne R] in
/-- Fraction addition is commutative. -/
theorem add_comm (a b : Fraction R) : a + b = b + a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.add
      grind

omit [NonzeroOne R] in
/-- Fraction addition is associative. -/
theorem add_assoc (a b c : Fraction R) : a + b + c = a + (b + c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.add
      grind

omit [NonzeroOne R] in
/-- Fraction multiplication is associative. -/
theorem mul_assoc (a b c : Fraction R) : a * b * c = a * (b * c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      grind

/-- One is a right multiplicative identity. -/
theorem mul_one (a : Fraction R) : a * 1 = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      simp only [Lean.Grind.Semiring.mul_one]

/-- One is a left multiplicative identity. -/
theorem one_mul (a : Fraction R) : 1 * a = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      simp only [Lean.Grind.Semiring.one_mul]

omit [NonzeroOne R] in
/-- Fraction multiplication distributes over addition on the left. -/
theorem left_distrib (a b c : Fraction R) : a * (b + c) = a * b + a * c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul Fraction.Rep.add
      grind

omit [NonzeroOne R] in
/-- Fraction multiplication distributes over addition on the right. -/
theorem right_distrib (a b c : Fraction R) : (a + b) * c = a * c + b * c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul Fraction.Rep.add
      grind

/-- Zero is a left multiplicative absorber. -/
theorem zero_mul (a : Fraction R) : 0 * a = 0 := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      simp only [Lean.Grind.Semiring.zero_mul]

/-- Zero is a right multiplicative absorber. -/
theorem mul_zero (a : Fraction R) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      simp only [Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.zero_mul]

/-- Every fraction cancels with its negation. -/
theorem neg_add_cancel (a : Fraction R) : -a + a = 0 := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.neg Fraction.Rep.add
      grind

omit [NonzeroOne R] in
/-- Fraction negation is involutive. -/
theorem neg_neg (a : Fraction R) : -(-a) = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.neg
      rw [Lean.Grind.AddCommGroup.neg_neg]

omit [NonzeroOne R] in
/-- Fraction multiplication is commutative. -/
theorem mul_comm (a b : Fraction R) : a * b = b * a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      grind

omit [NonzeroOne R] in
/-- Negation moves out of the left factor of a product. -/
theorem neg_mul (a b : Fraction R) : (-a) * b = -(a * b) := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.neg Fraction.Rep.mul
      grind

/-- The coefficient embedding preserves zero. -/
@[simp]
theorem ofCoeff_zero :
    ofCoeff (Zero.zero : R) = (Zero.zero : Fraction R) := rfl

/-- The coefficient embedding preserves one. -/
@[simp]
theorem ofCoeff_one :
    ofCoeff (One.one : R) = (One.one : Fraction R) := rfl

/-- The coefficient embedding preserves addition. -/
@[simp]
theorem ofCoeff_add (a b : R) : ofCoeff (a + b) = ofCoeff a + ofCoeff b := by
  apply rep_eq
  unfold Fraction.Rep.Rel Fraction.Rep.add
  grind

/-- The coefficient embedding preserves multiplication. -/
@[simp]
theorem ofCoeff_mul (a b : R) : ofCoeff (a * b) = ofCoeff a * ofCoeff b := by
  apply rep_eq
  unfold Fraction.Rep.Rel Fraction.Rep.mul
  grind

/-- The coefficient embedding preserves negation. -/
@[simp]
theorem ofCoeff_neg (a : R) : ofCoeff (-a) = -ofCoeff a := by
  apply rep_eq
  unfold Fraction.Rep.Rel Fraction.Rep.neg
  grind

/-- The coefficient embedding preserves subtraction. -/
@[simp]
theorem ofCoeff_sub (a b : R) : ofCoeff (a - b) = ofCoeff a - ofCoeff b := by
  rw [Lean.Grind.Ring.sub_eq_add_neg (α := R)]
  change ofCoeff (a + -b) = ofCoeff a + -ofCoeff b
  rw [ofCoeff_add, ofCoeff_neg]

/-- The coefficient embedding is injective. -/
theorem ofCoeff_injective {a b : R} (h : ofCoeff a = ofCoeff b) : a = b := by
  have hrel : a * 1 = b * 1 := Quotient.exact h
  simpa only [Lean.Grind.Semiring.mul_one] using hrel

/-- Natural powers of fractions. -/
@[expose]
def natPow (a : Fraction R) : Nat → Fraction R
  | 0 => 1
  | n + 1 => natPow a n * a

/-- Natural-number casts factor through the coefficient embedding. -/
instance : NatCast (Fraction R) :=
  ⟨fun n => ofCoeff (Nat.cast n)⟩

/-- Numerals factor through the coefficient embedding, reusing the canonical
zero and one. -/
instance (n : Nat) : OfNat (Fraction R) n :=
  ⟨match n with
    | 0 => Zero.zero
    | 1 => One.one
    | n + 2 => ofCoeff (OfNat.ofNat (α := R) (n + 2))⟩

/-- Fraction numerals agree with embedded coefficient numerals. -/
theorem ofNat_eq_ofCoeff (n : Nat) :
    OfNat.ofNat (α := Fraction R) n = ofCoeff (OfNat.ofNat (α := R) n) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n => rfl

/-- Natural scalar multiplication is multiplication by the cast scalar. -/
instance : SMul Nat (Fraction R) :=
  ⟨fun n a => (Nat.cast n : Fraction R) * a⟩

/-- Natural powers of fractions via `natPow`. -/
instance : HPow (Fraction R) Nat (Fraction R) :=
  ⟨natPow⟩

/-- Integer casts factor through the coefficient embedding. -/
instance : IntCast (Fraction R) :=
  ⟨fun i => ofCoeff (Int.cast i)⟩

/-- Integer scalar multiplication is multiplication by the cast scalar. -/
instance : SMul Int (Fraction R) :=
  ⟨fun i a => (Int.cast i : Fraction R) * a⟩

/-- The quotient construction is a lightweight semiring. -/
instance : Lean.Grind.Semiring (Fraction R) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact add_zero
  · exact add_comm
  · exact add_assoc
  · exact mul_assoc
  · exact mul_one
  · exact one_mul
  · exact left_distrib
  · exact right_distrib
  · exact zero_mul
  · exact mul_zero
  · intro a
    change natPow a 0 = 1
    rw [natPow]
  · intro a n
    change natPow a (n + 1) = natPow a n * a
    rw [natPow]
  · intro n
    rw [ofNat_eq_ofCoeff, ofNat_eq_ofCoeff, ofNat_eq_ofCoeff]
    rw [← ofCoeff_add]
    exact congrArg (ofCoeff (R := R))
      (Lean.Grind.Semiring.ofNat_succ (α := R) n)
  · intro n
    rw [ofNat_eq_ofCoeff]
    exact congrArg (ofCoeff (R := R))
      (Lean.Grind.Semiring.ofNat_eq_natCast (α := R) n)
  · intro _ _
    rfl

/-- The quotient construction is a lightweight ring. -/
instance : Lean.Grind.Ring (Fraction R) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · exact neg_add_cancel
  · intro _ _
    rfl
  · intro i a
    change ofCoeff (R := R) (Int.cast (-i)) * a =
      -(ofCoeff (R := R) (Int.cast i) * a)
    rw [Lean.Grind.Ring.intCast_neg, ofCoeff_neg, neg_mul]
  · intro n a
    change ofCoeff (R := R) (Int.cast (Int.ofNat n)) * a =
      ofCoeff (R := R) (Nat.cast n) * a
    have hcast : Int.cast (R := R) (Int.ofNat n) = Nat.cast n :=
      Lean.Grind.Ring.intCast_natCast n
    exact congrArg (fun x : Fraction R => x * a)
      (congrArg (ofCoeff (R := R)) hcast)
  · intro n
    rw [ofNat_eq_ofCoeff]
    exact congrArg (ofCoeff (R := R))
      (Lean.Grind.Ring.intCast_ofNat (α := R) n)
  · intro i
    change ofCoeff (R := R) (Int.cast (-i)) =
      -ofCoeff (R := R) (Int.cast i)
    rw [Lean.Grind.Ring.intCast_neg, ofCoeff_neg]

/-- The quotient construction is a lightweight commutative ring. -/
instance : Lean.Grind.CommRing (Fraction R) := by
  refine Lean.Grind.CommRing.mk ?_
  exact mul_comm

omit [NonzeroOne R] in
/-- Related representatives have zero numerators simultaneously. -/
private theorem num_eq_zero_iff {a b : Fraction.Rep R}
    (hab : Fraction.Rep.Rel a b) : a.num = 0 ↔ b.num = 0 := by
  constructor
  · intro ha
    apply ExactDivLaws.mul_right_cancel a.den_ne
    unfold Fraction.Rep.Rel at hab
    calc
      b.num * a.den = 0 := by simpa [ha, Lean.Grind.Semiring.zero_mul] using hab.symm
      _ = 0 * a.den := by rw [Lean.Grind.Semiring.zero_mul]
  · intro hb
    apply ExactDivLaws.mul_right_cancel b.den_ne
    unfold Fraction.Rep.Rel at hab
    calc
      a.num * b.den = 0 := by simpa [hb, Lean.Grind.Semiring.zero_mul] using hab
      _ = 0 * b.den := by rw [Lean.Grind.Semiring.zero_mul]

variable [DecidableEq R]

/-- Reciprocal of a fraction representative, with zero sent to zero. -/
@[expose]
def invRep (a : Fraction.Rep R) : Fraction R :=
  if h : a.num = 0 then 0 else ofRep ⟨a.den, a.num, h⟩

private theorem invRep_rel {a b : Fraction.Rep R}
    (hab : Fraction.Rep.Rel a b) : invRep a = invRep b := by
  by_cases ha : a.num = 0
  · have hb : b.num = 0 := (num_eq_zero_iff hab).mp ha
    simp [invRep, ha, hb]
  · have hb : b.num ≠ 0 := by
      intro hb
      exact ha ((num_eq_zero_iff hab).mpr hb)
    unfold invRep
    rw [dif_neg ha, dif_neg hb]
    apply rep_eq
    unfold Fraction.Rep.Rel at hab ⊢
    grind

/-- Multiplicative inverse in the fraction field. -/
@[expose]
protected def inv : Fraction R → Fraction R :=
  Quotient.lift invRep (by
    intro a b hab
    exact invRep_rel hab)

/-- Total inversion of fractions, with zero sent to zero. -/
instance : Inv (Fraction R) := ⟨Fraction.inv⟩
/-- Division of fractions is multiplication by the total inverse. -/
instance : Div (Fraction R) := ⟨fun a b => a * b⁻¹⟩

omit [NonzeroOne R] [DecidableEq R] in
/-- Products of embedded representatives multiply representatives. -/
@[simp]
theorem mul_ofRep (a b : Fraction.Rep R) :
    ofRep a * ofRep b = ofRep (Fraction.Rep.mul a b) := rfl

/-- Inverting an embedded representative applies `invRep`. -/
@[simp]
theorem inv_ofRep (a : Fraction.Rep R) : (ofRep a)⁻¹ = invRep a := rfl

omit [DecidableEq R] in
/-- A representative is zero exactly when its numerator is zero. -/
theorem ofRep_eq_zero_iff (a : Fraction.Rep R) : ofRep a = 0 ↔ a.num = 0 := by
  constructor
  · intro h
    have hrel : a.num * 1 = 0 * a.den := Quotient.exact h
    simpa only [Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.zero_mul] using hrel
  · intro h
    apply rep_eq
    unfold Fraction.Rep.Rel
    simp [h, Lean.Grind.Semiring.zero_mul]

omit [DecidableEq R] in
/-- The coefficient embedding reflects zero. -/
@[simp]
theorem ofCoeff_eq_zero_iff (a : R) : ofCoeff a = 0 ↔ a = 0 := by
  exact ofRep_eq_zero_iff ⟨a, 1, one_ne_zero⟩

/-- Fraction inversion uses the stable zero branch. -/
@[simp]
theorem inv_zero : (0 : Fraction R)⁻¹ = 0 := by
  change invRep ⟨0, 1, one_ne_zero⟩ = 0
  simp [invRep]

/-- Every nonzero fraction has the expected multiplicative inverse. -/
theorem mul_inv_cancel {a : Fraction R} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  induction a using Quotient.inductionOn with
  | _ a =>
      change ofRep a * (ofRep a)⁻¹ = 1
      have hnum : a.num ≠ 0 := by
        intro hnum
        exact ha ((ofRep_eq_zero_iff a).mpr hnum)
      rw [inv_ofRep]
      have hinv : invRep a = ofRep ⟨a.den, a.num, hnum⟩ := by
        simp [invRep, hnum]
      rw [hinv, mul_ofRep]
      apply rep_eq
      unfold Fraction.Rep.Rel Fraction.Rep.mul
      grind

omit [DecidableEq R] in
/-- Zero and one are distinct in the fraction field. -/
theorem zero_ne_one : (0 : Fraction R) ≠ 1 := by
  intro h
  have hcoeff : (0 : R) = 1 := ofCoeff_injective h
  exact one_ne_zero hcoeff.symm

/-- Inversion is involutive. -/
theorem inv_inv (a : Fraction R) : a⁻¹⁻¹ = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
      change (ofRep a)⁻¹⁻¹ = ofRep a
      rw [inv_ofRep]
      by_cases hnum : a.num = 0
      · have hzero : ofRep a = 0 := (ofRep_eq_zero_iff a).mpr hnum
        rw [show invRep a = 0 by simp [invRep, hnum], inv_zero, hzero]
      · rw [show invRep a = ofRep ⟨a.den, a.num, hnum⟩ by simp [invRep, hnum],
          inv_ofRep]
        unfold invRep
        rw [dif_neg a.den_ne]

/-- The inverse of one is one. -/
theorem inv_one : (1 : Fraction R)⁻¹ = 1 := by
  have hone : (1 : Fraction R) ≠ 0 := fun h => zero_ne_one h.symm
  have h := mul_inv_cancel hone
  rw [one_mul] at h
  exact h

/-- Integer powers of fractions use natural powers and total inversion. -/
@[expose]
def intPow (a : Fraction R) : Int → Fraction R
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

/-- Integer powers of fractions via `intPow`. -/
instance : HPow (Fraction R) Int (Fraction R) := ⟨intPow⟩

/-- Division is multiplication by the fraction inverse. -/
theorem div_eq_mul_inv (a b : Fraction R) : a / b = a * b⁻¹ := rfl

/-- A nonzero denominator cancels on the right of fraction division. -/
theorem div_mul_cancel (a : Fraction R) {b : Fraction R} (hb : b ≠ 0) :
    a / b * b = a := by
  rw [div_eq_mul_inv, mul_assoc, mul_comm b⁻¹ b, mul_inv_cancel hb, mul_one]

/-- Fraction division satisfies the exact-division law. -/
instance : ExactDivLaws (Fraction R) where
  mul_div_cancel_right a b hb := by
    rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel hb, mul_one]

/-- The quotient construction is a field in the lightweight Grind hierarchy. -/
instance : Lean.Grind.Field (Fraction R) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact div_eq_mul_inv
  · exact zero_ne_one
  · exact inv_zero
  · exact mul_inv_cancel
  · intro a
    change natPow a 0 = 1
    rw [natPow]
  · intro a n
    change natPow a (n + 1) = natPow a n * a
    rw [natPow]
  · intro a n
    cases n with
    | ofNat m =>
        cases m with
        | zero =>
            change intPow a (-Int.ofNat 0) = (intPow a (Int.ofNat 0))⁻¹
            rw [show -Int.ofNat 0 = Int.ofNat 0 by rfl]
            change (1 : Fraction R) = 1⁻¹
            exact inv_one.symm
        | succ m => rfl
    | negSucc m =>
        simp only [Int.neg_negSucc]
        change a ^ (m + 1) = ((a ^ (m + 1))⁻¹)⁻¹
        exact (inv_inv _).symm

omit [DecidableEq R] in
/-- The coefficient embedding preserves natural powers. -/
@[simp]
theorem ofCoeff_pow (a : R) (n : Nat) : ofCoeff (a ^ n) = ofCoeff a ^ n := by
  induction n with
  | zero =>
      rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero]
      exact ofCoeff_one
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ,
        ofCoeff_mul, ih]

/-- Pull an exact scalar quotient back through the coefficient embedding.

The hypothesis that the fraction quotient lies in the image is the
integrality fact supplied by generalized subresultants. -/
theorem div_pullback {a b c : R} (hb : b ≠ 0)
    (h : ofCoeff c = ofCoeff a / ofCoeff b) : a / b = c := by
  have hb' : ofCoeff b ≠ (0 : Fraction R) := by
    intro hzero
    exact hb ((ofCoeff_eq_zero_iff b).mp hzero)
  have hmul := congrArg (fun x : Fraction R => x * ofCoeff b) h
  rw [div_mul_cancel _ hb', ← ofCoeff_mul] at hmul
  have hbase : c * b = a := ofCoeff_injective hmul
  rw [← hbase]
  exact ExactDivLaws.mul_div_cancel_right c b hb

/-- An integral fraction quotient reconstructs its numerator in the original
coefficient ring. -/
theorem div_exact {a b : R} (hb : b ≠ 0)
    (h : ∃ c : R, ofCoeff c = ofCoeff a / ofCoeff b) : a / b * b = a := by
  rcases h with ⟨c, hc⟩
  have hb' : ofCoeff b ≠ (0 : Fraction R) := by
    intro hzero
    exact hb ((ofCoeff_eq_zero_iff b).mp hzero)
  have hmul := congrArg (fun x : Fraction R => x * ofCoeff b) hc
  rw [div_mul_cancel _ hb', ← ofCoeff_mul] at hmul
  have hbase : c * b = a := ofCoeff_injective hmul
  rw [div_pullback hb hc, hbase]

/-- The total exact-division wrapper reconstructs a nonzero-denominator
numerator whenever its fraction quotient is integral. -/
theorem exactDiv_exact {a b : R} (hb : b ≠ 0)
    (h : ∃ c : R, ofCoeff c = ofCoeff a / ofCoeff b) :
    exactDiv a b * b = a := by
  rw [exactDiv_eq_div_of_ne a hb]
  exact div_exact hb h

/-- A Brown scalar quotient in the embedding image satisfies the exact scale
recurrence used by `BrownLaw`. -/
theorem divExp_exact (x y : R) (n : Nat)
    (hden : powNat y (n - 1) ≠ 0)
    (h : ∃ c : R,
      ofCoeff c =
        ofCoeff (powNat x n) / ofCoeff (powNat y (n - 1))) :
    powNat x n = powNat y (n - 1) * divExp x y n := by
  have hexact := exactDiv_exact hden h
  unfold divExp
  calc
    powNat x n = exactDiv (powNat x n) (powNat y (n - 1)) *
        powNat y (n - 1) := hexact.symm
    _ = powNat y (n - 1) *
        exactDiv (powNat x n) (powNat y (n - 1)) := by grind

/-! Compile-time checks for the concrete fraction-field instance graph. -/

private instance : NonzeroOne Int := ⟨by decide⟩

example : Lean.Grind.Field (Fraction Int) := inferInstance
example : ExactDivLaws (Fraction Int) := inferInstance
example : DecidableEq (Fraction Int) := inferInstance

end Fraction
end Hex
