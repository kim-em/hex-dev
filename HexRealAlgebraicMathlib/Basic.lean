/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Order
public import HexNumberFieldMathlib.Nearest

public section

/-! Reality closure and the injective interpretation in the real numbers. -/

namespace Hex.AlgebraicNumber

/-- A canonical real algebraic number equals the inclusion of its real part. -/
theorem ofReal_re (a : AlgebraicNumber) (ha : a.isReal = true) :
    (a.toComplex.re : ℂ) = a.toComplex := by
  apply Complex.ext
  · rfl
  · simpa using ((isReal_iff a).mp ha).symm

/-- Canonical zero is real. -/
@[simp] theorem zero_isReal : (0 : AlgebraicNumber).isReal = true := by
  rw [isReal_iff, zero_toComplex]
  rfl

/-- Canonical rational casts are real. -/
@[simp] theorem ofRat_isReal (q : Rat) : (ofRat q).isReal = true := by
  rw [isReal_iff, ofRat_toComplex]
  simp

/-- Canonical one is real. -/
@[simp] theorem one_isReal : (1 : AlgebraicNumber).isReal = true := ofRat_isReal 1

/-- Real inputs are closed under canonical negation. -/
theorem neg_isReal (a : AlgebraicNumber) (ha : a.isReal = true) :
    (-a).isReal = true := by
  rw [isReal_iff, neg_toComplex, Complex.neg_im, (isReal_iff a).mp ha, neg_zero]

/-- Real inputs are closed under canonical addition. -/
theorem add_isReal (a b : AlgebraicNumber) (ha : a.isReal = true) (hb : b.isReal = true) :
    (a + b).isReal = true := by
  rw [isReal_iff, add_toComplex, Complex.add_im,
    (isReal_iff a).mp ha, (isReal_iff b).mp hb, add_zero]

/-- Real inputs are closed under canonical subtraction. -/
theorem sub_isReal (a b : AlgebraicNumber) (ha : a.isReal = true) (hb : b.isReal = true) :
    (a - b).isReal = true := by
  rw [isReal_iff, sub_toComplex, Complex.sub_im,
    (isReal_iff a).mp ha, (isReal_iff b).mp hb, sub_zero]

/-- Real inputs are closed under canonical multiplication. -/
theorem mul_isReal (a b : AlgebraicNumber) (ha : a.isReal = true) (hb : b.isReal = true) :
    (a * b).isReal = true := by
  rw [isReal_iff, mul_toComplex, ← ofReal_re a ha, ← ofReal_re b hb,
    ← Complex.ofReal_mul]
  rfl

/-- Canonical inversion preserves reality, including at zero. -/
theorem inv_isReal (a : AlgebraicNumber) (ha : a.isReal = true) :
    a⁻¹.isReal = true := by
  rw [isReal_iff, inv_toComplex, ← ofReal_re a ha, ← Complex.ofReal_inv]
  rfl

/-- Canonical division preserves reality, including zero denominators. -/
theorem div_isReal (a b : AlgebraicNumber) (ha : a.isReal = true) (hb : b.isReal = true) :
    (a / b).isReal = true := by
  rw [isReal_iff, div_toComplex, ← ofReal_re a ha, ← ofReal_re b hb,
    ← Complex.ofReal_div]
  rfl

/-- Canonical natural powers preserve reality. -/
theorem natPow_isReal (a : AlgebraicNumber) (ha : a.isReal = true) (n : Nat) :
    (natPow a n).isReal = true := by
  rw [isReal_iff, natPow_toComplex, ← ofReal_re a ha, ← Complex.ofReal_pow]
  rfl

/-- Canonical integer powers preserve reality. -/
theorem intPow_isReal (a : AlgebraicNumber) (ha : a.isReal = true) (n : Int) :
    (intPow a n).isReal = true := by
  rw [isReal_iff, intPow_toComplex, ← ofReal_re a ha, ← Complex.ofReal_zpow]
  rfl

/-- Canonical rational scalar multiplication preserves reality. -/
theorem smul_isReal (q : Rat) (a : AlgebraicNumber) (ha : a.isReal = true) :
    (smul q a).isReal = true := mul_isReal _ _ (ofRat_isReal q) ha

end Hex.AlgebraicNumber

namespace Hex.RealAlgebraicNumber

/-- The real value of a canonical real algebraic number. -/
@[expose] noncomputable def toReal (a : RealAlgebraicNumber) : ℝ :=
  a.toAlgebraic.toComplex.re

/-- The real interpretation includes into the existing complex interpretation. -/
@[simp] theorem ofReal_toReal (a : RealAlgebraicNumber) :
    (a.toReal : ℂ) = a.toAlgebraic.toComplex :=
  AlgebraicNumber.ofReal_re _ a.property

/-- The real interpretation is injective. -/
theorem toReal_injective : Function.Injective toReal := by
  intro a b h
  apply ext
  apply AlgebraicNumber.toComplex_injective
  rw [← ofReal_toReal, ← ofReal_toReal, h]

/-- Boolean equality is structural equality on the subtype. -/
theorem beq_iff (a b : RealAlgebraicNumber) : (a == b) = true ↔ a = b := by
  change (a.toAlgebraic == b.toAlgebraic) = true ↔ _
  rw [beq_iff_eq]
  exact ⟨ext, congrArg toAlgebraic⟩

/-- Zero projects to canonical zero. -/
@[simp] theorem zero_toAlgebraic : (0 : RealAlgebraicNumber).toAlgebraic = 0 := rfl

/-- Rational construction passes its closure check. -/
@[simp] theorem ofRat_toAlgebraic (q : Rat) :
    (ofRat q).toAlgebraic = AlgebraicNumber.ofRat q :=
  pack_val _ (AlgebraicNumber.ofRat_isReal q)

/-- One projects to canonical one. -/
@[simp] theorem one_toAlgebraic : (1 : RealAlgebraicNumber).toAlgebraic = 1 :=
  ofRat_toAlgebraic 1

/-- Canonical add passes its closure check. -/
@[simp] theorem add_toAlgebraic (a b : RealAlgebraicNumber) :
    (a + b).toAlgebraic = a.toAlgebraic + b.toAlgebraic :=
  by
    dsimp only [HAdd.hAdd, instHAdd, instAdd, Add.add, add]
    apply pack_val
    exact AlgebraicNumber.add_isReal a.toAlgebraic b.toAlgebraic a.property b.property

/-- Canonical sub passes its closure check. -/
@[simp] theorem sub_toAlgebraic (a b : RealAlgebraicNumber) :
    (a - b).toAlgebraic = a.toAlgebraic - b.toAlgebraic :=
  by
    dsimp only [HSub.hSub, instHSub, instSub, Sub.sub, sub]
    apply pack_val
    exact AlgebraicNumber.sub_isReal a.toAlgebraic b.toAlgebraic a.property b.property

/-- Canonical mul passes its closure check. -/
@[simp] theorem mul_toAlgebraic (a b : RealAlgebraicNumber) :
    (a * b).toAlgebraic = a.toAlgebraic * b.toAlgebraic :=
  by
    dsimp only [HMul.hMul, instHMul, instMul, Mul.mul, mul]
    apply pack_val
    exact AlgebraicNumber.mul_isReal a.toAlgebraic b.toAlgebraic a.property b.property

/-- Canonical div passes its closure check. -/
@[simp] theorem div_toAlgebraic (a b : RealAlgebraicNumber) :
    (a / b).toAlgebraic = a.toAlgebraic / b.toAlgebraic :=
  by
    dsimp only [HDiv.hDiv, instHDiv, instDiv, Div.div, div]
    apply pack_val
    exact AlgebraicNumber.div_isReal a.toAlgebraic b.toAlgebraic a.property b.property

/-- Canonical neg passes its closure check. -/
@[simp] theorem neg_toAlgebraic (a : RealAlgebraicNumber) :
    (-a).toAlgebraic = -a.toAlgebraic := by
  dsimp only [Neg.neg, instNeg, neg]
  apply pack_val
  exact AlgebraicNumber.neg_isReal _ a.property

/-- Canonical inv passes its closure check. -/
@[simp] theorem inv_toAlgebraic (a : RealAlgebraicNumber) :
    (a⁻¹).toAlgebraic = a.toAlgebraic⁻¹ := by
  dsimp only [Inv.inv, instInv, inv]
  apply pack_val
  exact AlgebraicNumber.inv_isReal _ a.property

/-- Canonical nat powers pass their closure check. -/
@[simp] theorem natPow_toAlgebraic (a : RealAlgebraicNumber) (n : Nat) :
    (natPow a n).toAlgebraic = AlgebraicNumber.natPow a.toAlgebraic n :=
  pack_val _ (AlgebraicNumber.natPow_isReal _ a.property n)

/-- Canonical int powers pass their closure check. -/
@[simp] theorem intPow_toAlgebraic (a : RealAlgebraicNumber) (n : Int) :
    (intPow a n).toAlgebraic = AlgebraicNumber.intPow a.toAlgebraic n :=
  pack_val _ (AlgebraicNumber.intPow_isReal _ a.property n)

/-- Rational scalar multiplication passes its closure check. -/
@[simp] theorem smul_toAlgebraic (q : Rat) (a : RealAlgebraicNumber) :
    (smul q a).toAlgebraic = AlgebraicNumber.smul q a.toAlgebraic :=
  pack_val _ (AlgebraicNumber.smul_isReal q _ a.property)

/-- The real value of zero. -/
@[simp] theorem zero_toReal : (0 : RealAlgebraicNumber).toReal = 0 := by
  simp [toReal]

/-- The real value of a rational cast. -/
@[simp] theorem ofRat_toReal (q : Rat) : (ofRat q).toReal = q := by
  simp [toReal]

/-- The real value of one. -/
@[simp] theorem one_toReal : (1 : RealAlgebraicNumber).toReal = 1 := by
  simp [toReal]

/-- The real interpretation preserves add. -/
@[simp] theorem add_toReal (a b : RealAlgebraicNumber) :
    (a + b).toReal = a.toReal + b.toReal := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, add_toAlgebraic, Complex.ofReal_add,
    AlgebraicNumber.add_toComplex]

/-- The real interpretation preserves sub. -/
@[simp] theorem sub_toReal (a b : RealAlgebraicNumber) :
    (a - b).toReal = a.toReal - b.toReal := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, sub_toAlgebraic, Complex.ofReal_sub,
    AlgebraicNumber.sub_toComplex]

/-- The real interpretation preserves mul. -/
@[simp] theorem mul_toReal (a b : RealAlgebraicNumber) :
    (a * b).toReal = a.toReal * b.toReal := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, mul_toAlgebraic, Complex.ofReal_mul,
    AlgebraicNumber.mul_toComplex]

/-- The real interpretation preserves div. -/
@[simp] theorem div_toReal (a b : RealAlgebraicNumber) :
    (a / b).toReal = a.toReal / b.toReal := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, div_toAlgebraic, Complex.ofReal_div,
    AlgebraicNumber.div_toComplex]

/-- The real interpretation preserves neg. -/
@[simp] theorem neg_toReal (a : RealAlgebraicNumber) :
    (-a).toReal = -a.toReal := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, neg_toAlgebraic, Complex.ofReal_neg,
    AlgebraicNumber.neg_toComplex]

/-- The real interpretation preserves inv. -/
@[simp] theorem inv_toReal (a : RealAlgebraicNumber) :
    (a⁻¹).toReal = a.toReal⁻¹ := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, inv_toAlgebraic, Complex.ofReal_inv,
    AlgebraicNumber.inv_toComplex]

/-- The real interpretation preserves nat powers. -/
@[simp] theorem natPow_toReal (a : RealAlgebraicNumber) (n : Nat) :
    (natPow a n).toReal = a.toReal ^ n := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, natPow_toAlgebraic, Complex.ofReal_pow,
    AlgebraicNumber.natPow_toComplex]

/-- The real interpretation preserves int powers. -/
@[simp] theorem intPow_toReal (a : RealAlgebraicNumber) (n : Int) :
    (intPow a n).toReal = a.toReal ^ n := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, intPow_toAlgebraic, Complex.ofReal_zpow,
    AlgebraicNumber.intPow_toComplex]

/-- The real interpretation preserves rational scalar multiplication. -/
@[simp] theorem smul_toReal (q : Rat) (a : RealAlgebraicNumber) :
    (smul q a).toReal = (q : ℝ) * a.toReal := by
  apply Complex.ofReal_injective
  simp only [ofReal_toReal, smul_toAlgebraic, Complex.ofReal_mul,
    Complex.ofReal_ratCast]
  exact AlgebraicNumber.smul_toComplex q a.toAlgebraic

/-- The real interpretation preserves powers written with notation. -/
@[simp] theorem pow_toReal (a : RealAlgebraicNumber) (n : Nat) :
    (a ^ n).toReal = a.toReal ^ n := natPow_toReal a n

/-- The real interpretation preserves integer powers written with notation. -/
@[simp] theorem zpow_toReal (a : RealAlgebraicNumber) (n : Int) :
    (a ^ n).toReal = a.toReal ^ n := intPow_toReal a n

/-- The real interpretation preserves rational scalar notation. -/
@[simp] theorem qsmul_toReal (q : Rat) (a : RealAlgebraicNumber) :
    (q • a).toReal = (q : ℝ) * a.toReal := smul_toReal q a

/-- The real interpretation preserves natural scalar notation. -/
@[simp] theorem nsmul_toReal (n : Nat) (a : RealAlgebraicNumber) :
    (n • a).toReal = (n : ℝ) * a.toReal := by
  change (smul (n : Rat) a).toReal = _
  simpa only [Rat.cast_natCast] using smul_toReal (n : Rat) a

/-- The real interpretation preserves integer scalar notation. -/
@[simp] theorem zsmul_toReal (n : Int) (a : RealAlgebraicNumber) :
    (n • a).toReal = (n : ℝ) * a.toReal := by
  change (smul (n : Rat) a).toReal = _
  simpa only [Rat.cast_intCast] using smul_toReal (n : Rat) a

/-- Exact comparison agrees with comparison of real values. -/
theorem compare_eq (a b : RealAlgebraicNumber) :
    compare a b = Ord.compare a.toReal b.toReal :=
  AlgebraicNumber.realCompare_eq _ _ a.property b.property

/-- Strict order is the strict order on real values. -/
theorem lt_iff (a b : RealAlgebraicNumber) : a < b ↔ a.toReal < b.toReal := by
  change compare a b = .lt ↔ _
  rw [compare_eq, compare_lt_iff_lt]

/-- Non-strict order is the non-strict order on real values. -/
theorem le_iff (a b : RealAlgebraicNumber) : a ≤ b ↔ a.toReal ≤ b.toReal := by
  change compare a b ≠ .gt ↔ _
  simp only [compare_eq, ne_eq, compare_gt_iff_gt, not_lt]

end Hex.RealAlgebraicNumber
