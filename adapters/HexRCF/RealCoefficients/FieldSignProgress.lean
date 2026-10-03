/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexRootsMathlib.MahlerPrec
public import HexSturmMathlib.Soundness

public section

namespace Hex.RCF.RealCoefficients.Field
private theorem literal_unique (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (real : s.meetsRealAxis = true) (x : ℝ)
    (root : (LiteralSign.realPoly (ZPoly.toRatPoly p)).IsRoot x)
    (lower : (((s.re-s.radiusHi).toRat : Rat) : ℝ) ≤ x)
    (upper : x ≤ (((s.re+s.radiusHi).toRat : Rat) : ℝ)) :
    x = (literalRep p s hw hp).root.re := by
  let rep := literalRep p s hw hp
  have selected := literalRep_bounds p s hw hp
  have selectedReal : (rep.root.re : ℂ) = rep.root :=
    Complex.ext rfl (literalRep_real p s hw hp real).symm
  have complexPoly : (LiteralSign.realPoly (ZPoly.toRatPoly p)).map Complex.ofRealHom =
      HexRootsMathlib.toPolyℂ p := by
    ext i; simp [LiteralSign.realPoly, HexRootsMathlib.toPolyℂ]
  have complexRoot : (HexRootsMathlib.toPolyℂ p).IsRoot (x : ℂ) := by
    change (HexRootsMathlib.toPolyℂ p).eval (x : ℂ) = 0
    rw [← complexPoly]
    rw [show (x : ℂ) = Complex.ofRealHom x from rfl, Polynomial.eval_map_apply]
    rw [root]; rfl
  by_contra distinct
  have complexDistinct : rep.root ≠ (x : ℂ) := by
    intro same
    exact distinct (by simpa only [Complex.ofReal_re] using congrArg Complex.re same.symm)
  have margin : HexRootsMathlib.Dyadic.toReal s.radiusHi < ‖rep.root - (x : ℂ)‖ / 4 := by
    have scale : (2 : ℝ) ^ (-s.prec) ≤ (2 : ℝ) ^ (-(mahlerPrec p : Int)) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2); omega
    calc
      HexRootsMathlib.Dyadic.toReal s.radiusHi =
          (2 : ℝ) ^ (-s.prec) * (1449 / 1024 : ℝ) := by
        rw [HexRootsMathlib.DyadicSquare.radiusHi_eq, HexRootsMathlib.DyadicSquare.halfWidth_eq]
        norm_num [Hex.sqrt2Hi, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec]
      _ ≤ (2 : ℝ) ^ (-(mahlerPrec p : Int)) * (1449 / 1024 : ℝ) :=
        mul_le_mul_of_nonneg_right scale (by norm_num)
      _ < ‖rep.root - (x : ℂ)‖ / 4 := HexRootsMathlib.mahlerPrec_separates p
        (HexRootsMathlib.RefinedIsolation.poly_ne_zero rep) rep.root (x : ℂ)
        (HexRootsMathlib.RefinedIsolation.isRoot rep) complexRoot complexDistinct
  have loEq : (((s.re-s.radiusHi).toRat : Rat) : ℝ) =
      HexRootsMathlib.Dyadic.toReal s.re - HexRootsMathlib.Dyadic.toReal s.radiusHi := by
    rw [← HexRootsMathlib.Dyadic.toReal_sub]; rfl
  have hiEq : (((s.re+s.radiusHi).toRat : Rat) : ℝ) =
      HexRootsMathlib.Dyadic.toReal s.re + HexRootsMathlib.Dyadic.toReal s.radiusHi := by
    rw [← HexRootsMathlib.Dyadic.toReal_add]; rfl
  rw [loEq, hiEq] at selected
  rw [loEq] at lower
  rw [hiEq] at upper
  have distance : ‖rep.root - (x : ℂ)‖ < 2 * HexRootsMathlib.Dyadic.toReal s.radiusHi := by
    rw [← selectedReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply abs_lt.mpr
    constructor <;> linarith [selected.1, selected.2]
  linarith
/-- The checked selected real root lies in a root-free rational domain with
exactly one real root. The original literal square fixes that root; the
owner's Mahler separation law rules out every other root even at endpoints. -/
theorem literal_domain (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true) :
    HexSturmMathlib.Domain (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero)
      (ZPoly.toRatPoly p) (.finite (s.re - s.radiusHi).toRat)
      (.finite (s.re + s.radiusHi).toRat) ∧
    (HexRealRootsMathlib.Tarski.rootsIn (LiteralSign.realPoly (ZPoly.toRatPoly p))
      (.finite ((s.re - s.radiusHi).toRat : ℝ))
      (.finite ((s.re + s.radiusHi).toRat : ℝ))).card = 1 := by
  classical
  let polynomial := LiteralSign.realPoly (ZPoly.toRatPoly p)
  let lower : ℝ := (s.re - s.radiusHi).toRat
  let upper : ℝ := (s.re + s.radiusHi).toRat
  let value := (literalRep p s hw hp).root.re
  have bounds : lower < value ∧ value < upper := literalRep_bounds p s hw hp
  have selected : polynomial.IsRoot value := literalRep_root p s hw hp real
  have mapped : polynomial = (HexPolyZMathlib.toPolyℚ p).map (Rat.castHom ℝ) := by
    ext i
    simp [polynomial, LiteralSign.realPoly, HexPolyZMathlib.toPolyℚ]
  have squarefree : Squarefree polynomial := by
    rw [mapped]
    exact ((Polynomial.separable_map (Rat.castHom ℝ)).mpr
      (ZPoly.CheckedIrreducible.separable p)).squarefree
  have unique (x : ℝ) (root : polynomial.IsRoot x) (lo : lower ≤ x) (hi : x ≤ upper) :
      x = value := literal_unique p s hw hp real x root lo hi
  have lowerNe : polynomial.eval lower ≠ 0 := by
    intro root
    have same := unique lower root le_rfl (le_of_lt (bounds.1.trans bounds.2))
    linarith [bounds.1]
  have upperNe : polynomial.eval upper ≠ 0 := by
    intro root
    have same := unique upper root (le_of_lt (bounds.1.trans bounds.2)) le_rfl
    linarith [bounds.2]
  constructor
  · exact ⟨squarefree.ne_zero, squarefree, bounds.1.trans bounds.2, lowerNe, upperNe⟩
  · have roots : HexRealRootsMathlib.Tarski.rootsIn polynomial (.finite lower) (.finite upper) =
        {value} := by
      ext x
      rw [HexRealRootsMathlib.Tarski.mem_rootsIn_iff polynomial squarefree.ne_zero,
        HexRealRootsMathlib.Tarski.inInterval_finite, Finset.mem_singleton]
      constructor
      · rintro ⟨root, lo, hi⟩
        exact unique x root lo.le hi.le
      · intro same
        subst x
        exact ⟨selected, bounds⟩
    rw [roots]
    exact Finset.card_singleton value

/-- Search signs are rational Tarski queries at the same selected root,
without isolating each coordinate as a separate algebraic number.
The absent-domain fallback is unreachable for a checked real literal. -/
@[expose] def literalSign (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec) :
    PolyQuot p (SimpleRoot.ofSquare p s hw hp) → Int :=
  let prepared := Sturm.prepare Sturm.orderSign (ZPoly.toRatPoly p)
    (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat)
  fun a => match prepared with
    | some domain => Sturm.queryPrepared domain a.coeffs
    | none => 0

/-- Rational prepared search signs denote the selected embedding exactly. -/
theorem literalSign_spec (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    literalSign p s hw hp a =
      (SignType.sign (value (literalRep p s hw hp) a) : Int) := by
  classical
  let f : Rat → ℝ := fun r => (r : ℝ)
  have hz : ∀ a : Rat, f a = 0 ↔ a = 0 := fun _ => Rat.cast_eq_zero
  have h1 : f 1 = 1 := by norm_num [f]
  have ha : ∀ a b : Rat, f (a + b) = f a + f b := Rat.cast_add
  have hs : ∀ a b : Rat, f (a - b) = f a - f b := Rat.cast_sub
  have hm : ∀ a b : Rat, f (a * b) = f a * f b := Rat.cast_mul
  have hn : ∀ a : Rat, f (-a) = -f a := Rat.cast_neg
  have hi : ∀ a : Rat, f a⁻¹ = (f a)⁻¹ := Rat.cast_inv
  have hnat : ∀ n : Nat, f (n : Rat) = (n : ℝ) := by intro n; norm_num [f]
  have hsign : ∀ a : Rat, Sturm.orderSign a = (SignType.sign (f a) : Int) := by
    intro a
    rw [HexSturmMathlib.orderSign_eq]
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · have hr : (a : ℝ) < 0 := by exact_mod_cast hneg
      simp [sign_neg hneg, sign_neg hr, f]
    · subst a; simp [f]
    · have hr : (0 : ℝ) < a := by exact_mod_cast hpos
      simp [sign_pos hpos, sign_pos hr, f]
  have signs := HexSturmMathlib.sign_spec f Sturm.orderSign hsign
  obtain ⟨valid, card⟩ := literal_domain p s hw hp real
  have available := (HexSturmMathlib.prepare_isSome f hz ha hs hm
    Sturm.orderSign (fun a => (signs a).2.1) (fun a => (signs a).2.2.1)
    h1 hn hi hnat (fun a => (signs a).1) (ZPoly.toRatPoly p)
    (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat)).mpr valid
  cases prepared : Sturm.prepare Sturm.orderSign (ZPoly.toRatPoly p)
      (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat) with
  | none =>
    rw [prepared] at available
    contradiction
  | some domain =>
    obtain ⟨signEq, headEq, loEq, upperEq⟩ := Sturm.prepare_eq_some _ _ _ _ domain prepared
    have meaning := HexSturmMathlib.queryPrepared_sound f hz h1 ha hs hm hnat
      Sturm.orderSign hsign hn hi domain signEq a.coeffs
    simp only [headEq, loEq, upperEq, Endpoint.map] at meaning
    have mem := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ valid.1 _ _
      (literalRep p s hw hp).root.re).mpr
      ⟨literalRep_root p s hw hp real,
        (HexRealRootsMathlib.Tarski.inInterval_finite _ _ _).mpr
          (literalRep_bounds p s hw hp)⟩
    change (literalRep p s hw hp).root.re ∈
      HexRealRootsMathlib.Tarski.rootsIn (LiteralSign.realPoly (ZPoly.toRatPoly p))
        (.finite ((s.re - s.radiusHi).toRat : ℝ))
        (.finite ((s.re + s.radiusHi).toRat : ℝ)) at mem
    change Sturm.queryPrepared domain a.coeffs = HexRealRootsMathlib.Tarski.rootSum
      (LiteralSign.realPoly (ZPoly.toRatPoly p)) (LiteralSign.realPoly a.coeffs)
      (.finite ((s.re - s.radiusHi).toRat : ℝ))
      (.finite ((s.re + s.radiusHi).toRat : ℝ)) at meaning
    obtain ⟨x, roots⟩ := Finset.card_eq_one.mp card
    have same : (literalRep p s hw hp).root.re = x := by
      simpa only [roots, Finset.mem_singleton] using mem
    rw [HexRealRootsMathlib.Tarski.rootSum_singleton _ _ _ _ x roots, ← same] at meaning
    simpa only [literalSign, prepared, ← value_realPoly] using meaning

/-- Construct the prepared domain as data, so compiled callers can capture it
once in their sign closure. A function-valued definition alone is eta-expanded
by Lean and does not provide this caching guarantee. -/
def prepareSign (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true) :
    {domain : Sturm.PreparedDomain Rat //
      Sturm.prepare Sturm.orderSign (ZPoly.toRatPoly p)
        (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat) = some domain} := by
  have available : (Sturm.prepare Sturm.orderSign (ZPoly.toRatPoly p)
      (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat)).isSome = true := by
    have oneSign := literalSign_spec p s hw hp real
      (1 : PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    rw [value_one (literalRep p s hw hp) (literalRep_mk p s hw hp)
      (literalRep_real p s hw hp real)] at oneSign
    cases prepared : Sturm.prepare Sturm.orderSign (ZPoly.toRatPoly p)
        (.finite (s.re - s.radiusHi).toRat) (.finite (s.re + s.radiusHi).toRat) with
    | none => simp only [literalSign, prepared] at oneSign; norm_num at oneSign
    | some domain => rfl
  exact ⟨_, Option.eq_some_of_isSome available⟩

/-- A captured prepared sign domain gives the selected real sign. -/
theorem prepareSign_spec (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) :
    Sturm.queryPrepared (prepareSign p s hw hp real).val a.coeffs =
      (SignType.sign (value (literalRep p s hw hp) a) : Int) := by
  simpa only [literalSign, (prepareSign p s hw hp real).property] using
    literalSign_spec p s hw hp real a

end Hex.RCF.RealCoefficients.Field
