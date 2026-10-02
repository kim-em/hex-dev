/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.CommonField
public import HexNumberFieldMathlib.PresentationSemantics
public import HexNumberFieldMathlib.IntegerRoots
public section

/-! Exact membership decisions and common primitive presentations. -/
namespace Hex.QAdjoin
open AlgebraicPoly.Common IntermediateField

/-- The total power-table wrapper is its successful checked computation. -/
theorem powerTable_eq (a : AlgebraicNumber) :
    powers? a (2 * a.p.natDegree - 2) = some (powerTable a) := by
  obtain ⟨powers, hp⟩ := Option.isSome_iff_exists.mp (powers?_isSome a (2 * a.p.natDegree - 2))
  simp [powerTable, hp]

/-- The shared table has the consecutive powers needed by the trace pairing. -/
theorem powerTable_spec (a : AlgebraicNumber) :
    (powerTable a).size = 2 * degree a - 1 ∧
      ∀ i (hi : i < (powerTable a).size), (powerTable a)[i].toComplex = a.toComplex ^ i := by
  obtain ⟨hs, hv⟩ := powers?_sound a _ (powerTable_eq a)
  refine ⟨?_, hv⟩
  have hd := a.pos_degree
  unfold degree
  omega

/-- Rational power-basis coordinates lie in the chosen simple extension. -/
theorem value_mem {a : AlgebraicNumber} (c : QAdjoin a) :
    PolyQuot.toComplex c a.rep a.rep_mk ∈ Rat⟮a.toComplex⟯ := by
  let K : IntermediateField Rat ℂ := Rat⟮a.toComplex⟯
  change (HexPolyMathlib.toPolynomial c.coeffs).eval₂ (algebraMap Rat ℂ) a.toComplex ∈ K
  induction HexPolyMathlib.toPolynomial c.coeffs using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add]
    exact K.add_mem hp hq
  | monomial n q =>
    rw [Polynomial.eval₂_monomial]
    exact K.mul_mem (K.algebraMap_mem q)
      (K.pow_mem (IntermediateField.mem_adjoin_simple_self Rat a.toComplex) n)

/-- Every coordinate value in a real-generated field is real. -/
theorem value_real {a : AlgebraicNumber} (c : QAdjoin a) (ha : a.isReal = true) :
    (PolyQuot.toComplex c a.rep a.rep_mk).im = 0 := by
  have hv : a.toComplex = (a.toComplex.re : ℂ) :=
    Complex.ext rfl (by simpa using (AlgebraicNumber.isReal_iff a).mp ha)
  change ((HexPolyMathlib.toPolynomial c.coeffs).eval₂ (algebraMap Rat ℂ) a.toComplex).im = 0
  induction HexPolyMathlib.toPolynomial c.coeffs using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
  | monomial n q =>
    rw [Polynomial.eval₂_monomial, hv, ← Complex.ofReal_pow]
    change ((q : ℂ) * ((a.toComplex.re ^ n : ℝ) : ℂ)).im = 0
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ratCast_im, mul_zero, zero_mul, add_zero]

/-- The real-field rejection skips work without changing coordinate recovery. -/
theorem ofAlgebraic?_eq (a b : AlgebraicNumber) :
    ofAlgebraic? a b = coordinates? a b (powerTable a) := by
  unfold ofAlgebraic?
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    cases hc : coordinates? a b (powerTable a) with
    | none => rfl
    | some c =>
      have hv := value_real c h.1
      rw [coordinates?_sound a b (powerTable a) hc] at hv
      have hb := (AlgebraicNumber.isReal_iff b).mpr hv
      simp_all
  · rfl

/-- Successful conversion recovers exactly the original canonical number. -/
theorem ofAlgebraic?_sound (a b : AlgebraicNumber) {c : QAdjoin a}
    (h : ofAlgebraic? a b = some c) : c.toAlgebraicNumber = b := by
  rw [ofAlgebraic?_eq] at h
  apply AlgebraicNumber.toComplex_injective
  exact (PolyQuot.toAlgebraicNumber_toComplex c a.rep a.rep_mk).trans
    (coordinates?_sound a b (powerTable a) h)

/-- Conversion succeeds exactly for elements of the chosen field. -/
theorem ofAlgebraic?_isSome_iff (a b : AlgebraicNumber) :
    (ofAlgebraic? a b).isSome = true ↔ b.toComplex ∈ Rat⟮a.toComplex⟯ := by
  rw [ofAlgebraic?_eq]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    rw [← coordinates?_sound a b (powerTable a) hc]
    exact value_mem c
  · intro h
    exact coordinates?_isSome a b (powerTable a) (powerTable_spec a).1
      (powerTable_spec a).2 h

@[simp] theorem ofAlgebraics?_size (a : AlgebraicNumber) (bs : Array AlgebraicNumber) :
    (ofAlgebraics? a bs).size = bs.size := by simp [ofAlgebraics?]

/-- Batch conversion preserves the single-value membership decision at each index. -/
@[simp] theorem ofAlgebraics?_get (a : AlgebraicNumber) (bs : Array AlgebraicNumber)
    (i : Nat) (hi : i < bs.size) :
    (ofAlgebraics? a bs)[i]'(by simpa using hi) = ofAlgebraic? a bs[i] := by
  simp [ofAlgebraics?, ofAlgebraic?]

private theorem checkPair?_sound (theta alpha gamma : AlgebraicNumber)
    (coordinates out : QAdjoin gamma × QAdjoin gamma)
    (h : checkPair? theta alpha gamma coordinates = some out) :
    out.1.toAlgebraicNumber = theta ∧ out.2.toAlgebraicNumber = alpha := by
  letI : ZPoly.CheckedIrreducible gamma.p := gamma.checked
  unfold checkPair? at h
  obtain ⟨thetaRecovered, htheta, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨alphaRecovered, halpha, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases heq : (thetaRecovered == theta && alphaRecovered == alpha) = true
  · simp only [heq, ↓reduceIte, Option.some.injEq] at h
    subst out
    have hthetaEq : thetaRecovered = theta :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp heq).1
    have halphaEq : alphaRecovered = alpha :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp heq).2
    constructor
    · apply AlgebraicNumber.toComplex_injective
      rw [← hthetaEq, QAdjoin.toAlgebraicNumber]
      exact (PolyQuot.toAlgebraicNumber_toComplex _ gamma.rep gamma.rep_mk).trans
        (PolyQuot.toAlgebraicNumber?_sound coordinates.1 gamma.rep gamma.rep_mk
          htheta).symm
    · apply AlgebraicNumber.toComplex_injective
      rw [← halphaEq, QAdjoin.toAlgebraicNumber]
      exact (PolyQuot.toAlgebraicNumber_toComplex _ gamma.rep gamma.rep_mk).trans
        (PolyQuot.toAlgebraicNumber?_sound coordinates.2 gamma.rep gamma.rep_mk
          halpha).symm
  · have hfalse : (thetaRecovered == theta && alphaRecovered == alpha) = false :=
      Bool.eq_false_of_not_eq_true heq
    simp [hfalse] at h

/-- A successful shift conversion preserves both selected algebraic values. -/
theorem recoverShift?_sound (theta alpha gamma : AlgebraicNumber)
    (shift : Int) {coordinates : QAdjoin gamma × QAdjoin gamma}
    (h : recoverShift? theta alpha gamma shift = some coordinates) :
    coordinates.1.toAlgebraicNumber = theta ∧
      coordinates.2.toAlgebraicNumber = alpha := by
  unfold recoverShift? at h
  by_cases hshift : shift = 0
  · simp [hshift] at h
  · simp only [hshift, ↓reduceIte] at h
    letI : ZPoly.CheckedIrreducible gamma.p := gamma.checked
    let generator : QAdjoin gamma := gamma.toQAdjoin
    let affine : DensePoly (QAdjoin gamma) :=
      DensePoly.ofList [generator, (-(shift : Rat)) • (1 : QAdjoin gamma)]
    let thetaRelation := DensePoly.composeImpl
      (DensePoly.ofCoeffs <| theta.p.toArray.map fun (c : Int) =>
        (c : Rat) • (1 : QAdjoin gamma)) affine
    let alphaRelation : DensePoly (QAdjoin gamma) :=
      DensePoly.ofCoeffs <| alpha.p.toArray.map fun (c : Int) =>
        (c : Rat) • (1 : QAdjoin gamma)
    let common := DensePoly.gcd thetaRelation alphaRelation
    by_cases hlinear : (common.natDegree = 1 && common.leadingCoeff != 0) = true
    · dsimp [common, thetaRelation, alphaRelation, affine, generator] at hlinear
      simp only [hlinear, ↓reduceIte] at h
      exact checkPair?_sound theta alpha gamma _ coordinates h
    · have hfalse :
          (common.natDegree = 1 && common.leadingCoeff != 0) = false :=
        Bool.eq_false_of_not_eq_true hlinear
      dsimp [common, thetaRelation, alphaRelation, affine, generator] at hfalse
      simp [hfalse] at h

private theorem presentShift?_sound (theta alpha gamma : AlgebraicNumber)
    (shift : Int) {p : Presentation}
    (h : presentShift? theta alpha gamma shift = some p) :
    p.entries.size = 2 ∧
      (∀ hzero : 0 < p.entries.size, (p.entries[0]'hzero).toAlgebraicNumber = theta) ∧
      (∀ hone : 1 < p.entries.size, (p.entries[1]'hone).toAlgebraicNumber = alpha) := by
  unfold presentShift? at h
  obtain ⟨coordinates, hcoordinates, h⟩ := Option.bind_eq_some_iff.mp h
  have hp : p = ⟨gamma, #[coordinates.1, coordinates.2]⟩ :=
    (Option.some.inj h).symm
  subst p
  obtain ⟨htheta, halpha⟩ :=
    recoverShift?_sound theta alpha gamma shift hcoordinates
  simp [htheta, halpha]

private theorem fastPair?_sound (theta alpha : AlgebraicNumber)
    {p : Presentation} (h : fastPair? theta alpha = some p) :
    p.entries.size = 2 ∧
      (∀ hzero : 0 < p.entries.size, (p.entries[0]'hzero).toAlgebraicNumber = theta) ∧
      (∀ hone : 1 < p.entries.size, (p.entries[1]'hone).toAlgebraicNumber = alpha) := by
  unfold fastPair? at h
  obtain ⟨gamma, _, hp⟩ := Option.bind_eq_some_iff.mp h
  by_cases hdegree : gamma.p.natDegree = theta.p.natDegree * alpha.p.natDegree
  · simp only [hdegree, ↓reduceIte] at hp
    exact presentShift?_sound theta alpha gamma 1 hp
  · simp [hdegree] at hp

private theorem presentation_exists (bs : Array AlgebraicNumber)
    (h : bs.all (fun b => b.isZero) ≠ true) :
    ∃ p, presentation? bs = some p := by
  apply Option.isSome_iff_exists.mp
  apply presentation?_isSome
  have hn : ¬ ∀ b ∈ bs, b.isZero = true := fun hall => h (Array.all_eq_true'.mpr hall)
  push Not at hn
  obtain ⟨b, hb, hz⟩ := hn
  exact ⟨b, Array.mem_toList_iff.mpr hb, Bool.eq_false_iff.mpr hz⟩

private theorem commonFallback_spec (bs : Array AlgebraicNumber)
    (hz : bs.all (fun b => b.isZero) ≠ true) :
    (commonFallback bs).entries.size = bs.size ∧
      ∀ i (hi : i < bs.size) (hp : i < (commonFallback bs).entries.size),
        (commonFallback bs).entries[i].toAlgebraicNumber = bs[i] := by
  obtain ⟨p, hp⟩ := presentation_exists bs hz
  have hs := presentation?_sound bs hp
  unfold commonFallback
  rw [hp]
  refine ⟨hs.1, ?_⟩
  intro i hi hpi
  apply AlgebraicNumber.toComplex_injective
  exact (PolyQuot.toAlgebraicNumber_toComplex _ p.generator.rep p.generator.rep_mk).trans
    (hs.2 i hi hpi)

/-- The common presentation preserves length and every input value. -/
theorem common_spec (bs : Array AlgebraicNumber) :
    (common bs).entries.size = bs.size ∧
      ∀ i (hi : i < bs.size) (hp : i < (common bs).entries.size),
        (common bs).entries[i].toAlgebraicNumber = bs[i] := by
  by_cases hz : bs.all (fun b => b.isZero) = true
  · unfold common
    rw [ite_eq_left hz]
    refine ⟨by simp, ?_⟩
    intro i hi hp
    apply AlgebraicNumber.toComplex_injective
    rw [QAdjoin.toAlgebraicNumber, PolyQuot.toAlgebraicNumber_toComplex]
    simp only [Array.getElem_map, PolyQuot.map_zero]
    have hall : ∀ b ∈ bs, b.isZero = true := by simpa only [Array.all_eq_true'] using hz
    exact ((AlgebraicNumber.isZero_iff bs[i]).mp (hall _ (Array.getElem_mem hi))).symm
  · by_cases hsize : bs.size = 2
    · cases hfast : fastPair? bs[0]! bs[1]! with
      | none =>
          unfold common
          rw [ite_eq_right hz, ite_eq_left hsize, hfast]
          exact commonFallback_spec bs hz
      | some p =>
          have hs := fastPair?_sound bs[0]! bs[1]! hfast
          have hcommon : common bs = p := by
            unfold common
            rw [ite_eq_right hz, ite_eq_left hsize, hfast]
          rw [hcommon]
          refine ⟨by omega, ?_⟩
          intro i hi hpi
          have hi' : i = 0 ∨ i = 1 := by omega
          rcases hi' with rfl | rfl
          · simpa [getElem!_pos bs 0 (by omega)] using hs.2.1 hpi
          · simpa [getElem!_pos bs 1 (by omega)] using hs.2.2 hpi
    · unfold common
      rw [ite_eq_right hz, ite_eq_right hsize]
      exact commonFallback_spec bs hz

@[simp] theorem common_size (bs : Array AlgebraicNumber) :
    (common bs).entries.size = bs.size := (common_spec bs).1

/-- Each common-field coordinate converts back to its original input. -/
theorem common_get (bs : Array AlgebraicNumber) (i : Nat) (hi : i < bs.size) :
    ((common bs).entries[i]'(by simpa using hi)).toAlgebraicNumber = bs[i] :=
  (common_spec bs).2 i hi _

end Hex.QAdjoin
