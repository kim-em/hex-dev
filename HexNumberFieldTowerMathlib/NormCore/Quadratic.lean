/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.NormCore.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

public section

namespace Hex.NumberTower.Norm

open Polynomial

/-- The quadratic norm identity, with formal degrees so the linear
coefficient may vanish. -/
theorem quadratic_resultant (a b p q : ℂ) :
    resultant (X ^ 2 + C b * X + C a) (C p + C q * X) 2 1 =
      p * p - b * p * q + a * q * q := by
  simp [resultant, Matrix.det_fin_three, sylvester, Matrix.of_apply,
    Fin.addCases, Set.mem_Icc, coeff_X]
  ring_nf
  simp

/-- Replacing a polynomial by a linear expression with the same values on
the roots of a monic quadratic preserves its resultant, including repeated
roots and a vanishing linear coefficient. -/
theorem quadratic_congr (a b p q : ℂ) (g : Polynomial ℂ) (n : Nat)
    (hn : g.natDegree ≤ n)
    (heval : ∀ z : ℂ, z * z + b * z + a = 0 → g.eval z = p + q * z) :
    resultant (X ^ 2 + C b * X + C a) g 2 n =
      p * p - b * p * q + a * q * q := by
  let f : Polynomial ℂ := X ^ 2 + C b * X + C a
  let h : Polynomial ℂ := C p + C q * X
  have hf : IsMonicOfDegree f 2 := isMonicOfDegree_add_add_two b a
  have hh : h.natDegree ≤ 1 := by
    simpa [h, add_comm] using (natDegree_linear_le (a := q) (b := p))
  have hprod : (f.roots.map g.eval).prod = (f.roots.map h.eval).prod := by
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    have hz' := (mem_roots hf.monic.ne_zero).mp hz
    have hroot : z * z + b * z + a = 0 := by
      simpa [f, IsRoot, pow_two] using hz'
    simpa [h] using heval z hroot
  calc
    resultant f g 2 n = (f.roots.map g.eval).prod := by
      simpa [hf.natDegree_eq, hf.leadingCoeff_eq] using
        resultant_eq_prod_eval f g n hn (IsAlgClosed.splits f)
    _ = (f.roots.map h.eval).prod := hprod
    _ = resultant f h 2 1 := by
      symm
      simpa [hf.natDegree_eq, hf.leadingCoeff_eq] using
        resultant_eq_prod_eval f h 1 hh (IsAlgClosed.splits f)
    _ = p * p - b * p * q + a * q * q := quadratic_resultant a b p q

noncomputable section

variable {R : Type*} [CommRing R] [DecidableEq R]

local instance : CommRing (DensePoly R) := denseCommRing

private theorem poly_pair (a b : R) :
    HexPolyMathlib.toPolynomial (DensePoly.ofCoeffs #[a, b]) = C a + X * C b := by
  simp [Finset.sum_range_succ, Array.getD]

private theorem poly_three (a b : R) :
    HexPolyMathlib.toPolynomial (DensePoly.ofCoeffs #[a, b, 1]) =
      X ^ 2 + C b * X + C a := by
  simp [Finset.sum_range_succ, Array.getD]
  ring

private theorem map_scale (φ : DensePoly R →+* ℂ) (k : R) (p : DensePoly R) :
    φ (DensePoly.scale k p) = φ (DensePoly.C k) * φ p := by
  have heq : DensePoly.scale k p = DensePoly.C k * p := by
    apply (HexPolyMathlib.equiv (R := R)).injective
    simp
  rw [heq, map_mul]

private theorem map_shift (φ : DensePoly R →+* ℂ) (p : DensePoly R) :
    φ (DensePoly.shift 1 p) = φ (DensePoly.monomial 1 1) * φ p := by
  have heq : DensePoly.shift 1 p = DensePoly.monomial 1 1 * p := by
    apply (HexPolyMathlib.equiv (R := R)).injective
    change HexPolyMathlib.toPolynomial (DensePoly.shift 1 p) =
      HexPolyMathlib.toPolynomial (DensePoly.monomial 1 1 * p)
    rw [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_monomial,
      monomial_one_one_eq_X]
    ext n
    cases n <;> simp [HexPolyMathlib.coeff_toPolynomial]
    rfl
  rw [heq, map_mul]

private theorem horner_eval {ι : Type*} (u v : ι → R) (a b c : R)
    (φ : DensePoly R →+* ℂ) (z : ℂ)
    (hroot : z * z + φ (DensePoly.C b) * z + φ (DensePoly.C a) = 0)
    (items : List ι) :
    let scale (k : R) (p : DensePoly R) := if k = 0 then 0 else DensePoly.scale k p
    let parts := items.foldr (fun i (p, q) =>
      (DensePoly.shift 1 p + scale (c * a) q + DensePoly.C (u i),
       DensePoly.shift 1 q - scale c p + scale (c * b) q + DensePoly.C (v i))) (0, 0)
    let outer := items.foldr (fun i value =>
      DensePoly.ofCoeffs #[DensePoly.C (u i), DensePoly.C (v i)] +
        DensePoly.ofCoeffs #[DensePoly.monomial 1 1, DensePoly.C (-c)] * value) 0
    ((HexPolyMathlib.toPolynomial outer).map φ).eval z = φ parts.1 + z * φ parts.2 := by
  let : CommRing (DensePoly (DensePoly R)) := denseCommRing
  let scale (k : R) (p : DensePoly R) := if k = 0 then 0 else DensePoly.scale k p
  let step (i : ι) (p q : DensePoly R) :=
    (DensePoly.shift 1 p + scale (c * a) q + DensePoly.C (u i),
     DensePoly.shift 1 q - scale c p + scale (c * b) q + DensePoly.C (v i))
  let lift (i : ι) := DensePoly.ofCoeffs #[DensePoly.C (u i), DensePoly.C (v i)]
  let base : DensePoly (DensePoly R) :=
    DensePoly.ofCoeffs #[DensePoly.monomial 1 1, DensePoly.C (-c)]
  let χ : R →+* ℂ := (φ.comp (HexPolyMathlib.equiv (R := R)).symm.toRingHom).comp C
  have hχ (k : R) : χ k = φ (DensePoly.C k) := by simp [χ]
  let ψ : DensePoly (DensePoly R) →+* ℂ := (evalRingHom z).comp
    ((mapRingHom φ).comp (HexPolyMathlib.equiv (R := DensePoly R)).toRingHom)
  have hadd (g h : DensePoly (DensePoly R)) : ψ (g + h) = ψ g + ψ h := by
    change ((HexPolyMathlib.toPolynomial (g + h)).map φ).eval z =
      ((HexPolyMathlib.toPolynomial g).map φ).eval z +
        ((HexPolyMathlib.toPolynomial h).map φ).eval z
    simp
  have hmul (g h : DensePoly (DensePoly R)) : ψ (g * h) = ψ g * ψ h := by
    change ((HexPolyMathlib.toPolynomial (g * h)).map φ).eval z =
      ((HexPolyMathlib.toPolynomial g).map φ).eval z *
        ((HexPolyMathlib.toPolynomial h).map φ).eval z
    simp
  have hlift (i : ι) : ψ (lift i) = χ (u i) + z * χ (v i) := by
    change ((HexPolyMathlib.toPolynomial (lift i)).map φ).eval z = _
    rw [poly_pair]
    simp [← hχ]
    ring
  have hbase : ψ base = φ (DensePoly.monomial 1 1) - χ c * z := by
    change ((HexPolyMathlib.toPolynomial base).map φ).eval z = _
    rw [poly_pair]
    simp [← hχ]
    ring
  have hscale (k : R) (p : DensePoly R) : φ (scale k p) = χ k * φ p := by
    dsimp only [scale]
    split
    · rename_i hk
      subst k
      simp
    · rw [map_scale, hχ]
  have hroot' : z * z + χ b * z + χ a = 0 := by simpa only [hχ] using hroot
  have hfold : ∀ items : List ι,
      ψ (items.foldr (fun i value => lift i + base * value) 0) =
        φ (items.foldr (fun i (p, q) => step i p q) (0, 0)).1 +
          z * φ (items.foldr (fun i (p, q) => step i p q) (0, 0)).2 := by
    intro items
    induction items with
    | nil => simp
    | cons i items ih =>
        rcases hparts : items.foldr (fun i (p, q) => step i p q) (0, 0) with ⟨p, q⟩
        simp only [hparts] at ih
        simp only [List.foldr_cons, hparts, step, hadd, hmul, map_add, map_sub, map_mul,
          hlift, hbase, ih, map_shift, hscale, ← hχ]
        linear_combination -(χ c) * φ q * hroot'
  exact hfold items

end

noncomputable section

variable {R : Type*} [Field R] [DecidableEq R]

local instance : CommRing (DensePoly R) := denseCommRing

private theorem quadratic_image {ι : Type*} (u v : ι → R) (a b c : R)
    (φ : DensePoly R →+* ℂ) (items : List ι) :
    let scale (k : R) (p : DensePoly R) := if k = 0 then 0 else DensePoly.scale k p
    let parts := items.foldr (fun i (p, q) =>
      (DensePoly.shift 1 p + scale (c * a) q + DensePoly.C (u i),
       DensePoly.shift 1 q - scale c p + scale (c * b) q + DensePoly.C (v i))) (0, 0)
    let outer := items.foldr (fun i value =>
      DensePoly.ofCoeffs #[DensePoly.C (u i), DensePoly.C (v i)] +
        DensePoly.ofCoeffs #[DensePoly.monomial 1 1, DensePoly.C (-c)] * value) 0
    φ (DensePoly.resultant (DensePoly.ofCoeffs #[DensePoly.C a, DensePoly.C b, 1]) outer) =
      φ (parts.1 * parts.1 - parts.1 * scale b parts.2 + parts.2 * scale a parts.2) := by
  let : IsDomain (DensePoly R) :=
    (HexPolyMathlib.equiv (R := R)).toMulEquiv.isDomain (Polynomial R)
  let scale (k : R) (p : DensePoly R) := if k = 0 then 0 else DensePoly.scale k p
  let parts := items.foldr (fun i (p, q) =>
    (DensePoly.shift 1 p + scale (c * a) q + DensePoly.C (u i),
     DensePoly.shift 1 q - scale c p + scale (c * b) q + DensePoly.C (v i))) (0, 0)
  let outer := items.foldr (fun i value =>
    DensePoly.ofCoeffs #[DensePoly.C (u i), DensePoly.C (v i)] +
      DensePoly.ofCoeffs #[DensePoly.monomial 1 1, DensePoly.C (-c)] * value) 0
  let m : DensePoly (DensePoly R) := DensePoly.ofCoeffs #[DensePoly.C a, DensePoly.C b, 1]
  change φ (DensePoly.resultant m outer) =
    φ (parts.1 * parts.1 - parts.1 * scale b parts.2 + parts.2 * scale a parts.2)
  have hm : HexPolyMathlib.toPolynomial m =
      X ^ 2 + C (DensePoly.C b) * X + C (DensePoly.C a) := poly_three _ _
  have hdegree : m.natDegree = 2 := by
    rw [← HexPolyMathlib.natDegree_toPolynomial, hm]
    exact (isMonicOfDegree_add_add_two (DensePoly.C b) (DensePoly.C a)).natDegree_eq
  have hmap : (HexPolyMathlib.toPolynomial m).map φ =
      X ^ 2 + C (φ (DensePoly.C b)) * X + C (φ (DensePoly.C a)) := by
    rw [hm]
    simp
  have houter : ((HexPolyMathlib.toPolynomial outer).map φ).natDegree ≤ outer.natDegree := by
    rw [← HexPolyMathlib.natDegree_toPolynomial]
    exact natDegree_map_le
  have hpoints (z : ℂ)
      (hz : z * z + φ (DensePoly.C b) * z + φ (DensePoly.C a) = 0) :
      ((HexPolyMathlib.toPolynomial outer).map φ).eval z = φ parts.1 + φ parts.2 * z := by
    have hpoint : ((HexPolyMathlib.toPolynomial outer).map φ).eval z =
        φ parts.1 + z * φ parts.2 := horner_eval u v a b c φ z hz items
    simpa only [mul_comm] using hpoint
  have hscale (k : R) (p : DensePoly R) :
      φ (scale k p) = φ (DensePoly.C k) * φ p := by
    dsimp only [scale]
    split
    · rename_i hk
      subst k
      have hzero : DensePoly.C (0 : R) = (0 : DensePoly R) := by
        apply (HexPolyMathlib.equiv (R := R)).injective
        simp
      simp [hzero]
    · exact map_scale φ k p
  rw [DensePoly.toPolynomial_resultant, ← resultant_map_map, hdegree, hmap]
  rw [quadratic_congr _ _ _ _ _ _ houter hpoints]
  simp only [map_add, map_sub, map_mul, hscale]
  ring

end

open Arithmetic

/-- The bounded quadratic computation returns exactly the encoded resultant.
Only the lower tower must be a field; the top quadratic may have repeated
roots or a nonzero linear coefficient. -/
theorem quadratic_eq_resultant (level : Level) (lower : List Level)
    (hdegree : level.degree = 2) (hlower : LevelsValid lower)
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ = (LevelSemantics.coeffDenote lower a)⁻¹)
    (f : Array (Array Rat)) (c : Int) :
    quadratic level lower f c =
      (DensePoly.resultant (definingOuter level lower)
        (shiftedOuter level lower f c)).toArray.map Coeff.data := by
  let : Field (Coeff lower) := coeffFieldPoly lower hlower hinjective hinv
  let : CommRing (DensePoly (Coeff lower)) := denseCommRing
  let a := Coeff.ofData lower (level.defining.getD 0 #[])
  let b := Coeff.ofData lower (level.defining.getD 1 #[])
  let shift := Coeff.ofData lower #[(c : Rat)]
  let u (coefficient : Array Rat) := Coeff.ofData lower (block coefficient 0 (levelsDim lower))
  let v (coefficient : Array Rat) := Coeff.ofData lower (block coefficient 1 (levelsDim lower))
  let scale (k : Coeff lower) (p : DensePoly (Coeff lower)) :=
    if k = 0 then 0 else DensePoly.scale k p
  let parts := f.toList.foldr (fun coefficient (p, q) =>
    (DensePoly.shift 1 p + scale (shift * a) q + DensePoly.C (u coefficient),
     DensePoly.shift 1 q - scale shift p + scale (shift * b) q + DensePoly.C (v coefficient))) (0, 0)
  have hone : DensePoly.C (1 : Coeff lower) = (1 : DensePoly (Coeff lower)) := by
    apply (HexPolyMathlib.equiv (R := Coeff lower)).injective
    simp
  have hm : definingOuter level lower =
      DensePoly.ofCoeffs #[DensePoly.C a, DensePoly.C b, 1] := by
    simp only [definingOuter, hdegree]
    change DensePoly.ofCoeffs #[DensePoly.C a, DensePoly.C b, DensePoly.C 1] = _
    rw [hone]
  have hlift (coefficient : Array Rat) : liftCoefficient level lower coefficient =
      DensePoly.ofCoeffs #[DensePoly.C (u coefficient), DensePoly.C (v coefficient)] := by
    simp only [liftCoefficient, hdegree]
    rfl
  have hneg : Coeff.ofData lower #[(-(c : Rat))] = -shift := by
    apply (LevelSemantics.coeffHom lower hlower hinjective hinv).injective
    change LevelSemantics.coeffDenote lower (Coeff.ofData lower #[(-(c : Rat))]) =
      LevelSemantics.coeffDenote lower (-shift)
    rw [LevelSemantics.coeffDenote_neg]
    simp [shift, LevelSemantics.coeffDenote, Coeff.ofData,
      LevelSemantics.denote_fixed, LevelSemantics.denote_rat lower hlower]
  have hshift : shiftedOuter level lower f c = f.toList.foldr (fun coefficient value =>
      DensePoly.ofCoeffs #[DensePoly.C (u coefficient), DensePoly.C (v coefficient)] +
        DensePoly.ofCoeffs #[DensePoly.monomial 1 1, DensePoly.C (-shift)] * value) 0 := by
    simp only [shiftedOuter, ← Array.foldr_toList, hlift, hneg]
  have hnorm : DensePoly.resultant (definingOuter level lower) (shiftedOuter level lower f c) =
      parts.1 * parts.1 - parts.1 * scale b parts.2 + parts.2 * scale a parts.2 := by
    apply rawPolynomial_injective lower hlower hinjective hinv
    apply Polynomial.funext
    intro x
    let φ : DensePoly (Coeff lower) →+* ℂ :=
      (evalRingHom x).comp (rawPolynomialHom lower hlower hinjective hinv)
    have hφ (p : DensePoly (Coeff lower)) : φ p = (rawPolynomial lower p).eval x := by
      change (rawPolynomialHom lower hlower hinjective hinv p).eval x = _
      rw [rawPolynomialHom_apply]
    rw [← hφ, ← hφ, hm, hshift]
    exact quadratic_image u v a b shift φ f.toList
  unfold quadratic
  simp only [← Array.foldr_toList]
  change (let (p, q) := parts;
    (p * p - p * scale b q + q * scale a q).toArray.map Coeff.data) = _
  rcases hparts : parts with ⟨p, q⟩
  simp only [hparts] at hnorm
  exact congrArg (fun p : DensePoly (Coeff lower) => p.toArray.map Coeff.data) hnorm.symm

/-- The quadratic dispatch and the general fallback compute the same
encoded one-level resultant over every validated lower tower. -/
theorem oneLevel_eq (level : Level) (lower : List Level)
    (hlower : LevelsValid lower) (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ = (LevelSemantics.coeffDenote lower a)⁻¹)
    (f : Array (Array Rat)) (c : Int) :
    oneLevel level lower f c =
      (DensePoly.resultant (definingOuter level lower)
        (shiftedOuter level lower f c)).toArray.map Coeff.data := by
  unfold oneLevel
  split
  · exact quadratic_eq_resultant level lower ‹_› hlower hinjective hinv f c
  · rfl

end Hex.NumberTower.Norm
