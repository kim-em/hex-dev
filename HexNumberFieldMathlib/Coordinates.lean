/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Primitive
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Trace.Basic

public section

/-!
# Trace coordinates for primitive presentations

Semantic invariants for the checked trace and coordinate-recovery routines.
-/

namespace Hex.AlgebraicPoly.Common

open Module IntermediateField

private theorem vector_mapM_isSome {n : Nat} {A B : Type*}
    (items : Vector A n) (f : A → Option B)
    (h : ∀ i : Fin n, (f (items.get i)).isSome) :
    (items.mapM f).isSome := by
  have harray : (items.toArray.mapM f).isSome := by
    apply HexRootsMathlib.array_mapM_isSome
    intro item hitem
    have hitem' : item ∈ items.toArray := by simpa using hitem
    rw [Array.mem_iff_getElem] at hitem'
    obtain ⟨i, hi, rfl⟩ := hitem'
    exact h ⟨i, by simpa using hi⟩
  rw [← Vector.toArray_mapM] at harray
  cases hmap : items.mapM f with
  | none => simp [hmap] at harray
  | some => simp

private theorem vector_mapM_some_get {n : Nat} {A B : Type*}
    {items : Vector A n} {f : A → Option B} {out : Vector B n}
    (hmap : items.mapM f = some out) (i : Fin n) :
    f (items.get i) = some (out.get i) := by
  have harray : items.toArray.mapM f = some out.toArray := by
    rw [← Vector.toArray_mapM, hmap]
    rfl
  have hi : i.val < items.toArray.size := by simp
  have ho : i.val < out.toArray.size := by simp
  exact (HexRootsMathlib.array_mapM_some_get harray).2 i hi ho

private theorem spanCoeffs_isSome_of_det_ne_zero {n : Nat}
    (M : Matrix Rat n n) (v : Vector Rat n)
    (hdet : (_root_.Matrix.det (HexMatrixMathlib.matrixEquiv M)) ≠ 0) :
    (Matrix.spanCoeffs M v).isSome := by
  let M' := HexMatrixMathlib.matrixEquiv M
  let v' := HexMatrixMathlib.vectorEquiv v
  let c' : Fin n → Rat := _root_.Matrix.vecMul v' M'⁻¹
  let c : Vector Rat n := HexMatrixMathlib.vectorEquiv.symm c'
  have hunit : IsUnit M'.det := isUnit_iff_ne_zero.mpr hdet
  have hmath : _root_.Matrix.vecMul c' M' = v' := by
    dsimp [c']
    rw [_root_.Matrix.vecMul_vecMul,
      _root_.Matrix.nonsing_inv_mul M' hunit,
      _root_.Matrix.vecMul_one]
  have hexec : Matrix.vecMul c M = v := by
    apply HexMatrixMathlib.vectorEquiv.injective
    rw [HexMatrixMathlib.vectorEquiv_vecMul]
    funext j
    simpa [c, M', v', Hex.Matrix.row, _root_.Matrix.vecMul, dotProduct,
      Fintype.linearCombination_apply] using congrFun hmath j
  cases hspan : Matrix.spanCoeffs M v with
  | none =>
      exact ((Matrix.spanCoeffs_eq_none_iff M v).mp hspan
        ⟨c, hexec⟩).elim
  | some => simp

private theorem vecMul_injective_of_det_ne_zero {n : Nat}
    (M : Matrix Rat n n)
    (hdet : (_root_.Matrix.det (HexMatrixMathlib.matrixEquiv M)) ≠ 0) :
    Function.Injective fun c : Vector Rat n ↦ Matrix.vecMul c M := by
  let M' := HexMatrixMathlib.matrixEquiv M
  have hunit : IsUnit M' := by
    rw [_root_.Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  have hinjective : Function.Injective M'.vecMul :=
    _root_.Matrix.vecMul_injective_iff_isUnit.mpr hunit
  intro a b hab
  apply HexMatrixMathlib.vectorEquiv.injective
  apply hinjective
  have hbridge (c : Vector Rat n) :
      HexMatrixMathlib.vectorEquiv (Matrix.vecMul c M) =
        M'.vecMul (HexMatrixMathlib.vectorEquiv c) := by
    rw [HexMatrixMathlib.vectorEquiv_vecMul]
    funext j
    simp [M', Hex.Matrix.row, _root_.Matrix.vecMul, dotProduct,
      Fintype.linearCombination_apply]
  exact (hbridge a).symm.trans <|
    (congrArg HexMatrixMathlib.vectorEquiv hab).trans (hbridge b)

/-- The next coefficient of the rational minimal polynomial is the normalized
next coefficient stored in the primitive integer polynomial. -/
private theorem minpoly_nextCoeff (a : AlgebraicNumber) :
    (minpoly Rat a.toComplex).nextCoeff =
      (a.p.leadingCoeff : Rat)⁻¹ * (a.p.coeff (degree a - 1) : Rat) := by
  rw [Polynomial.nextCoeff_of_natDegree_pos]
  · rw [← degree_eq_minpoly, ← AlgebraicNumber.p_eq_minpoly,
      Polynomial.coeff_smul, HexPolyZMathlib.coeff_toPolyℚ, smul_eq_mul]
  · rw [← degree_eq_minpoly]
    exact degree_pos a

/-- The degree of an algebraic number lying in a primitive field divides the
degree of that field. -/
theorem degree_dvd_of_mem (gamma a : AlgebraicNumber)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯) :
    degree a ∣ degree gamma := by
  let K : IntermediateField Rat ℂ := Rat⟮gamma.toComplex⟯
  let aK : K := ⟨a.toComplex, ha⟩
  let : FiniteDimensional Rat K :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_toComplex gamma)
  have hmin : minpoly Rat aK = minpoly Rat a.toComplex :=
    (minpoly.algHom_eq K.val K.val.injective aK).symm
  rw [degree_eq_minpoly a, ← hmin, degree_eq_minpoly gamma,
    ← IntermediateField.adjoin.finrank (isIntegral_toComplex gamma)]
  exact minpoly.degree_dvd (IsIntegral.of_finite Rat aK)

/-- Trace succeeds whenever the input belongs to the stated primitive field. -/
theorem trace?_isSome (gamma a : AlgebraicNumber)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯) :
    (trace? (degree gamma) a).isSome := by
  have hmod : degree gamma % degree a = 0 :=
    Nat.mod_eq_zero_of_dvd (degree_dvd_of_mem gamma a ha)
  simp [trace?, (degree_pos a).ne', hmod]

/-- A successful executable trace is the field trace from the primitive
ambient field. -/
theorem trace?_sound (gamma a : AlgebraicNumber)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯) {t : Rat}
    (h : trace? (degree gamma) a = some t) :
    t = Algebra.trace Rat Rat⟮gamma.toComplex⟯
      (⟨a.toComplex, ha⟩ : Rat⟮gamma.toComplex⟯) := by
  let K : IntermediateField Rat ℂ := Rat⟮gamma.toComplex⟯
  let aK : K := ⟨a.toComplex, ha⟩
  change t = Algebra.trace Rat K aK
  let : FiniteDimensional Rat K :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_toComplex gamma)
  have hmin : minpoly Rat aK = minpoly Rat a.toComplex :=
    (minpoly.algHom_eq K.val K.val.injective aK).symm
  have hm : degree a = Module.finrank Rat Rat⟮aK⟯ := by
    rw [degree_eq_minpoly a, ← hmin,
      IntermediateField.adjoin.finrank (IsIntegral.of_finite Rat aK)]
  have hd : degree gamma = Module.finrank Rat K := by
    rw [IntermediateField.adjoin.finrank (isIntegral_toComplex gamma),
      ← degree_eq_minpoly]
  have htower : degree a * Module.finrank Rat⟮aK⟯ K = degree gamma := by
    rw [hm, hd]
    exact Module.finrank_mul_finrank Rat Rat⟮aK⟯ K
  have hquot : degree gamma / degree a = Module.finrank Rat⟮aK⟯ K := by
    exact Nat.div_eq_of_eq_mul_left (degree_pos a) (by
      simpa [Nat.mul_comm] using htower.symm)
  have hmod : degree gamma % degree a = 0 := by
    rw [← htower]
    exact Nat.mul_mod_right _ _
  unfold trace? at h
  simp at h
  rw [← h.2]
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin,
    minpoly_nextCoeff, hquot]
  field_simp

private theorem traceGram_det_ne_zero (gamma : AlgebraicNumber)
    (powers : Array AlgebraicNumber) (powerTraces : Array Rat)
    (hsize : powers.size = 2 * degree gamma - 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (hmap : powers.mapM (trace? (degree gamma)) = some powerTraces) :
    (_root_.Matrix.det (HexMatrixMathlib.matrixEquiv
      (Matrix.ofFn fun i : Fin (degree gamma) =>
        fun j : Fin (degree gamma) => powerTraces[i.val + j.val]!))) ≠ 0 := by
  let K : IntermediateField Rat ℂ := Rat⟮gamma.toComplex⟯
  let : FiniteDimensional Rat K :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_toComplex gamma)
  let pb := IntermediateField.adjoin.powerBasis (isIntegral_toComplex gamma)
  have hpbdim : pb.dim = degree gamma := by
    change (minpoly Rat gamma.toComplex).natDegree = degree gamma
    exact (degree_eq_minpoly gamma).symm
  let basis : Basis (Fin (degree gamma)) Rat K :=
    pb.basis.reindex (finCongr hpbdim)
  have hbasis (i : Fin (degree gamma)) :
      basis i = (AdjoinSimple.gen Rat gamma.toComplex) ^ i.val := by
    simp [basis, pb]
  have hmatrix :
      HexMatrixMathlib.matrixEquiv
        (Matrix.ofFn fun i : Fin (degree gamma) =>
          fun j : Fin (degree gamma) => powerTraces[i.val + j.val]!) =
      (Algebra.traceForm Rat K).toMatrix basis := by
    ext i j
    rw [HexMatrixMathlib.matrixEquiv_ofFn,
      Algebra.traceForm_toMatrix, hbasis, hbasis]
    have hij : i.val + j.val < powers.size := by
      have hpos := degree_pos gamma
      omega
    have hmember : powers[i.val + j.val].toComplex ∈ K := by
      rw [hvalues (i.val + j.val) hij]
      exact K.pow_mem (IntermediateField.mem_adjoin_simple_self
        Rat gamma.toComplex) (i.val + j.val)
    have htraceBound : i.val + j.val < powerTraces.size := by
      rw [← (HexRootsMathlib.array_mapM_some_get hmap).1]
      exact hij
    have htrace := trace?_sound gamma powers[i.val + j.val] hmember
      ((HexRootsMathlib.array_mapM_some_get hmap).2
        (i.val + j.val) hij htraceBound)
    rw [getElem!_pos powerTraces (i.val + j.val) htraceBound]
    calc
      powerTraces[i.val + j.val] =
          Algebra.trace Rat K ⟨powers[i.val + j.val].toComplex, hmember⟩ :=
        htrace
      _ = Algebra.trace Rat K
          ((AdjoinSimple.gen Rat gamma.toComplex) ^ i.val *
            (AdjoinSimple.gen Rat gamma.toComplex) ^ j.val) := by
        apply congrArg (Algebra.trace Rat K)
        apply Subtype.ext
        simp [K, hvalues (i.val + j.val) hij, pow_add]
  rw [hmatrix]
  exact det_traceForm_ne_zero basis

private theorem coordinateProducts_get (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber)
    (hsize : powers.size = 2 * degree gamma - 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (products : Vector AlgebraicNumber (degree gamma))
    (hproducts :
      (⟨(List.range (degree gamma)).toArray, by simp⟩ :
          Vector Nat (degree gamma)).mapM
        (fun k => mul? a powers[k]!) = some products)
    (i : Fin (degree gamma)) :
    (products.get i).toComplex = a.toComplex * gamma.toComplex ^ i.val := by
  let indices : Vector Nat (degree gamma) :=
    ⟨(List.range (degree gamma)).toArray, by simp⟩
  have hibound : i.val < powers.size := by
    have hpos := degree_pos gamma
    omega
  have hiindex : indices.get i = i.val := by
    simp [indices]
  have hrun := vector_mapM_some_get (items := indices) hproducts i
  rw [hiindex] at hrun
  have hmul := mul?_sound a powers[i.val]! hrun
  rw [getElem!_pos powers i.val hibound,
    hvalues i.val hibound] at hmul
  exact hmul

private theorem coordinateRhs_get (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber)
    (hsize : powers.size = 2 * degree gamma - 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯)
    (products : Vector AlgebraicNumber (degree gamma))
    (hproducts :
      (⟨(List.range (degree gamma)).toArray, by simp⟩ :
          Vector Nat (degree gamma)).mapM
        (fun k => mul? a powers[k]!) = some products)
    (rhs : Vector Rat (degree gamma))
    (hrhs : products.mapM (trace? (degree gamma)) = some rhs)
    (i : Fin (degree gamma)) :
    rhs.get i = Algebra.trace Rat Rat⟮gamma.toComplex⟯
      (⟨a.toComplex * gamma.toComplex ^ i.val,
        (Rat⟮gamma.toComplex⟯ : IntermediateField Rat ℂ).mul_mem ha
          ((Rat⟮gamma.toComplex⟯ : IntermediateField Rat ℂ).pow_mem
            (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex)
            i.val)⟩ : Rat⟮gamma.toComplex⟯) := by
  let K : IntermediateField Rat ℂ := Rat⟮gamma.toComplex⟯
  have hproduct := coordinateProducts_get gamma a powers hsize hvalues
    products hproducts i
  have hproductMem : (products.get i).toComplex ∈ K := by
    rw [hproduct]
    exact K.mul_mem ha (K.pow_mem
      (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex) i.val)
  have hrun := vector_mapM_some_get hrhs i
  have htrace := trace?_sound gamma (products.get i) hproductMem hrun
  calc
    rhs.get i = Algebra.trace Rat K
        ⟨(products.get i).toComplex, hproductMem⟩ := htrace
    _ = Algebra.trace Rat K
        ⟨a.toComplex * gamma.toComplex ^ i.val,
          K.mul_mem ha (K.pow_mem
            (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex)
            i.val)⟩ := by
      apply congrArg (Algebra.trace Rat K)
      apply Subtype.ext
      exact hproduct

private theorem basisCoeffs_solve (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber) (powerTraces : Array Rat)
    (hsize : powers.size = 2 * degree gamma - 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯)
    (hpowerTraces :
      powers.mapM (trace? (degree gamma)) = some powerTraces)
    (products : Vector AlgebraicNumber (degree gamma))
    (hproducts :
      (⟨(List.range (degree gamma)).toArray, by simp⟩ :
          Vector Nat (degree gamma)).mapM
        (fun k => mul? a powers[k]!) = some products)
    (rhs : Vector Rat (degree gamma))
    (hrhs : products.mapM (trace? (degree gamma)) = some rhs) :
    ∃ c : Vector Rat (degree gamma),
      Matrix.vecMul c
          (Matrix.ofFn fun i : Fin (degree gamma) =>
            fun j : Fin (degree gamma) => powerTraces[i.val + j.val]!) = rhs ∧
      ∑ i : Fin (degree gamma), c.get i •
          (⟨gamma.toComplex ^ i.val,
            (Rat⟮gamma.toComplex⟯ : IntermediateField Rat ℂ).pow_mem
              (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex)
              i.val⟩ : Rat⟮gamma.toComplex⟯) =
        (⟨a.toComplex, ha⟩ : Rat⟮gamma.toComplex⟯) := by
  let K : IntermediateField Rat ℂ := Rat⟮gamma.toComplex⟯
  let : FiniteDimensional Rat K :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_toComplex gamma)
  let pb := IntermediateField.adjoin.powerBasis (isIntegral_toComplex gamma)
  have hpbdim : pb.dim = degree gamma := by
    change (minpoly Rat gamma.toComplex).natDegree = degree gamma
    exact (degree_eq_minpoly gamma).symm
  let basis : Basis (Fin (degree gamma)) Rat K :=
    pb.basis.reindex (finCongr hpbdim)
  have hbasis (i : Fin (degree gamma)) :
      basis i = (⟨gamma.toComplex ^ i.val,
        K.pow_mem (IntermediateField.mem_adjoin_simple_self
          Rat gamma.toComplex) i.val⟩ : K) := by
    apply Subtype.ext
    simp [basis, pb]
  let aK : K := ⟨a.toComplex, ha⟩
  let c : Vector Rat (degree gamma) :=
    Vector.ofFn fun i => basis.repr aK i
  have hreconstruct : ∑ i : Fin (degree gamma), c.get i •
      (⟨gamma.toComplex ^ i.val,
        K.pow_mem (IntermediateField.mem_adjoin_simple_self
          Rat gamma.toComplex) i.val⟩ : K) = aK := by
    simpa [c, hbasis] using basis.sum_repr aK
  refine ⟨c, ?_, hreconstruct⟩
  apply HexMatrixMathlib.vectorEquiv.injective
  rw [HexMatrixMathlib.vectorEquiv_vecMul]
  funext j
  simp only [Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have htraceBound (i : Fin (degree gamma)) :
      i.val + j.val < powerTraces.size := by
    rw [← (HexRootsMathlib.array_mapM_some_get hpowerTraces).1]
    have hpos := degree_pos gamma
    omega
  have hpowersBound (i : Fin (degree gamma)) :
      i.val + j.val < powers.size := by
    have hpos := degree_pos gamma
    omega
  have hentry (i : Fin (degree gamma)) :
      powerTraces[i.val + j.val]! = Algebra.trace Rat K
        ((⟨gamma.toComplex ^ i.val,
            K.pow_mem (IntermediateField.mem_adjoin_simple_self
              Rat gamma.toComplex) i.val⟩ : K) *
          (⟨gamma.toComplex ^ j.val,
            K.pow_mem (IntermediateField.mem_adjoin_simple_self
              Rat gamma.toComplex) j.val⟩ : K)) := by
    have hpow := hpowersBound i
    have hmember : powers[i.val + j.val].toComplex ∈ K := by
      rw [hvalues (i.val + j.val) hpow]
      exact K.pow_mem (IntermediateField.mem_adjoin_simple_self
        Rat gamma.toComplex) (i.val + j.val)
    have htrace := trace?_sound gamma powers[i.val + j.val] hmember
      ((HexRootsMathlib.array_mapM_some_get hpowerTraces).2
        (i.val + j.val) hpow (htraceBound i))
    rw [getElem!_pos powerTraces (i.val + j.val) (htraceBound i)]
    calc
      powerTraces[i.val + j.val]'(htraceBound i) = Algebra.trace Rat K
          ⟨(powers[i.val + j.val]'hpow).toComplex, hmember⟩ := htrace
      _ = _ := by
        apply congrArg (Algebra.trace Rat K)
        apply Subtype.ext
        simp [hvalues (i.val + j.val) hpow, pow_add]
  rw [show (HexMatrixMathlib.vectorEquiv rhs) j = rhs.get j by rfl,
    coordinateRhs_get gamma a powers hsize hvalues ha products hproducts
      rhs hrhs j]
  simp only [HexMatrixMathlib.matrixEquiv_ofFn,
    HexMatrixMathlib.vectorEquiv_apply]
  change (∑ i : Fin (degree gamma),
      c.get i * powerTraces[i.val + j.val]!) =
    Algebra.trace Rat K
      ⟨a.toComplex * gamma.toComplex ^ j.val,
        K.mul_mem ha (K.pow_mem
          (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex)
          j.val)⟩
  simp_rw [hentry]
  calc
    ∑ i : Fin (degree gamma), c.get i * Algebra.trace Rat K
        ((⟨gamma.toComplex ^ i.val,
            K.pow_mem (IntermediateField.mem_adjoin_simple_self
              Rat gamma.toComplex) i.val⟩ : K) *
          (⟨gamma.toComplex ^ j.val,
            K.pow_mem (IntermediateField.mem_adjoin_simple_self
              Rat gamma.toComplex) j.val⟩ : K)) =
      Algebra.trace Rat K
        ((∑ i : Fin (degree gamma), c.get i •
          (⟨gamma.toComplex ^ i.val,
            K.pow_mem (IntermediateField.mem_adjoin_simple_self
              Rat gamma.toComplex) i.val⟩ : K)) *
          ⟨gamma.toComplex ^ j.val,
            K.pow_mem (IntermediateField.mem_adjoin_simple_self
              Rat gamma.toComplex) j.val⟩) := by
        rw [Finset.sum_mul, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        change c.get i • Algebra.trace Rat K
            ((⟨gamma.toComplex ^ i.val,
                K.pow_mem (IntermediateField.mem_adjoin_simple_self
                  Rat gamma.toComplex) i.val⟩ : K) *
              (⟨gamma.toComplex ^ j.val,
                K.pow_mem (IntermediateField.mem_adjoin_simple_self
                  Rat gamma.toComplex) j.val⟩ : K)) = _
        rw [← map_smul]
        congr 1
        exact (Algebra.smul_mul_assoc _ _ _).symm
    _ = _ := by
      rw [hreconstruct]
      apply congrArg (Algebra.trace Rat K)
      apply Subtype.ext
      rfl

private theorem coordinateEval (gamma : AlgebraicNumber)
    (coeffs : Vector Rat (degree gamma)) :
    QAdjoin.toComplex
        (QAdjoin.reduce gamma.p gamma.x
          (DensePoly.ofCoeffs coeffs.toArray))
        gamma.rep gamma.rep_mk =
      ∑ i : Fin (degree gamma),
        (coeffs.get i : ℂ) * gamma.toComplex ^ i.val := by
  unfold QAdjoin.toComplex QAdjoin.reduce
  rw [QAdjoin.eval_reduceCoeffs,
    HexPolyMathlib.eval₂_toPolynomial]
  let f : DensePoly Rat := DensePoly.ofCoeffs coeffs.toArray
  have hfsize : f.size ≤ degree gamma :=
    (DensePoly.size_ofCoeffs_le coeffs.toArray).trans (by simp)
  change (∑ i ∈ Finset.range f.size,
      (algebraMap Rat ℂ) (f.coeff i) * gamma.rep.root ^ i) = _
  calc
    ∑ i ∈ Finset.range f.size,
        (algebraMap Rat ℂ) (f.coeff i) * gamma.rep.root ^ i =
      ∑ i ∈ Finset.range (degree gamma),
        (algebraMap Rat ℂ) (f.coeff i) * gamma.rep.root ^ i := by
      apply Finset.sum_subset (Finset.range_mono hfsize)
      intro i _ hi
      have hfi : f.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f (by simpa using hi)
      simp [hfi]
    _ = ∑ i ∈ Finset.range (degree gamma),
        (coeffs.toArray.getD i (Zero.zero : Rat) : ℂ) *
          gamma.toComplex ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show f.coeff i = coeffs.toArray.getD i (Zero.zero : Rat) by
        simp [f]]
      rfl
    _ = ∑ i : Fin (degree gamma),
        (coeffs.toArray.getD i.val (Zero.zero : Rat) : ℂ) *
          gamma.toComplex ^ i.val :=
      (Fin.sum_univ_eq_sum_range
        (fun i => (coeffs.toArray.getD i (Zero.zero : Rat) : ℂ) *
          gamma.toComplex ^ i) (degree gamma)).symm
    _ = ∑ i : Fin (degree gamma),
        (coeffs.get i : ℂ) * gamma.toComplex ^ i.val := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i.val < coeffs.toArray.size := by simp
      have hget : coeffs.toArray.getD i.val (Zero.zero : Rat) =
          coeffs.get i := by
        rw [Vector.get_eq_getElem,
          ← Array.getElem_eq_getD (Zero.zero : Rat)]
        exact Vector.getElem_toArray (xs := coeffs) hi'
      rw [hget]

private theorem coordinateOfSpan_sound (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber) (powerTraces : Array Rat)
    (hsize : powers.size = 2 * degree gamma - 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯)
    (hpowerTraces :
      powers.mapM (trace? (degree gamma)) = some powerTraces)
    (products : Vector AlgebraicNumber (degree gamma))
    (hproducts :
      (⟨(List.range (degree gamma)).toArray, by simp⟩ :
          Vector Nat (degree gamma)).mapM
        (fun k => mul? a powers[k]!) = some products)
    (rhs : Vector Rat (degree gamma))
    (hrhs : products.mapM (trace? (degree gamma)) = some rhs)
    (coeffs : Vector Rat (degree gamma))
    (hcoeffs : Matrix.spanCoeffs
      (Matrix.ofFn fun i : Fin (degree gamma) =>
        fun j : Fin (degree gamma) => powerTraces[i.val + j.val]!)
      rhs = some coeffs) :
    QAdjoin.toComplex
        (QAdjoin.reduce gamma.p gamma.x
          (DensePoly.ofCoeffs coeffs.toArray))
        gamma.rep gamma.rep_mk = a.toComplex := by
  obtain ⟨canonical, hcanonical, hreconstruct⟩ :=
    basisCoeffs_solve gamma a powers powerTraces hsize hvalues ha
      hpowerTraces products hproducts rhs hrhs
  have hdet := traceGram_det_ne_zero gamma powers powerTraces hsize
    hvalues hpowerTraces
  have hcoeffsSolve := Matrix.spanCoeffs_sound _ _ _ hcoeffs
  have hcanonicalEq : coeffs = canonical :=
    (vecMul_injective_of_det_ne_zero _ hdet)
      (hcoeffsSolve.trans hcanonical.symm)
  subst coeffs
  rw [coordinateEval]
  have hcomplex := congrArg
    (fun z : Rat⟮gamma.toComplex⟯ => (z : ℂ)) hreconstruct
  simpa [map_sum, Algebra.smul_def] using hcomplex

/-- Coordinate recovery succeeds for an element of the primitive field when
the supplied table contains the required consecutive powers. -/
theorem coordinates?_isSome (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber)
    (hsize : powers.size = 2 * degree gamma - 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (ha : a.toComplex ∈ Rat⟮gamma.toComplex⟯) :
    (coordinates? gamma a powers).isSome := by
  let K : IntermediateField Rat ℂ := Rat⟮gamma.toComplex⟯
  unfold coordinates?
  split
  · simp
  · simp only
    have hpowerTracesSome :
        (powers.mapM (trace? (degree gamma))).isSome := by
      apply HexRootsMathlib.array_mapM_isSome
      intro power hpower
      have hpower' : power ∈ powers := by simpa using hpower
      rw [Array.mem_iff_getElem] at hpower'
      obtain ⟨i, hi, rfl⟩ := hpower'
      apply trace?_isSome gamma
      rw [hvalues i hi]
      exact K.pow_mem
        (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex) i
    obtain ⟨powerTraces, hpowerTraces⟩ :=
      Option.isSome_iff_exists.mp hpowerTracesSome
    have hproductsSome :
        ((⟨Array.range (degree gamma), by simp⟩ :
            Vector Nat (degree gamma)).mapM
          fun k => mul? a powers[k]!).isSome := by
      apply vector_mapM_isSome
      intro i
      exact mul?_isSome _ _
    obtain ⟨products, hproducts⟩ :=
      Option.isSome_iff_exists.mp hproductsSome
    have hindices :
        (⟨Array.range (degree gamma), by simp⟩ :
            Vector Nat (degree gamma)) =
          ⟨(List.range (degree gamma)).toArray, by simp⟩ := by
      apply Vector.ext
      intro i hi
      simp
    have hproductsList :
        (⟨(List.range (degree gamma)).toArray, by simp⟩ :
            Vector Nat (degree gamma)).mapM
          (fun k => mul? a powers[k]!) = some products := by
      rw [← hindices]
      exact hproducts
    have hrhsSome :
        (products.mapM (trace? (degree gamma))).isSome := by
      apply vector_mapM_isSome
      intro i
      apply trace?_isSome gamma
      have hproduct := coordinateProducts_get gamma a powers hsize
        hvalues products hproductsList i
      rw [hproduct]
      exact K.mul_mem ha (K.pow_mem
        (IntermediateField.mem_adjoin_simple_self Rat gamma.toComplex)
        i.val)
    obtain ⟨rhs, hrhs⟩ := Option.isSome_iff_exists.mp hrhsSome
    have hdet :
        (_root_.Matrix.det (HexMatrixMathlib.matrixEquiv
          (Matrix.ofFn fun i : Fin (degree gamma) =>
            fun j : Fin (degree gamma) =>
              powerTraces[i.val + j.val]!))) ≠ 0 :=
      traceGram_det_ne_zero gamma powers powerTraces hsize hvalues
        hpowerTraces
    have hcoeffsSome : (Matrix.spanCoeffs
        (Matrix.ofFn fun i : Fin (degree gamma) =>
          fun j : Fin (degree gamma) => powerTraces[i.val + j.val]!)
        rhs).isSome :=
      spanCoeffs_isSome_of_det_ne_zero _ rhs hdet
    obtain ⟨coeffs, hcoeffs⟩ :=
      Option.isSome_iff_exists.mp hcoeffsSome
    let coordinate : QAdjoin gamma.p gamma.x :=
      QAdjoin.reduce gamma.p gamma.x
        (DensePoly.ofCoeffs coeffs.toArray)
    let : ZPoly.CheckedIrreducible gamma.p := gamma.checked
    obtain ⟨recovered, hrecovered⟩ := Option.isSome_iff_exists.mp
      (QAdjoin.toAlgebraicNumber?_isSome coordinate gamma.rep
        gamma.rep_mk)
    have hcoordinate :
        QAdjoin.toComplex coordinate gamma.rep gamma.rep_mk =
          a.toComplex := by
      exact coordinateOfSpan_sound gamma a powers powerTraces hsize
        hvalues ha hpowerTraces products hproductsList rhs hrhs coeffs
        hcoeffs
    have hrecoveredValue : recovered.toComplex = a.toComplex :=
      (QAdjoin.toAlgebraicNumber?_sound coordinate gamma.rep gamma.rep_mk
        hrecovered).trans hcoordinate
    have hrecoveredEq : recovered = a :=
      AlgebraicNumber.toComplex_injective hrecoveredValue
    subst recovered
    simp [hpowerTraces, hproducts, hrhs, hcoeffs, coordinate,
      hrecovered]

/-- Successful coordinate recovery represents the original algebraic value at
the selected primitive embedding. -/
theorem coordinates?_sound (gamma a : AlgebraicNumber)
    (powers : Array AlgebraicNumber) {coordinate : QAdjoin gamma.p gamma.x}
    (h : coordinates? gamma a powers = some coordinate) :
    QAdjoin.toComplex coordinate gamma.rep gamma.rep_mk = a.toComplex := by
  let : ZPoly.CheckedIrreducible gamma.p := gamma.checked
  unfold coordinates? at h
  split at h
  next hzero =>
    have hcoordinate : (0 : QAdjoin gamma.p gamma.x) = coordinate :=
      Option.some.inj h
    rw [← hcoordinate, QAdjoin.map_zero]
    exact ((AlgebraicNumber.isZero_iff a).mp hzero).symm
  next _ =>
    obtain ⟨powerTraces, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨products, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rhs, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨coeffs, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨recovered, hrecovered, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next heq =>
      have hcoordinate := Option.some.inj h
      subst coordinate
      rw [← QAdjoin.toAlgebraicNumber?_sound _ gamma.rep gamma.rep_mk
        hrecovered]
      exact (AlgebraicNumber.beq_iff recovered a).mp heq
    next => simp at h

end Hex.AlgebraicPoly.Common
