/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.BadVector
public import HexBerlekampZassenhausMathlib.Resultant
import all HexBerlekampZassenhausMathlib.FactorBound

public section
set_option backward.proofsInPublic true

/-!
Executable arithmetic for the BHKS bad-vector contradiction.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

/-- The complete-vector coordinate envelope used by the BHKS adjustment is
strictly below the executable resultant cap. -/
theorem adjustedCoordBound_lt_bhksBound
    (f : Hex.ZPoly) (hfdeg : 0 < f.degree?.getD 0) :
    let n := f.degree?.getD 0
    let R := 4 * n + n * n * n
    let V := (2 * n) * 2 ^ (2 * n) * R
    V + V * R + 2 ^ n * R < Hex.bhksBound f := by
  let n := f.degree?.getD 0
  let R := 4 * n + n * n * n
  let V := (2 * n) * 2 ^ (2 * n) * R
  let E := V + V * R + 2 ^ n * R
  let C := 500 * (Hex.bhksColumnFloor f + 1)
  let M := (n + 1) * E * C
  let A := max (Hex.ZPoly.defaultFactorCoeffBound f) M
  have hn : 0 < n := by simpa only [n] using hfdeg
  have hC : 1 ≤ C := by
    dsimp only [C]
    have : 1 ≤ Hex.bhksColumnFloor f + 1 := Nat.one_le_iff_ne_zero.mpr (by omega)
    omega
  have hEM : E ≤ M := by
    dsimp only [M]
    calc
      E = 1 * E * 1 := by simp
      _ ≤ (n + 1) * E * C := by
        gcongr
        all_goals omega
  have hEA : E ≤ A := hEM.trans (Nat.le_max_right _ _)
  have hbase : 1 ≤ (2 * n) * A := by
    have hA : 1 ≤ A := by
      have : 1 ≤ E := by
        have hR : 0 < R := by
          dsimp only [R]
          omega
        have hterm : 0 < 2 ^ n * R :=
          Nat.mul_pos (pow_pos (by omega) _) hR
        dsimp only [E]
        omega
      omega
    exact Nat.mul_pos (by omega) hA
  have hA_base : A ≤ (2 * n) * A := by
    calc
      A = 1 * A := by simp
      _ ≤ (2 * n) * A := by
        gcongr
        all_goals omega
  have hbase_pow :
      (2 * n) * A ≤ ((2 * n) * A) ^ (2 * n) := by
    calc
      (2 * n) * A = ((2 * n) * A) ^ 1 := by simp
      _ ≤ ((2 * n) * A) ^ (2 * n) :=
        Nat.pow_le_pow_right hbase (by omega)
  unfold Hex.bhksBound
  change E < 1 + ((2 * n) * A) ^ (2 * n)
  omega

/--
The explicit `bhksBound` strictly dominates the resultant of the input and
any corrected full auxiliary whose complete lattice vector satisfies the `E`
coordinate bound built into that cap.
-/
theorem cldFullAux_resultant_natAbs_lt_bhksBound
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (hf : f ≠ 0) (hfdeg : 0 < f.degree?.getD 0)
    (hp2 : 2 ≤ p) (hp500 : p ≤ 500)
    (hr : liftedFactors.size ≤ f.degree?.getD 0)
    (hv : ∀ x : Fin (liftedFactors.size + f.degree?.getD 0),
      v[x].natAbs ≤
        let n := f.degree?.getD 0
        let R := 4 * n + n * n * n
        let V := (2 * n) * 2 ^ (2 * n) * R
        V + V * R + 2 ^ n * R) :
    (Polynomial.resultant
      (HexPolyZMathlib.toPolynomial f)
      (HexPolyZMathlib.toPolynomial
        (cldFullAux f p a liftedFactors v))).natAbs <
      Hex.bhksBound f := by
  let n := f.degree?.getD 0
  let R := 4 * n + n * n * n
  let V := (2 * n) * 2 ^ (2 * n) * R
  let E := V + V * R + 2 ^ n * R
  let C := 500 * (Hex.bhksColumnFloor f + 1)
  let M := (n + 1) * E * C
  let A := max (Hex.ZPoly.defaultFactorCoeffBound f) M
  have hfcoeff (k : Nat) :
      ((HexPolyZMathlib.toPolynomial f).coeff k).natAbs ≤ A := by
    rw [HexPolyZMathlib.coeff_toPolynomial]
    have hself : f ∣ f :=
      ⟨1, (Hex.DensePoly.mul_one_right_poly f).symm⟩
    exact (defaultFactorCoeffBound_valid f hf f hself k).trans
      (Nat.le_max_left _ _)
  have hhcoeff (k : Nat) :
      ((HexPolyZMathlib.toPolynomial
        (cldFullAux f p a liftedFactors v)).coeff k).natAbs ≤ A := by
    rw [HexPolyZMathlib.coeff_toPolynomial]
    have hM := cldFullAux_coeff_natAbs_le
      f p a liftedFactors v E hp2 hp500 hr (by
        intro x
        simpa only [E, V, R, n] using hv x) k
    exact hM.trans (by
      simpa only [A, M, C, E, n] using Nat.le_max_right
        (Hex.ZPoly.defaultFactorCoeffBound f) M)
  have hres := resultant_natAbs_le_coeff_bound
    (HexPolyZMathlib.toPolynomial f)
    (HexPolyZMathlib.toPolynomial (cldFullAux f p a liftedFactors v))
    A hfcoeff hhcoeff
  have hdegF :
      (HexPolyZMathlib.toPolynomial f).natDegree = n := by
    simpa only [n] using HexPolyMathlib.natDegree_toPolynomial f
  have hdegH :
      (HexPolyZMathlib.toPolynomial
        (cldFullAux f p a liftedFactors v)).natDegree ≤ n := by
    simpa only [n] using cldFullAux_natDegree_le f p a liftedFactors v
  let N :=
    (HexPolyZMathlib.toPolynomial f).natDegree +
      (HexPolyZMathlib.toPolynomial
        (cldFullAux f p a liftedFactors v)).natDegree
  have hN : N ≤ 2 * n := by
    dsimp only [N]
    omega
  have hApos : 1 ≤ A := by
    have hdefault := Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf
    have hle : Hex.ZPoly.defaultFactorCoeffBound f ≤ A :=
      Nat.le_max_left _ _
    omega
  have hnpos : 0 < n := by
    simpa only [n] using hfdeg
  have hbasepos : 1 ≤ (2 * n) * A := by
    have hAne : A ≠ 0 := by omega
    exact Nat.one_le_iff_ne_zero.mpr <|
      mul_ne_zero (mul_ne_zero (by omega) hnpos.ne') hAne
  have hpow :
      (N * A) ^ N ≤ ((2 * n) * A) ^ (2 * n) := by
    calc
      (N * A) ^ N ≤ ((2 * n) * A) ^ N :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right A hN) N
      _ ≤ ((2 * n) * A) ^ (2 * n) :=
        Nat.pow_le_pow_right hbasepos hN
  have hupper :
      (Polynomial.resultant
        (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial
          (cldFullAux f p a liftedFactors v))).natAbs ≤
        ((2 * n) * A) ^ (2 * n) :=
    hres.trans hpow
  unfold Hex.bhksBound
  change
    (Polynomial.resultant
      (HexPolyZMathlib.toPolynomial f)
      (HexPolyZMathlib.toPolynomial
        (cldFullAux f p a liftedFactors v))).natAbs <
      1 + ((2 * n) * A) ^ (2 * n)
  omega

/--
Abstract algebraic BHKS bad-vector contradiction.

The hypotheses expose exactly the production facts later supplied by the
Hensel lift: local monicity and positive degree, pairwise coprimality, own-CLD
coprimality, and the fact that every monic irreducible factor of `f` is
represented by one true support.  The conclusion rules out a bounded lattice
vector having one zero exponent while remaining nonzero on every true support.
-/
theorem no_badVector
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (trueSupports : Set (Set (Fin liftedFactors.size)))
    (hf : f ≠ 0) (hfdeg : 0 < f.degree?.getD 0)
    (hf_lc_coprime :
      IsCoprime ((p ^ a : Nat) : Int)
        (HexPolyZMathlib.toPolynomial f).leadingCoeff)
    (hp2 : 2 ≤ p) (hp500 : p ≤ 500)
    (hr : liftedFactors.size ≤ f.degree?.getD 0)
    (hk : 1 < p ^ a)
    (hprecision : 2 * Hex.bhksBound f < p ^ a)
    (hcut : ∀ j : Fin (f.degree?.getD 0),
      Hex.bhksCoeffCutThreshold p f j.val ≤ a)
    (hfac : ∀ i : Fin liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic (liftedFactors.getD i.val 1) ∧
        0 < (liftedFactors.getD i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr f (liftedFactors.getD i.val 1 * h) (p ^ a))
    (hdeg_le : ∀ i : Fin liftedFactors.size,
      (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i.val 1)).natDegree ≤
          (HexPolyZMathlib.toPolynomial f).natDegree)
    (hcop : ∀ i j : Fin liftedFactors.size, j ≠ i →
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD j.val 1)).map
            (Int.castRingHom (ZMod (p ^ a)))))
    (hown : ∀ i : Fin liftedFactors.size,
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (Hex.cldQuotientMod f
            (liftedFactors.getD i.val 1) p a)).map
              (Int.castRingHom (ZMod (p ^ a)))))
    (hsupport :
      ∀ q : Polynomial ℤ,
        Irreducible q → q ∣ HexPolyZMathlib.toPolynomial f →
        ∃ S ∈ trueSupports, ∀ i ∈ S,
          (HexPolyZMathlib.toPolynomial
            (liftedFactors.getD i.val 1)).map
              (Int.castRingHom (ZMod (p ^ a))) ∣
            q.map (Int.castRingHom (ZMod (p ^ a))))
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (hv : Hex.Matrix.memLattice
      (Hex.bhksLatticeBasis f p a liftedFactors).basis v)
    (hzero : ∃ i : Fin liftedFactors.size,
      v[Fin.castAdd (f.degree?.getD 0) i] = 0)
    (hnonzero : ∀ S ∈ trueSupports, ∃ i ∈ S,
      v[Fin.castAdd (f.degree?.getD 0) i] ≠ 0)
    (hvBound : ∀ x : Fin (liftedFactors.size + f.degree?.getD 0),
      v[x].natAbs ≤
        let n := f.degree?.getD 0
        let R := 4 * n + n * n * n
        let V := (2 * n) * 2 ^ (2 * n) * R
        V + V * R + 2 ^ n * R) :
    False := by
  classical
  let H := cldFullAux f p a liftedFactors v
  let res := Polynomial.resultant
    (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial H)
  have hf_poly_ne : HexPolyZMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    apply HexPolyZMathlib.equiv.injective
    simpa using hzero
  have hcoord_lt (i : Fin liftedFactors.size) :
      v[Fin.castAdd (f.degree?.getD 0) i].natAbs < p ^ a := by
    let n := f.degree?.getD 0
    let R := 4 * n + n * n * n
    let V := (2 * n) * 2 ^ (2 * n) * R
    let E := V + V * R + 2 ^ n * R
    have hE : E < Hex.bhksBound f := by
      simpa only [E, V, R, n] using adjustedCoordBound_lt_bhksBound f hfdeg
    have hvE :
        v[Fin.castAdd (f.degree?.getD 0) i].natAbs ≤ E := by
      simpa only [E, V, R, n] using
        hvBound (Fin.castAdd (f.degree?.getD 0) i)
    exact hvE.trans_lt (hE.trans (by omega))
  have hres_ne : res ≠ 0 := by
    apply int_resultant_ne_zero_of_no_irreducible_common_factor
      (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial H)
      hf_poly_ne
    intro q hqirr hqf hqH
    obtain ⟨S, hS, hSdiv⟩ := hsupport q hqirr hqf
    obtain ⟨i, hiS, hi_ne⟩ := hnonzero S hS
    have hqHmap :
        q.map (Int.castRingHom (ZMod (p ^ a))) ∣
          (HexPolyZMathlib.toPolynomial H).map
            (Int.castRingHom (ZMod (p ^ a))) :=
      Polynomial.map_dvd (Int.castRingHom (ZMod (p ^ a))) hqH
    have hiH :
        (HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))) ∣
          (HexPolyZMathlib.toPolynomial H).map
            (Int.castRingHom (ZMod (p ^ a))) :=
      (hSdiv i hiS).trans hqHmap
    have hicast :=
      coord_cast_eq_zero_of_liftedFactor_dvd_cldFullAux
        f p a liftedFactors v i hfdeg hk (by omega) hcut hfac
          (hcop i) (hown i) hv (by simpa only [H] using hiH)
    have hidvd :
        ((p ^ a : Nat) : ℤ) ∣
          v[Fin.castAdd (f.degree?.getD 0) i] :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ a)).mp hicast
    have hile :=
      Int.natAbs_le_of_dvd_ne_zero hidvd hi_ne
    have hle_mod :
        p ^ a ≤ v[Fin.castAdd (f.degree?.getD 0) i].natAbs := by
      simpa using hile
    exact (not_lt_of_ge hle_mod) (hcoord_lt i)
  obtain ⟨i₀, hi₀zero⟩ := hzero
  obtain ⟨cofactor, hi₀monic, hi₀deg, hi₀fac⟩ := hfac i₀
  let q := HexPolyZMathlib.toPolynomial (liftedFactors.getD i₀.val 1)
  have hqmonic : q.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hi₀monic
  have hqdeg :
      q.natDegree =
        (liftedFactors.getD i₀.val 1).degree?.getD 0 := by
    exact HexPolyMathlib.natDegree_toPolynomial _
  have hqf :
      q.map (Int.castRingHom (ZMod (p ^ a))) ∣
        (HexPolyZMathlib.toPolynomial f).map
          (Int.castRingHom (ZMod (p ^ a))) := by
    have hmap := HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      f (liftedFactors.getD i₀.val 1 * cofactor) (p ^ a) hi₀fac
    rw [hmap, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hqH :
      q.map (Int.castRingHom (ZMod (p ^ a))) ∣
        (HexPolyZMathlib.toPolynomial H).map
          (Int.castRingHom (ZMod (p ^ a))) := by
    exact liftedFactor_dvd_cldFullAux f p a liftedFactors v i₀
      hfdeg hk (by omega) hcut hfac (hcop i₀) hv hi₀zero
  have hres_dvd :
      ((p ^ (a * q.natDegree) : Nat) : ℤ) ∣ res := by
    exact pow_dvd_resultant_of_map_dvd_left_coprime hk hqmonic rfl
      hf_poly_ne hf_lc_coprime
      (hdeg_le i₀) hqf hqH
  have ha_le : a ≤ a * q.natDegree := by
    rw [hqdeg]
    exact Nat.le_mul_of_pos_right a hi₀deg
  have hpow_nat : p ^ a ∣ p ^ (a * q.natDegree) :=
    pow_dvd_pow p ha_le
  have hpow_int :
      ((p ^ a : Nat) : ℤ) ∣ ((p ^ (a * q.natDegree) : Nat) : ℤ) := by
    exact_mod_cast hpow_nat
  have hpa_res : ((p ^ a : Nat) : ℤ) ∣ res :=
    hpow_int.trans hres_dvd
  have hres_lower := Int.natAbs_le_of_dvd_ne_zero hpa_res hres_ne
  have hres_upper :
      res.natAbs < Hex.bhksBound f := by
    exact cldFullAux_resultant_natAbs_lt_bhksBound
      f p a liftedFactors v hf hfdeg hp2 hp500 hr hvBound
  have hmod_abs : (((p ^ a : Nat) : ℤ).natAbs) = p ^ a := by simp
  rw [hmod_abs] at hres_lower
  omega

end BHKS

end

end HexBerlekampZassenhausMathlib
