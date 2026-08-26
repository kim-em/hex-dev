/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.CLDColumnBound

public section
set_option backward.proofsInPublic true

/-!
Full-vector auxiliary polynomials for the BHKS retained-row argument.

The truncated CLD lattice stores high cut coefficients in its top-right block
and independent period coefficients in its bottom-right block.  Consequently
the high-cut tail by itself is not the polynomial used in the resultant
argument.  The definitions below reconstruct the whole coefficient from both
blocks.  For a lattice vector with first block `e`, tail coordinate `t_j`, and
cut exponent `ell_j`, the coefficient is

`p^ell_j * t_j + sum_i e_i * lowResidue(i,j)`.

For an actual row combination this is exactly the full centred CLD residue
combination plus an explicit multiple of `p^precision`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open scoped BigOperators

namespace BHKS

/-- The long-division loop updates quotient entries in place, so it preserves
the quotient array's allocated length. -/
private theorem divModArrayAux_fst_size
    {R : Type*} [Zero R] [DecidableEq R] [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R) :
    ∀ fuel (quot rem : Array R),
      (Hex.DensePoly.divModArrayAux q qDegree scaleLead fuel quot rem).1.size =
        quot.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro quot rem
      rfl
  | succ fuel ih =>
      intro quot rem
      rw [Hex.DensePoly.divModArrayAux]
      split
      · rfl
      · rename_i rd hrd
        split
        · rfl
        · dsimp only
          rw [ih]
          simp

/-- The executable dense quotient uses at most the preallocated
`dividend.size - divisorDegree` coefficient slots. -/
private theorem divMod_fst_size_le
    {R : Type*} [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : Hex.DensePoly R) :
    (Hex.DensePoly.divMod f g).1.size ≤ f.size - (g.size - 1) := by
  unfold Hex.DensePoly.divMod
  split
  · simp
  · unfold Hex.DensePoly.divModArray
    split
    · simp
    · dsimp only
      exact Nat.le_trans (Hex.DensePoly.size_ofCoeffs_le _)
        (le_of_eq (by
          rw [divModArrayAux_fst_size]
          simp))

/-- A positive-degree CLD divisor leaves a quotient with strictly fewer
coefficient slots than the input.  Thus the production `coeffWidth = deg(f)`
array stores the whole CLD quotient, not a truncation. -/
theorem cldQuotientMod_size_le_degree
    (f g : Hex.ZPoly) (p a : Nat)
    (hf : 0 < f.degree?.getD 0)
    (hg : 0 < g.degree?.getD 0) :
    (Hex.cldQuotientMod f g p a).size ≤ f.degree?.getD 0 := by
  rw [HexBerlekampZassenhausMathlib.cldQuotientMod_eq_spec]
  unfold Hex.cldQuotientModBignum
  let num := Hex.ZPoly.reduceModPow
    (f * Hex.DensePoly.derivative g) p a
  have hfsize : f.size = f.degree?.getD 0 + 1 := by
    have hpos : 0 < f.size := by
      by_contra h
      have hs : f.size = 0 := by omega
      simp [Hex.DensePoly.degree?, hs] at hf
    rw [Hex.DensePoly.degree?_eq_some_of_pos_size f hpos]
    simp
    omega
  have hgsize : g.size - 1 = g.degree?.getD 0 := by
    have hpos : 0 < g.size := by
      by_contra h
      have hs : g.size = 0 := by omega
      simp [Hex.DensePoly.degree?, hs] at hg
    rw [Hex.DensePoly.degree?_eq_some_of_pos_size g hpos]
    simp
  have hderiv :
      (Hex.DensePoly.derivative g).size ≤ g.size - 1 :=
    Hex.DensePoly.size_derivative_le g
  have hnum :
      num.size ≤ f.size + (g.size - 1) - 1 := by
    calc
      num.size ≤ (f * Hex.DensePoly.derivative g).size :=
        Hex.ZPoly.reduceModPow_size_le _ p a
      _ ≤ f.size + (Hex.DensePoly.derivative g).size - 1 :=
        Hex.DensePoly.size_mul_le _ _
      _ ≤ f.size + (g.size - 1) - 1 := by
        omega
  calc
    (Hex.ZPoly.reduceModPow
        (Hex.DensePoly.divMod num g).1 p a).size
        ≤ (Hex.DensePoly.divMod num g).1.size :=
      Hex.ZPoly.reduceModPow_size_le _ p a
    _ ≤ num.size - (g.size - 1) := divMod_fst_size_le num g
    _ ≤ f.degree?.getD 0 := by omega

/-- The full centred CLD-residue combination attached to the first block of a
BHKS vector. -/
@[expose]
def polCoeff
    (L : Hex.BhksLatticeBasis)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (v : Vector ℤ (L.factorCount + L.coeffWidth))
    (j : Fin L.coeffWidth) : ℤ :=
  ∑ i : Fin L.factorCount,
    v[Fin.castAdd L.coeffWidth i] *
      Hex.centeredResiduePow L.p L.precision (z i j)

/-- Correct reconstruction of one coefficient of the truncated-lattice
auxiliary polynomial from the *full* lattice vector. -/
@[expose]
def fullAuxCoeff
    (L : Hex.BhksLatticeBasis)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (v : Vector ℤ (L.factorCount + L.coeffWidth))
    (j : Fin L.coeffWidth) : ℤ :=
  let ell := L.cutThresholds.getD j.val 0
  ((L.p ^ ell : Nat) : ℤ) * v[Fin.natAdd L.factorCount j] +
    ∑ i : Fin L.factorCount,
      v[Fin.castAdd L.coeffWidth i] *
        Hex.centeredResiduePow L.p ell
          (Hex.centeredResiduePow L.p L.precision (z i j))

/-- Polynomial whose coefficients are the full centred CLD-residue
combination `POL(e)`. -/
@[expose]
def pol
    (L : Hex.BhksLatticeBasis)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (v : Vector ℤ (L.factorCount + L.coeffWidth)) : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs <| Array.ofFn fun j => polCoeff L z v j

/-- Polynomial reconstructed from all coordinates of a truncated BHKS lattice
vector. -/
@[expose]
def fullAux
    (L : Hex.BhksLatticeBasis)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (v : Vector ℤ (L.factorCount + L.coeffWidth)) : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs <| Array.ofFn fun j => fullAuxCoeff L z v j

/-- Coefficient rule for `pol`. -/
@[simp, grind =] theorem pol_coeff
    (L : Hex.BhksLatticeBasis)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (v : Vector ℤ (L.factorCount + L.coeffWidth))
    (j : Fin L.coeffWidth) :
    (pol L z v).coeff j.val = polCoeff L z v j := by
  rw [pol, Hex.DensePoly.coeff_ofCoeffs]
  simp [Array.getD, j.isLt]

/-- Coefficient rule for `fullAux`. -/
@[simp, grind =] theorem fullAux_coeff
    (L : Hex.BhksLatticeBasis)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (v : Vector ℤ (L.factorCount + L.coeffWidth))
    (j : Fin L.coeffWidth) :
    (fullAux L z v).coeff j.val = fullAuxCoeff L z v j := by
  rw [fullAux, Hex.DensePoly.coeff_ofCoeffs]
  simp [Array.getD, j.isLt]

/--
The corrected coefficient reconstruction identity.

The top-right block contributes the cut coefficients, the bottom-right block
contributes the period coefficient, and the low residues restore the discarded
part of each centred CLD residue.  The only term left over is the displayed
multiple of `p^precision`.
-/
theorem fullAuxCoeff_vecMul
    (L : Hex.BhksLatticeBasis) (hL : BhksBlockForm L)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (c : Vector ℤ (L.factorCount + L.coeffWidth))
    (j : Fin L.coeffWidth)
    (hcut : L.cutThresholds.getD j.val 0 ≤ L.precision)
    (hp : 0 < L.p)
    (hcld : ∀ i : Fin L.factorCount,
      (L.cldRows.getD i.val #[]).getD j.val 0 =
        Hex.psiCut L.p L.precision (L.cutThresholds.getD j.val 0) (z i j)) :
    fullAuxCoeff L z (Hex.Matrix.vecMul c L.basis) j =
      polCoeff L z (Hex.Matrix.vecMul c L.basis) j +
        ((L.p ^ L.precision : Nat) : ℤ) * c[Fin.natAdd L.factorCount j] := by
  classical
  let ell := L.cutThresholds.getD j.val 0
  have hpell : L.p ^ ell ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt hp)
  have hfirst (i : Fin L.factorCount) :
      (Hex.Matrix.vecMul c L.basis)[Fin.castAdd L.coeffWidth i] =
        c[Fin.castAdd L.coeffWidth i] :=
    vecMul_first_of_blockForm L hL c i
  have htail :=
    vecMul_tail_of_blockForm L hL c j
  have hdecomp (i : Fin L.factorCount) :
      Hex.centeredResiduePow L.p L.precision (z i j) =
        Hex.centeredResiduePow L.p ell
            (Hex.centeredResiduePow L.p L.precision (z i j)) +
          ((L.p ^ ell : Nat) : ℤ) *
            Hex.psiCut L.p L.precision ell (z i j) := by
    exact Hex.centeredResiduePow_add_pow_mul_psiCut
      L.p L.precision ell (z i j) hpell
  have hpow :
      ((L.p ^ ell : Nat) : ℤ) *
          ((L.p ^ (L.precision - ell) : Nat) : ℤ) =
        ((L.p ^ L.precision : Nat) : ℤ) := by
    norm_cast
    rw [← pow_add, Nat.add_sub_of_le hcut]
  unfold fullAuxCoeff polCoeff
  change
    ((L.p ^ ell : Nat) : ℤ) *
          (Hex.Matrix.vecMul c L.basis)[Fin.natAdd L.factorCount j] +
        ∑ i : Fin L.factorCount,
          (Hex.Matrix.vecMul c L.basis)[Fin.castAdd L.coeffWidth i] *
            Hex.centeredResiduePow L.p ell
              (Hex.centeredResiduePow L.p L.precision (z i j)) =
      (∑ i : Fin L.factorCount,
          (Hex.Matrix.vecMul c L.basis)[Fin.castAdd L.coeffWidth i] *
            Hex.centeredResiduePow L.p L.precision (z i j)) +
        ((L.p ^ L.precision : Nat) : ℤ) * c[Fin.natAdd L.factorCount j]
  rw [htail]
  simp_rw [hfirst, hcld]
  dsimp only [ell] at hdecomp hpow ⊢
  have hperiod :
      ((L.p ^ L.cutThresholds.getD j.val 0 : Nat) : ℤ) *
          (Int.ofNat (L.p ^ (L.precision - L.cutThresholds.getD j.val 0)) *
            c[Fin.natAdd L.factorCount j]) =
        ((L.p ^ L.precision : Nat) : ℤ) * c[Fin.natAdd L.factorCount j] := by
    change
      ((L.p ^ L.cutThresholds.getD j.val 0 : Nat) : ℤ) *
          (((L.p ^ (L.precision - L.cutThresholds.getD j.val 0) : Nat) : ℤ) *
            c[Fin.natAdd L.factorCount j]) =
        ((L.p ^ L.precision : Nat) : ℤ) * c[Fin.natAdd L.factorCount j]
    rw [← mul_assoc, hpow]
  have hsumdecomp :
      (∑ i : Fin L.factorCount,
          c[Fin.castAdd L.coeffWidth i] *
            Hex.centeredResiduePow L.p L.precision (z i j)) =
        (∑ i : Fin L.factorCount,
          c[Fin.castAdd L.coeffWidth i] *
            Hex.centeredResiduePow L.p (L.cutThresholds.getD j.val 0)
              (Hex.centeredResiduePow L.p L.precision (z i j))) +
        ∑ i : Fin L.factorCount,
          ((L.p ^ L.cutThresholds.getD j.val 0 : Nat) : ℤ) *
            (c[Fin.castAdd L.coeffWidth i] *
              Hex.psiCut L.p L.precision
                (L.cutThresholds.getD j.val 0) (z i j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    calc
      c[Fin.castAdd L.coeffWidth i] *
          Hex.centeredResiduePow L.p L.precision (z i j) =
        c[Fin.castAdd L.coeffWidth i] *
          (Hex.centeredResiduePow L.p (L.cutThresholds.getD j.val 0)
              (Hex.centeredResiduePow L.p L.precision (z i j)) +
            ((L.p ^ L.cutThresholds.getD j.val 0 : Nat) : ℤ) *
                Hex.psiCut L.p L.precision
                (L.cutThresholds.getD j.val 0) (z i j)) := by
          exact congrArg
            (fun x : ℤ => c[Fin.castAdd L.coeffWidth i] * x)
            (hdecomp i)
      _ = c[Fin.castAdd L.coeffWidth i] *
              Hex.centeredResiduePow L.p (L.cutThresholds.getD j.val 0)
                (Hex.centeredResiduePow L.p L.precision (z i j)) +
            ((L.p ^ L.cutThresholds.getD j.val 0 : Nat) : ℤ) *
              (c[Fin.castAdd L.coeffWidth i] *
                Hex.psiCut L.p L.precision
                  (L.cutThresholds.getD j.val 0) (z i j)) := by ring
  rw [mul_add, Finset.mul_sum, hperiod]
  rw [hsumdecomp]
  ring

/-- Polynomial form of `fullAuxCoeff_vecMul`: the full-vector auxiliary is
coefficientwise congruent modulo `p^precision` to `POL(e)`. -/
theorem fullAux_congr_pol_vecMul
    (L : Hex.BhksLatticeBasis) (hL : BhksBlockForm L)
    (z : Fin L.factorCount → Fin L.coeffWidth → ℤ)
    (c : Vector ℤ (L.factorCount + L.coeffWidth))
    (hcut : ∀ j : Fin L.coeffWidth,
      L.cutThresholds.getD j.val 0 ≤ L.precision)
    (hp : 0 < L.p)
    (hcld : ∀ i : Fin L.factorCount, ∀ j : Fin L.coeffWidth,
      (L.cldRows.getD i.val #[]).getD j.val 0 =
        Hex.psiCut L.p L.precision (L.cutThresholds.getD j.val 0) (z i j)) :
    Hex.ZPoly.congr
      (fullAux L z (Hex.Matrix.vecMul c L.basis))
      (pol L z (Hex.Matrix.vecMul c L.basis))
      (L.p ^ L.precision) := by
  intro k
  by_cases hk : k < L.coeffWidth
  · let j : Fin L.coeffWidth := ⟨k, hk⟩
    rw [show k = j.val by rfl, fullAux_coeff, pol_coeff,
      fullAuxCoeff_vecMul L hL z c j (hcut j) hp (fun i => hcld i j)]
    simp
  · have hfull : (fullAux L z (Hex.Matrix.vecMul c L.basis)).coeff k = 0 := by
      rw [fullAux, Hex.DensePoly.coeff_ofCoeffs]
      simp [Array.getD, hk]
      change (0 : ℤ) = 0
      rfl
    have hpol : (pol L z (Hex.Matrix.vecMul c L.basis)).coeff k = 0 := by
      rw [pol, Hex.DensePoly.coeff_ofCoeffs]
      simp [Array.getD, hk]
      change (0 : ℤ) = 0
      rfl
    rw [hfull, hpol]
    simp

/-- Raw quotient coefficient used by the production all-coefficients CLD
lattice. -/
@[expose]
def cldResidue
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (i : Fin (Hex.bhksLatticeBasis f p a liftedFactors).factorCount)
    (j : Fin (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth) : ℤ :=
  (Hex.cldQuotientMod f (liftedFactors.getD i.val 1) p a).coeff j.val

/-- Production specialization of the corrected full-vector auxiliary. -/
@[expose]
def cldFullAux
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth)) : Hex.ZPoly :=
  fullAux (Hex.bhksLatticeBasis f p a liftedFactors)
    (cldResidue f p a liftedFactors) v

/--
Every coefficient of the corrected production auxiliary is bounded by the
`M` component of `Hex.bhksBound`, provided all coordinates of the full lattice
vector have magnitude at most `E`.

The period coordinate contributes one term bounded by `E*C`; each of the at
most `degree f` first-block coordinates contributes another such term.
-/
theorem cldFullAux_coeff_natAbs_le
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (E : Nat)
    (hp2 : 2 ≤ p) (hp500 : p ≤ 500)
    (hr : liftedFactors.size ≤ f.degree?.getD 0)
    (hv : ∀ x : Fin (liftedFactors.size + f.degree?.getD 0),
      v[x].natAbs ≤ E)
    (k : Nat) :
    ((cldFullAux f p a liftedFactors v).coeff k).natAbs ≤
      (f.degree?.getD 0 + 1) * E *
        (500 * (Hex.bhksColumnFloor f + 1)) := by
  classical
  let n := f.degree?.getD 0
  let r := liftedFactors.size
  let C := 500 * (Hex.bhksColumnFloor f + 1)
  by_cases hk : k < n
  · let j :
        Fin (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth :=
      ⟨k, by simpa only [Hex.bhksLatticeBasis, n] using hk⟩
    let ell := Hex.bhksCoeffCutThreshold p f k
    have hpell : 0 < p ^ ell := pow_pos (by omega) ell
    have hpow : p ^ ell ≤ C := by
      exact Hex.pow_bhksCoeffCutThreshold_le f hp2 hp500
        (by simpa only [n] using Nat.le_of_lt hk)
    have hres (i : Fin r) :
        (Hex.centeredResiduePow p ell
          (Hex.centeredResiduePow p a
            ((Hex.cldQuotientMod f
              (liftedFactors.getD i.val 1) p a).coeff k))).natAbs ≤ C := by
      have hcenter :=
        two_mul_natAbs_centeredResiduePow_le p ell
          (Hex.centeredResiduePow p a
            ((Hex.cldQuotientMod f
              (liftedFactors.getD i.val 1) p a).coeff k)) hpell
      exact Nat.le_trans (by omega) hpow
    have hperiod :
        (((p ^ ell : Nat) : ℤ) *
          v[Fin.natAdd r j]).natAbs ≤ E * C := by
      rw [Int.natAbs_mul]
      calc
        (p ^ ell) * v[Fin.natAdd r j].natAbs ≤ C * E :=
          Nat.mul_le_mul hpow (hv (Fin.natAdd r j))
        _ = E * C := Nat.mul_comm _ _
    have hterms (i : Fin r) :
        (v[Fin.castAdd n i] *
          Hex.centeredResiduePow p ell
            (Hex.centeredResiduePow p a
              ((Hex.cldQuotientMod f
                (liftedFactors.getD i.val 1) p a).coeff k))).natAbs ≤
          E * C := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hv (Fin.castAdd n i)) (hres i)
    have hsum :
        (∑ i : Fin r,
          v[Fin.castAdd n i] *
            Hex.centeredResiduePow p ell
              (Hex.centeredResiduePow p a
                ((Hex.cldQuotientMod f
                  (liftedFactors.getD i.val 1) p a).coeff k))).natAbs ≤
          r * (E * C) := by
      calc
        _ ≤ ∑ i : Fin r,
            (v[Fin.castAdd n i] *
              Hex.centeredResiduePow p ell
                (Hex.centeredResiduePow p a
                  ((Hex.cldQuotientMod f
                    (liftedFactors.getD i.val 1) p a).coeff k))).natAbs := by
              simpa using Int.natAbs_sum_le
                (Finset.univ : Finset (Fin r))
                (fun i =>
                  v[Fin.castAdd n i] *
                    Hex.centeredResiduePow p ell
                      (Hex.centeredResiduePow p a
                        ((Hex.cldQuotientMod f
                          (liftedFactors.getD i.val 1) p a).coeff k)))
        _ ≤ ∑ _i : Fin r, E * C :=
          Finset.sum_le_sum fun i _ => hterms i
        _ = r * (E * C) := by simp
    unfold cldFullAux
    rw [show k = j.val by rfl, fullAux_coeff]
    change
      (fullAuxCoeff (Hex.bhksLatticeBasis f p a liftedFactors)
          (cldResidue f p a liftedFactors) v j).natAbs ≤
        (n + 1) * E * C
    unfold fullAuxCoeff cldResidue
    simp only [Hex.bhksLatticeBasis]
    rw [Hex.bhksCutThresholds_getD_of_lt f p k (by simpa only [n] using hk)]
    change
      ((((p ^ ell : Nat) : ℤ) * v[Fin.natAdd r j] +
        ∑ i : Fin r,
          v[Fin.castAdd n i] *
            Hex.centeredResiduePow p ell
              (Hex.centeredResiduePow p a
                ((Hex.cldQuotientMod f
                  (liftedFactors.getD i.val 1) p a).coeff k))).natAbs) ≤
        (n + 1) * E * C
    calc
      _ ≤ E * C + r * (E * C) :=
        (Int.natAbs_add_le _ _).trans (Nat.add_le_add hperiod hsum)
      _ ≤ E * C + n * (E * C) := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right (E * C) (by simpa only [r, n] using hr)) _
      _ = (n + 1) * E * C := by ring
  · have hk' : ¬ k < f.degree?.getD 0 := by simpa only [n] using hk
    have hzero : (cldFullAux f p a liftedFactors v).coeff k = 0 := by
      unfold cldFullAux fullAux
      rw [Hex.DensePoly.coeff_ofCoeffs]
      simp only [Hex.bhksLatticeBasis]
      simp [Array.getD, hk']
      change (0 : ℤ) = 0
      rfl
    rw [hzero]
    simp

/-- The corrected full auxiliary stores exactly `degree f` coefficient slots. -/
theorem cldFullAux_natDegree_le
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth)) :
    (HexPolyZMathlib.toPolynomial
      (cldFullAux f p a liftedFactors v)).natDegree ≤
        f.degree?.getD 0 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [HexPolyZMathlib.coeff_toPolynomial]
  unfold cldFullAux fullAux
  rw [Hex.DensePoly.coeff_ofCoeffs]
  simp only [Hex.bhksLatticeBasis]
  have hk' : ¬ k < f.degree?.getD 0 := by omega
  simp only [Array.size_ofFn, Array.getD, hk', ↓reduceDIte]
  change (0 : ℤ) = 0
  rfl

/-- Production specialization of the full centred residue combination
`POL(e)`. -/
@[expose]
def cldPol
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth)) : Hex.ZPoly :=
  pol (Hex.bhksLatticeBasis f p a liftedFactors)
    (cldResidue f p a liftedFactors) v

/-- The same production CLD combination before coefficient centering. -/
@[expose]
def cldCombination
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth)) : Polynomial ℤ :=
  ∑ i : Fin liftedFactors.size,
    Polynomial.C v[Fin.castAdd (f.degree?.getD 0) i] *
      HexPolyZMathlib.toPolynomial
        (Hex.cldQuotientMod f (liftedFactors.getD i.val 1) p a)

/-- Coefficients of the uncentred CLD combination. -/
theorem cldCombination_coeff
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (j : Nat) :
    (cldCombination f p a liftedFactors v).coeff j =
      ∑ i : Fin liftedFactors.size,
        v[Fin.castAdd (f.degree?.getD 0) i] *
          (Hex.cldQuotientMod f
            (liftedFactors.getD i.val 1) p a).coeff j := by
  change
    (∑ i ∈ (Finset.univ : Finset (Fin liftedFactors.size)),
      Polynomial.C v[Fin.castAdd (f.degree?.getD 0) i] *
        HexPolyZMathlib.toPolynomial
          (Hex.cldQuotientMod f (liftedFactors.getD i.val 1) p a)).coeff j =
      ∑ i ∈ (Finset.univ : Finset (Fin liftedFactors.size)),
        v[Fin.castAdd (f.degree?.getD 0) i] *
          (Hex.cldQuotientMod f
            (liftedFactors.getD i.val 1) p a).coeff j
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Polynomial.coeff_C_mul, HexPolyZMathlib.coeff_toPolynomial]

/-- In-range coefficient formula for the centred production CLD combination. -/
theorem cldPol_coeff_of_lt
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (k : Nat) (hk : k < f.degree?.getD 0) :
    (cldPol f p a liftedFactors v).coeff k =
      ∑ i : Fin liftedFactors.size,
        v[Fin.castAdd (f.degree?.getD 0) i] *
          Hex.centeredResiduePow p a
            ((Hex.cldQuotientMod f
              (liftedFactors.getD i.val 1) p a).coeff k) := by
  unfold cldPol pol polCoeff cldResidue
  rw [Hex.DensePoly.coeff_ofCoeffs]
  simp only [Hex.bhksLatticeBasis]
  simp [Array.getD, hk]
  rfl

/-- Modulo the lift modulus, centering the stored CLD coefficients does not
change the polynomial combination. -/
theorem cldPol_map_eq_cldCombination
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (hf : 0 < f.degree?.getD 0)
    (hdeg : ∀ i : Fin liftedFactors.size,
      0 < (liftedFactors.getD i.val 1).degree?.getD 0) :
    (HexPolyZMathlib.toPolynomial (cldPol f p a liftedFactors v)).map
        (Int.castRingHom (ZMod (p ^ a))) =
      (cldCombination f p a liftedFactors v).map
        (Int.castRingHom (ZMod (p ^ a))) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map, Polynomial.coeff_map,
    HexPolyZMathlib.coeff_toPolynomial, cldCombination_coeff]
  by_cases hk : k < f.degree?.getD 0
  · rw [cldPol_coeff_of_lt f p a liftedFactors v k hk]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_mul, map_mul]
    congr 1
    change
      ((Hex.centeredResiduePow p a
        ((Hex.cldQuotientMod f
          (liftedFactors.getD i.val 1) p a).coeff k) : ℤ) :
          ZMod (p ^ a)) =
        (((Hex.cldQuotientMod f
          (liftedFactors.getD i.val 1) p a).coeff k : ℤ) :
          ZMod (p ^ a))
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa only [Hex.centeredResiduePow] using
      (Hex.self_sub_centeredModNat_dvd
        ((Hex.cldQuotientMod f
          (liftedFactors.getD i.val 1) p a).coeff k) (p ^ a))
  · have hk' : f.degree?.getD 0 ≤ k := Nat.le_of_not_gt hk
    have hleft :
        (cldPol f p a liftedFactors v).coeff k = 0 := by
      rw [cldPol, pol, Hex.DensePoly.coeff_ofCoeffs]
      simp only [Hex.bhksLatticeBasis]
      simp [Array.getD, hk]
      rfl
    rw [hleft, map_zero, map_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hsize :=
      cldQuotientMod_size_le_degree f
        (liftedFactors.getD i.val 1) p a hf (hdeg i)
    have hcoeff :
        (Hex.cldQuotientMod f
          (liftedFactors.getD i.val 1) p a).coeff k = 0 :=
      Hex.DensePoly.coeff_eq_zero_of_size_le _ (hsize.trans hk')
    rw [hcoeff, mul_zero, map_zero]

/-- If one first-block exponent is zero, the corresponding lifted local factor
divides the uncentred CLD combination modulo the lift modulus.  Pairwise
coprimality cancels every other lifted factor from its CLD syzygy. -/
theorem liftedFactor_dvd_cldCombination_of_coord_eq_zero
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (i₀ : Fin liftedFactors.size)
    (hk : 1 < p ^ a)
    (hfac : ∀ i : Fin liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic (liftedFactors.getD i.val 1) ∧
        0 < (liftedFactors.getD i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr f (liftedFactors.getD i.val 1 * h) (p ^ a))
    (hcop : ∀ j : Fin liftedFactors.size, j ≠ i₀ →
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD j.val 1)).map
            (Int.castRingHom (ZMod (p ^ a)))))
    (hzero : v[Fin.castAdd (f.degree?.getD 0) i₀] = 0) :
    (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i₀.val 1)).map
          (Int.castRingHom (ZMod (p ^ a))) ∣
      (cldCombination f p a liftedFactors v).map
        (Int.castRingHom (ZMod (p ^ a))) := by
  let φ := Int.castRingHom (ZMod (p ^ a))
  let q₀ := (HexPolyZMathlib.toPolynomial
    (liftedFactors.getD i₀.val 1)).map φ
  obtain ⟨h₀, _hmonic₀, _hdeg₀, hfac₀⟩ := hfac i₀
  have hmap₀ :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      f (liftedFactors.getD i₀.val 1 * h₀) (p ^ a) hfac₀
  have hq₀_dvd_f :
      q₀ ∣ (HexPolyZMathlib.toPolynomial f).map φ := by
    rw [hmap₀, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
    exact dvd_mul_right _ _
  unfold cldCombination
  rw [Polynomial.map_sum]
  apply Finset.dvd_sum
  intro j _
  by_cases hji : j = i₀
  · subst j
    simp [hzero]
  · obtain ⟨hj, hmonicj, hdegj, hfacj⟩ := hfac j
    have hcld := cldQuotientMod_congr_mul_derivative
      f (liftedFactors.getD j.val 1) hj p a hk hmonicj hdegj hfacj
    have hcldmap :=
      HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
        (liftedFactors.getD j.val 1 *
          Hex.cldQuotientMod f (liftedFactors.getD j.val 1) p a)
        (f * Hex.DensePoly.derivative (liftedFactors.getD j.val 1))
        (p ^ a) hcld
    have hproduct :
        q₀ ∣
          (HexPolyZMathlib.toPolynomial
            (liftedFactors.getD j.val 1)).map φ *
          (HexPolyZMathlib.toPolynomial
            (Hex.cldQuotientMod f
              (liftedFactors.getD j.val 1) p a)).map φ := by
      rw [← Polynomial.map_mul, ← HexPolyMathlib.toPolynomial_mul,
        hcldmap, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
      exact dvd_mul_of_dvd_left hq₀_dvd_f _
    have hquot :
        q₀ ∣
          (HexPolyZMathlib.toPolynomial
            (Hex.cldQuotientMod f
              (liftedFactors.getD j.val 1) p a)).map φ :=
      (hcop j hji).dvd_of_dvd_mul_left hproduct
    rw [Polynomial.map_mul]
    exact dvd_mul_of_dvd_right hquot _

/--
Conversely, if a lifted factor divides the CLD combination and is coprime to
its own CLD quotient modulo the lift modulus, then its first-block exponent
vanishes modulo that modulus.
-/
theorem coord_cast_eq_zero_of_liftedFactor_dvd_cldCombination
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (i₀ : Fin liftedFactors.size)
    (hk : 1 < p ^ a)
    (hfac : ∀ i : Fin liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic (liftedFactors.getD i.val 1) ∧
        0 < (liftedFactors.getD i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr f (liftedFactors.getD i.val 1 * h) (p ^ a))
    (hcop : ∀ j : Fin liftedFactors.size, j ≠ i₀ →
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD j.val 1)).map
            (Int.castRingHom (ZMod (p ^ a)))))
    (hown :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (Hex.cldQuotientMod f
            (liftedFactors.getD i₀.val 1) p a)).map
              (Int.castRingHom (ZMod (p ^ a)))))
    (hdvd :
      (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i₀.val 1)).map
          (Int.castRingHom (ZMod (p ^ a))) ∣
        (cldCombination f p a liftedFactors v).map
          (Int.castRingHom (ZMod (p ^ a)))) :
    ((v[Fin.castAdd (f.degree?.getD 0) i₀] : ℤ) : ZMod (p ^ a)) = 0 := by
  classical
  letI : Fact (1 < p ^ a) := ⟨hk⟩
  haveI : Nontrivial (ZMod (p ^ a)) := inferInstance
  let φ := Int.castRingHom (ZMod (p ^ a))
  let q₀ := (HexPolyZMathlib.toPolynomial
    (liftedFactors.getD i₀.val 1)).map φ
  let term : Fin liftedFactors.size → Polynomial (ZMod (p ^ a)) := fun j =>
    (Polynomial.C v[Fin.castAdd (f.degree?.getD 0) j] *
      HexPolyZMathlib.toPolynomial
        (Hex.cldQuotientMod f (liftedFactors.getD j.val 1) p a)).map φ
  have hother : ∀ j : Fin liftedFactors.size, j ≠ i₀ → q₀ ∣ term j := by
    intro j hji
    obtain ⟨hj, hmonicj, hdegj, hfacj⟩ := hfac j
    obtain ⟨h₀, _hmonic₀, _hdeg₀, hfac₀⟩ := hfac i₀
    have hmap₀ :=
      HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
        f (liftedFactors.getD i₀.val 1 * h₀) (p ^ a) hfac₀
    have hq₀_dvd_f :
        q₀ ∣ (HexPolyZMathlib.toPolynomial f).map φ := by
      rw [hmap₀, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
      exact dvd_mul_right _ _
    have hcld := cldQuotientMod_congr_mul_derivative
      f (liftedFactors.getD j.val 1) hj p a hk hmonicj hdegj hfacj
    have hcldmap :=
      HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
        (liftedFactors.getD j.val 1 *
          Hex.cldQuotientMod f (liftedFactors.getD j.val 1) p a)
        (f * Hex.DensePoly.derivative (liftedFactors.getD j.val 1))
        (p ^ a) hcld
    have hproduct :
        q₀ ∣
          (HexPolyZMathlib.toPolynomial
            (liftedFactors.getD j.val 1)).map φ *
          (HexPolyZMathlib.toPolynomial
            (Hex.cldQuotientMod f
              (liftedFactors.getD j.val 1) p a)).map φ := by
      rw [← Polynomial.map_mul, ← HexPolyMathlib.toPolynomial_mul,
        hcldmap, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
      exact dvd_mul_of_dvd_left hq₀_dvd_f _
    have hquot :
        q₀ ∣
          (HexPolyZMathlib.toPolynomial
            (Hex.cldQuotientMod f
              (liftedFactors.getD j.val 1) p a)).map φ :=
      (hcop j hji).dvd_of_dvd_mul_left hproduct
    unfold term
    rw [Polynomial.map_mul]
    exact dvd_mul_of_dvd_right hquot _
  have hrest :
      q₀ ∣ ∑ j ∈ (Finset.univ : Finset (Fin liftedFactors.size)).erase i₀,
        term j := by
    apply Finset.dvd_sum
    intro j hj
    exact hother j (Finset.ne_of_mem_erase hj)
  have hcombo :
      (cldCombination f p a liftedFactors v).map φ =
        ∑ j : Fin liftedFactors.size, term j := by
    unfold cldCombination term
    rw [Polynomial.map_sum]
  have hsplit :
      term i₀ +
          ∑ j ∈ (Finset.univ : Finset (Fin liftedFactors.size)).erase i₀,
            term j =
        ∑ j : Fin liftedFactors.size, term j :=
    Finset.add_sum_erase _ _ (Finset.mem_univ i₀)
  have hi : q₀ ∣ term i₀ := by
    have hsum : q₀ ∣ ∑ j : Fin liftedFactors.size, term j := by
      rw [← hcombo]
      exact hdvd
    exact ⟨(hsum.choose - hrest.choose), by
      rw [hsum.choose_spec, hrest.choose_spec] at hsplit
      linear_combination hsplit⟩
  have hconst :
      q₀ ∣ Polynomial.C
        ((v[Fin.castAdd (f.degree?.getD 0) i₀] : ℤ) : ZMod (p ^ a)) := by
    have hi' :
        q₀ ∣ Polynomial.C
            ((v[Fin.castAdd (f.degree?.getD 0) i₀] : ℤ) : ZMod (p ^ a)) *
          (HexPolyZMathlib.toPolynomial
            (Hex.cldQuotientMod f
              (liftedFactors.getD i₀.val 1) p a)).map φ := by
      simpa [term, Polynomial.map_mul] using hi
    exact hown.dvd_of_dvd_mul_right hi'
  obtain ⟨_h₀, hmonic₀, hdeg₀, _hfac₀⟩ := hfac i₀
  have hqmonic : q₀.Monic := by
    exact
      (HexHenselMathlib.toPolynomial_monic_of_dense_monic
        (liftedFactors.getD i₀.val 1) hmonic₀).map φ
  have hqdeg : 0 < q₀.natDegree := by
    have hqmonicZ :
        (HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).Monic :=
      HexHenselMathlib.toPolynomial_monic_of_dense_monic
        (liftedFactors.getD i₀.val 1) hmonic₀
    have hqdegZ :
        0 <
          (HexPolyZMathlib.toPolynomial
            (liftedFactors.getD i₀.val 1)).natDegree := by
      rwa [HexPolyMathlib.natDegree_toPolynomial]
    rw [show q₀ =
      (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i₀.val 1)).map φ from rfl,
      hqmonicZ.natDegree_map φ]
    exact hqdegZ
  by_contra hscalar
  have hCne :
      Polynomial.C
        ((v[Fin.castAdd (f.degree?.getD 0) i₀] : ℤ) : ZMod (p ^ a)) ≠ 0 := by
    exact Polynomial.C_ne_zero.mpr hscalar
  obtain ⟨s, hs⟩ := hconst
  have hsne : s ≠ 0 := by
    intro hs0
    rw [hs0, mul_zero] at hs
    exact hCne hs
  have hdegree := hqmonic.natDegree_mul' hsne
  rw [← hs, Polynomial.natDegree_C] at hdegree
  omega

/--
The CLD quotient belonging to one lifted factor is coprime to that factor
modulo the lift modulus.  The two substantive inputs are exactly the familiar
square-free factorisation properties: the factor is coprime to its complementary
factor `h`, and it is coprime to its own derivative.

Indeed the CLD congruence and `f ≡ q * h` give
`q * cld = q * (h * q')` after mapping modulo `p^a`.  Monicity cancels `q`;
the right-hand side is coprime to `q`.
-/
theorem isCoprime_cldQuotientMod
    (f q h : Hex.ZPoly) (p a : Nat)
    (hk : 1 < p ^ a)
    (hqmonic : Hex.DensePoly.Monic q)
    (hqdeg : 0 < q.degree?.getD 0)
    (hfac : Hex.ZPoly.congr f (q * h) (p ^ a))
    (hcop_h :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial q).map
          (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial h).map
          (Int.castRingHom (ZMod (p ^ a)))))
    (hcop_deriv :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial q).map
          (Int.castRingHom (ZMod (p ^ a))))
        (((HexPolyZMathlib.toPolynomial q).map
          (Int.castRingHom (ZMod (p ^ a)))).derivative)) :
    IsCoprime
      ((HexPolyZMathlib.toPolynomial q).map
        (Int.castRingHom (ZMod (p ^ a))))
      ((HexPolyZMathlib.toPolynomial
        (Hex.cldQuotientMod f q p a)).map
          (Int.castRingHom (ZMod (p ^ a)))) := by
  classical
  letI : Fact (1 < p ^ a) := ⟨hk⟩
  let φ := Int.castRingHom (ZMod (p ^ a))
  let Q := (HexPolyZMathlib.toPolynomial q).map φ
  let H := (HexPolyZMathlib.toPolynomial h).map φ
  let C := (HexPolyZMathlib.toPolynomial
    (Hex.cldQuotientMod f q p a)).map φ
  have hcld := cldQuotientMod_congr_mul_derivative
    f q h p a hk hqmonic hqdeg hfac
  have hcldmap :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      (q * Hex.cldQuotientMod f q p a)
      (f * Hex.DensePoly.derivative q) (p ^ a) hcld
  have hfacmap :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      f (q * h) (p ^ a) hfac
  have hmul : Q * C = Q * (H * Q.derivative) := by
    rw [show Q * C =
      (HexPolyZMathlib.toPolynomial
        (q * Hex.cldQuotientMod f q p a)).map φ by
          simp [Q, C, HexPolyMathlib.toPolynomial_mul]]
    rw [hcldmap, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul,
      hfacmap, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul,
      HexPolyMathlib.toPolynomial_derivative, Polynomial.derivative_map]
    simp only [Q, H]
    ring
  have hQmonic : Q.Monic :=
    (HexHenselMathlib.toPolynomial_monic_of_dense_monic q hqmonic).map φ
  have hcancel : C = H * Q.derivative := by
    have hz : Q * (C - H * Q.derivative) = 0 := by
      rw [mul_sub, hmul, sub_self]
    exact sub_eq_zero.mp (hQmonic.mul_right_eq_zero_iff.mp hz)
  change IsCoprime Q C
  rw [hcancel]
  exact hcop_h.mul_right hcop_deriv

/-- The corrected auxiliary polynomial for the production BHKS basis is
congruent to its full centred CLD-residue combination modulo `p^a`. -/
theorem cldFullAux_congr_cldPol
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (c : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (hp : 0 < p)
    (hcut : ∀ j : Fin (f.degree?.getD 0),
      Hex.bhksCoeffCutThreshold p f j.val ≤ a) :
    Hex.ZPoly.congr
      (cldFullAux f p a liftedFactors
        (Hex.Matrix.vecMul c (Hex.bhksLatticeBasis f p a liftedFactors).basis))
      (cldPol f p a liftedFactors
        (Hex.Matrix.vecMul c (Hex.bhksLatticeBasis f p a liftedFactors).basis))
      (p ^ a) := by
  apply fullAux_congr_pol_vecMul
  · exact bhksLatticeBasis_blockForm f p a liftedFactors
  · intro j
    simp only [Hex.bhksLatticeBasis]
    rw [Hex.bhksCutThresholds_getD_of_lt f p j.val j.isLt]
    exact hcut j
  · exact hp
  · intro i j
    have hi : i.val < liftedFactors.size := by
      simpa only [Hex.bhksLatticeBasis] using i.isLt
    have hj : j.val < f.degree?.getD 0 := by
      simpa only [Hex.bhksLatticeBasis] using j.isLt
    simp only [Hex.bhksLatticeBasis, cldResidue]
    have hrow :
        (liftedFactors.map (fun g => Hex.cldCoeffs f p a g)).getD i.val #[] =
          Hex.cldCoeffs f p a (liftedFactors.getD i.val 1) := by
      simp [Array.getD, hi]
    rw [hrow]
    rw [Hex.cldCoeffs_getD_of_lt f p a _ j.val hj,
      Hex.bhksCutThresholds_getD_of_lt f p j.val hj]

/-- A zero first-block coordinate of an actual BHKS lattice vector makes the
corresponding lifted factor divide the corrected full auxiliary modulo the
lift modulus. -/
theorem liftedFactor_dvd_cldFullAux
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (i₀ : Fin liftedFactors.size)
    (hf : 0 < f.degree?.getD 0)
    (hk : 1 < p ^ a)
    (hp : 0 < p)
    (hcut : ∀ j : Fin (f.degree?.getD 0),
      Hex.bhksCoeffCutThreshold p f j.val ≤ a)
    (hfac : ∀ i : Fin liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic (liftedFactors.getD i.val 1) ∧
        0 < (liftedFactors.getD i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr f (liftedFactors.getD i.val 1 * h) (p ^ a))
    (hcop : ∀ j : Fin liftedFactors.size, j ≠ i₀ →
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD j.val 1)).map
            (Int.castRingHom (ZMod (p ^ a)))))
    (hv : Hex.Matrix.memLattice
      (Hex.bhksLatticeBasis f p a liftedFactors).basis v)
    (hzero : v[Fin.castAdd (f.degree?.getD 0) i₀] = 0) :
    (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i₀.val 1)).map
          (Int.castRingHom (ZMod (p ^ a))) ∣
      (HexPolyZMathlib.toPolynomial
        (cldFullAux f p a liftedFactors v)).map
          (Int.castRingHom (ZMod (p ^ a))) := by
  obtain ⟨c, hc⟩ := hv
  have haux := HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
    (cldFullAux f p a liftedFactors
      (Hex.Matrix.vecMul c (Hex.bhksLatticeBasis f p a liftedFactors).basis))
    (cldPol f p a liftedFactors
      (Hex.Matrix.vecMul c (Hex.bhksLatticeBasis f p a liftedFactors).basis))
    (p ^ a) (cldFullAux_congr_cldPol f p a liftedFactors c hp hcut)
  have hpol := cldPol_map_eq_cldCombination
    f p a liftedFactors v hf (fun i => (hfac i).choose_spec.2.1)
  have hdvd := liftedFactor_dvd_cldCombination_of_coord_eq_zero
    f p a liftedFactors v i₀ hk hfac hcop hzero
  rw [hc] at haux
  rw [haux, hpol]
  exact hdvd

/-- Divisibility of the corrected full auxiliary by a lifted factor forces the
corresponding first-block coordinate to vanish modulo the lift modulus. -/
theorem coord_cast_eq_zero_of_liftedFactor_dvd_cldFullAux
    (f : Hex.ZPoly) (p a : Nat) (liftedFactors : Array Hex.ZPoly)
    (v : Vector ℤ
      ((Hex.bhksLatticeBasis f p a liftedFactors).factorCount +
        (Hex.bhksLatticeBasis f p a liftedFactors).coeffWidth))
    (i₀ : Fin liftedFactors.size)
    (hf : 0 < f.degree?.getD 0)
    (hk : 1 < p ^ a)
    (hp : 0 < p)
    (hcut : ∀ j : Fin (f.degree?.getD 0),
      Hex.bhksCoeffCutThreshold p f j.val ≤ a)
    (hfac : ∀ i : Fin liftedFactors.size,
      ∃ h : Hex.ZPoly,
        Hex.DensePoly.Monic (liftedFactors.getD i.val 1) ∧
        0 < (liftedFactors.getD i.val 1).degree?.getD 0 ∧
        Hex.ZPoly.congr f (liftedFactors.getD i.val 1 * h) (p ^ a))
    (hcop : ∀ j : Fin liftedFactors.size, j ≠ i₀ →
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD j.val 1)).map
            (Int.castRingHom (ZMod (p ^ a)))))
    (hown :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial
          (liftedFactors.getD i₀.val 1)).map
            (Int.castRingHom (ZMod (p ^ a))))
        ((HexPolyZMathlib.toPolynomial
          (Hex.cldQuotientMod f
            (liftedFactors.getD i₀.val 1) p a)).map
              (Int.castRingHom (ZMod (p ^ a)))))
    (hv : Hex.Matrix.memLattice
      (Hex.bhksLatticeBasis f p a liftedFactors).basis v)
    (hdvd :
      (HexPolyZMathlib.toPolynomial
        (liftedFactors.getD i₀.val 1)).map
          (Int.castRingHom (ZMod (p ^ a))) ∣
        (HexPolyZMathlib.toPolynomial
          (cldFullAux f p a liftedFactors v)).map
            (Int.castRingHom (ZMod (p ^ a)))) :
    ((v[Fin.castAdd (f.degree?.getD 0) i₀] : ℤ) : ZMod (p ^ a)) = 0 := by
  obtain ⟨c, hc⟩ := hv
  have haux := HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
    (cldFullAux f p a liftedFactors
      (Hex.Matrix.vecMul c (Hex.bhksLatticeBasis f p a liftedFactors).basis))
    (cldPol f p a liftedFactors
      (Hex.Matrix.vecMul c (Hex.bhksLatticeBasis f p a liftedFactors).basis))
    (p ^ a) (cldFullAux_congr_cldPol f p a liftedFactors c hp hcut)
  have hpol := cldPol_map_eq_cldCombination
    f p a liftedFactors v hf (fun i => (hfac i).choose_spec.2.1)
  rw [hc] at haux
  rw [haux, hpol] at hdvd
  exact coord_cast_eq_zero_of_liftedFactor_dvd_cldCombination
    f p a liftedFactors v i₀ hk hfac hcop hown hdvd

end BHKS

end

end HexBerlekampZassenhausMathlib
