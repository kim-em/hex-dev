/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.Irreducibility
public import HexBerlekamp.Factor
public import HexPolyFp.Compose
public import HexPolyFp.Quotient
public import HexPolyFp.QuotientFrobenius
public import HexArith.Nat.Pow
public import HexBerlekamp.RabinSoundness.KernelWitness
import all HexBerlekamp.RabinSoundness.RabinCore
import all HexBerlekamp.RabinSoundness.RabinShape
import all HexBerlekamp.RabinSoundness.KernelWitness

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Project-side soundness of `Berlekamp.rabinTest` against
`FpPoly.Irreducible`. The CRT candidates, foundational lemmas, product
identity, and kernel-witness infrastructure live in the
`HexBerlekamp.RabinSoundness.*` submodules; this module assembles the
Berlekamp completeness composition (`berlekampFactor_*`).
-/
namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
/-! ### Berlekamp completeness composition

Combining the CRT-produced kernel polynomial with the matrix-kernel iff
yields the algebraic half of Berlekamp completeness: if no fixed-space
kernel witness admits a Berlekamp split, the square-free monic input is
irreducible. -/

omit [ZMod64.PrimeModulus p] in
/-- Foldl of zero terms over `ZMod64 p` starting from `0` stays at `0`. -/
private theorem foldl_add_eq_zero_of_terms_zero
    {α : Type _} (xs : List α) (g : α → ZMod64 p)
    (hg : ∀ x ∈ xs, g x = 0) :
    xs.foldl (fun acc x => acc + g x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : g x = 0 := hg x (by simp)
      have hxs : ∀ y ∈ xs, g y = 0 := fun y hy => hg y (List.mem_cons_of_mem _ hy)
      have hzero_add : (0 : ZMod64 p) + g x = 0 := by rw [hx]; grind
      rw [hzero_add]
      exact ih hxs

/-- Relate a `nullspaceBasisMatrix` entry to the corresponding basis polynomial
coefficient. The `(i, k)` entry of the basis matrix equals the `i`-th coefficient
of the `k`-th basis polynomial, for `i < basisSize f`. -/
private theorem nullspaceBasisMatrix_entry_eq_basis_coeff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (k : Fin (basisSize f -
      Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)))
    (i : Nat) (hi : i < basisSize f) :
    ((Matrix.nullspaceBasisMatrix (fixedSpaceMatrix f hmonic))[i]'hi)[k.val]'k.isLt =
      ((fixedSpaceKernel f hmonic).get k).coeff i := by
  -- Establish: ((fixedSpaceKernel f hmonic).get k).coeff i = coeffVector f (basis k) [i]
  have hker_coeff :
      ((fixedSpaceKernel f hmonic).get k).coeff i =
        (coeffVector f ((fixedSpaceKernel f hmonic).get k))[i]'hi := by
    unfold coeffVector
    rw [Vector.getElem_ofFn]
  -- coeffVector f (basis k) = (fixedSpaceKernelVectors f hmonic).get k
  have hker_get : (fixedSpaceKernel f hmonic).get k =
      vectorToPoly ((fixedSpaceKernelVectors f hmonic).get k) := by
    unfold fixedSpaceKernel
    exact Vector.getElem_ofFn _
  have hker_eq :
      coeffVector f ((fixedSpaceKernel f hmonic).get k) =
        (fixedSpaceKernelVectors f hmonic).get k := by
    rw [hker_get, coeffVector_vectorToPoly]
  rw [hker_coeff, hker_eq]
  -- Goal: M'[i][k.val] = ((fixedSpaceKernelVectors f hmonic).get k)[i]
  unfold fixedSpaceKernelVectors
  rw [← Matrix.nullspaceBasisMatrix_col]
  simp [Matrix.col]

/--
**Algebraic half of Berlekamp completeness for square-free inputs.**

For a monic square-free `f ∈ F_p[x]`, if every fixed-space kernel witness fails
to produce a Berlekamp split (`kernelWitnessSplit? f w = none`), then `f` is
irreducible.

The proof goes by contradiction: a nontrivial factorization `f = a₀ * b₀`
yields a monic irreducible factor `g ∣ a₀` and a monic cofactor `b' = f / g`
of positive degree. The reduced CRT zero-one witness from
`exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split` produces
a polynomial `h` of size `≤ basisSize f` with `f ∣ linearPow h p - h` and
`h` nonconstant modulo `f`. The fixed-space iff
(`isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self`) makes `h` an
algebraic kernel polynomial; the spanning lemma
`fixedSpaceKernelPolynomial_coeffVector_complete` decomposes its coefficient
vector as a linear combination of basis polynomials. Because `h` is not a
constant, at least one basis polynomial `w` must be nonconstant; the iff in
the matrix→algebraic direction (`fixedSpaceKernel_sound`) and
`dvd_primeFieldProduct_witness_of_dvd_linearPow_sub_self` lift `w` to a
witness of `f ∣ Π_c (w − C c)`. The executable split surface
`exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree` then
produces `kernelWitnessSplit? f w = some _`, contradicting `hno_split`.
-/
theorem irreducible_of_no_kernelWitnessSplit_squareFree
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hno_split : ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
      kernelWitnessSplit? f w = none) :
    FpPoly.Irreducible f := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  -- f ≠ 0 from monicity.
  have hf_ne_zero : f ≠ 0 := by
    intro hzero
    have hlead : f.leadingCoeff = 1 := hmonic
    rw [hzero] at hlead
    have hlead_zero : (0 : FpPoly p).leadingCoeff = 0 := by
      exact DensePoly.leadingCoeff_zero
    rw [hlead_zero] at hlead
    exact zmod64_one_ne_zero_local hlead.symm
  refine ⟨hf_ne_zero, ?_⟩
  intro a₀ b₀ hab
  by_cases ha₀_unit : a₀.degree? = some 0
  · exact Or.inl ha₀_unit
  refine Or.inr ?_
  by_cases hb₀_unit : b₀.degree? = some 0
  · exact hb₀_unit
  exfalso
  -- Both factors are nonconstant.
  have ha₀_ne_zero : a₀ ≠ 0 := factor_ne_zero_of_ne_zero hab hf_ne_zero
  have hb₀_ne_zero : b₀ ≠ 0 := by
    have hba : b₀ * a₀ = f := by rw [FpPoly.mul_comm]; exact hab
    exact factor_ne_zero_of_ne_zero hba hf_ne_zero
  have ha₀_pos : 0 < a₀.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit ha₀_ne_zero ha₀_unit
  have hb₀_pos : 0 < b₀.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit hb₀_ne_zero hb₀_unit
  have ha₀_lt_f : a₀.degree?.getD 0 < basisSize f :=
    factor_degree_lt_basisSize hab ha₀_ne_zero hb₀_pos
  -- Extract a monic irreducible factor `g` of `a₀`.
  obtain ⟨g, _hg_irr, hg_monic, hg_dvd_a₀, hg_deg_pos, hg_deg_le_a₀⟩ :=
    exists_monic_irreducible_factor_of_factor hmonic hab ha₀_pos
  -- `g ∣ f` via `g ∣ a₀ ∣ f`.
  have hg_dvd_f : g ∣ f := by
    rcases hg_dvd_a₀ with ⟨r, hr⟩
    refine ⟨r * b₀, ?_⟩
    calc f = a₀ * b₀ := hab.symm
      _ = (g * r) * b₀ := by rw [hr]
      _ = g * (r * b₀) := FpPoly.mul_assoc g r b₀
  have hg_ne_zero : g ≠ 0 := ne_zero_of_pos_degree hg_deg_pos
  -- Cofactor `b' := f / g` with `g * b' = f`.
  let b' : FpPoly p := f / g
  have hf_eq : g * b' = f := (fp_eq_mul_div_of_dvd hg_dvd_f).symm
  have hb'_ne_zero : b' ≠ 0 := by
    intro hzero
    rw [hzero, FpPoly.mul_zero] at hf_eq
    exact hf_ne_zero hf_eq.symm
  -- `b'` is monic: leading coefficient is forced by `g * b' = f` and both `g, f` monic.
  have hb'_monic : DensePoly.Monic b' := by
    have hlead : DensePoly.leadingCoeff f =
        DensePoly.leadingCoeff g * DensePoly.leadingCoeff b' := by
      rw [← hf_eq]
      exact FpPoly.leadingCoeff_mul g b' hg_ne_zero hb'_ne_zero
    have hf_one : DensePoly.leadingCoeff f = 1 := hmonic
    have hg_one : DensePoly.leadingCoeff g = 1 := hg_monic
    unfold DensePoly.Monic
    rw [hg_one, hf_one] at hlead
    have hone_mul : (1 : ZMod64 p) * DensePoly.leadingCoeff b' =
        DensePoly.leadingCoeff b' := by grind
    rw [hone_mul] at hlead
    exact hlead.symm
  -- `b'` has positive degree.
  have hg_lt_f : g.degree?.getD 0 < basisSize f :=
    Nat.lt_of_le_of_lt hg_deg_le_a₀ ha₀_lt_f
  have hb'_pos : 0 < b'.degree?.getD 0 := by
    have hdeg_eq : (g * b').degree?.getD 0 =
        g.degree?.getD 0 + b'.degree?.getD 0 :=
      FpPoly.degree?_mul_eq_add_degree? g b' hg_ne_zero hb'_ne_zero
    rw [hf_eq] at hdeg_eq
    unfold basisSize at hg_lt_f
    omega
  -- Square-freeness on `g * b' = f`.
  have hsf' : ∀ d, d ∣ (g * b') → d ∣ DensePoly.derivative (g * b') →
      isUnitPolynomial d = true := by
    rw [hf_eq]; exact hsquareFree
  -- Reduced zero-one CRT witness `h`.
  obtain ⟨h, h_dvd, h_nonconst, h_size⟩ :=
    exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split
      g b' hg_monic hb'_monic hg_deg_pos hb'_pos hsf'
  rw [hf_eq] at h_dvd h_nonconst h_size
  -- Size bound: `h.size ≤ basisSize f`.
  have hh_size_le : h.size ≤ basisSize f := h_size
  -- `h` is a fixed-space kernel polynomial.
  have hh_kernel : IsFixedSpaceKernelPolynomial f hmonic h := by
    rw [isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self f hmonic h hh_size_le]
    exact h_dvd
  -- Span as linear combination of basis vectors.
  obtain ⟨c_coeff, hc_eq⟩ :=
    fixedSpaceKernelPolynomial_coeffVector_complete f hmonic h hh_kernel
  -- Notation for the basis matrix.
  let M := fixedSpaceMatrix f hmonic
  -- Set kernel dimension shorthand.
  let ndim := basisSize f - Matrix.rowReduce_rank M
  -- Extract a nonconstant basis polynomial, contradicting `hno_split`.
  -- Strategy: if every basis polynomial is a constant, then h is a constant,
  -- contradicting h_nonconst applied to h.coeff 0.
  have hbasis_size_le : ∀ k : Fin ndim,
      ((fixedSpaceKernel f hmonic).get k).size ≤ basisSize f := by
    intro k
    have hker_eq :
        (fixedSpaceKernel f hmonic).get k =
          vectorToPoly ((fixedSpaceKernelVectors f hmonic).get k) := by
      unfold fixedSpaceKernel
      exact Vector.getElem_ofFn _
    rw [hker_eq]
    unfold vectorToPoly
    have hle :
        (FpPoly.ofCoeffs
            ((fixedSpaceKernelVectors f hmonic).get k).toArray).size ≤
          ((fixedSpaceKernelVectors f hmonic).get k).toArray.size :=
      DensePoly.size_ofCoeffs_le _
    have hsz :
        ((fixedSpaceKernelVectors f hmonic).get k).toArray.size = basisSize f :=
      ((fixedSpaceKernelVectors f hmonic).get k).size_toArray
    omega
  by_cases hall_const :
      ∀ k : Fin ndim, ((fixedSpaceKernel f hmonic).get k).size ≤ 1
  · -- Every basis polynomial is a constant. Show `h` is a constant.
    -- Specifically, prove `h.coeff i = 0` for all `i ≥ 1`.
    have hh_coeff_zero : ∀ i, 1 ≤ i → h.coeff i = 0 := by
      intro i hi
      by_cases hi_lt : i < basisSize f
      · -- Use hc_eq to extract h.coeff i as a linear combination.
        have hi_fin : i < basisSize f := hi_lt
        have hget :
            (Matrix.mulVec (Matrix.nullspaceBasisMatrix M) c_coeff)[i]'hi_fin =
              (coeffVector f h)[i]'hi_fin :=
          congrArg (fun v : Vector (ZMod64 p) (basisSize f) => v[i]'hi_fin) hc_eq
        -- Right-hand side is h.coeff i.
        have hrhs : (coeffVector f h)[i]'hi_fin = h.coeff i := by
          unfold coeffVector
          rw [Vector.getElem_ofFn hi_fin]
        -- Left-hand side expands to a foldl.
        have hlhs :
            (Matrix.mulVec (Matrix.nullspaceBasisMatrix M) c_coeff)[i]'hi_fin =
              (List.finRange ndim).foldl
                (fun acc k => acc +
                  ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
                    c_coeff[k.val]'k.isLt) 0 := by
          unfold Matrix.mulVec Vector.dotProduct Matrix.row
          rw [Vector.getElem_ofFn hi_fin]
          rfl
        rw [hlhs] at hget
        rw [hrhs] at hget
        -- All terms in the foldl are 0 because basis polynomials have size ≤ 1.
        have hzero_terms : ∀ k ∈ List.finRange ndim,
            ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
                c_coeff[k.val]'k.isLt = 0 := by
          intro k _hk
          rw [nullspaceBasisMatrix_entry_eq_basis_coeff f hmonic k i hi_fin]
          have hk_const : ((fixedSpaceKernel f hmonic).get k).size ≤ 1 := hall_const k
          have hcoeff_zero : ((fixedSpaceKernel f hmonic).get k).coeff i = 0 :=
            DensePoly.coeff_eq_zero_of_size_le _ (by omega)
          rw [hcoeff_zero]
          grind
        have hfoldl_zero :
            (List.finRange ndim).foldl
              (fun acc k => acc +
                ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
                  c_coeff[k.val]'k.isLt) 0 = 0 :=
          foldl_add_eq_zero_of_terms_zero (List.finRange ndim)
            (fun k => ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
              c_coeff[k.val]'k.isLt)
            hzero_terms
        rw [hfoldl_zero] at hget
        exact hget.symm
      · have hi_ge : basisSize f ≤ i := Nat.le_of_not_lt hi_lt
        exact DensePoly.coeff_eq_zero_of_size_le _ (Nat.le_trans hh_size_le hi_ge)
    -- `h = DensePoly.C d` for a fresh `d`.
    have hh_eq_C : ∃ d : ZMod64 p, h = DensePoly.C d := by
      refine ⟨h.coeff 0, ?_⟩
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_C]
      cases i with
      | zero => simp
      | succ i =>
          rw [hh_coeff_zero (i + 1) (by omega)]
          simp; rfl
    obtain ⟨d, hd⟩ := hh_eq_C
    -- Then `f ∣ h - C d` holds (the difference is 0).
    apply h_nonconst d
    refine ⟨0, ?_⟩
    rw [hd, FpPoly.sub_self, FpPoly.mul_zero]
  · -- Some basis polynomial is nonconstant. Use it to contradict hno_split.
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hall_const
    let w : FpPoly p := (fixedSpaceKernel f hmonic).get k
    have hw_size_ge : 1 < w.size := Nat.lt_of_not_le hk
    -- w is in the kernel toList.
    have hw_mem : w ∈ (fixedSpaceKernel f hmonic).toList := by
      have hk_lt :
          k.val < (fixedSpaceKernel f hmonic).toList.length := by
        rw [Vector.length_toList]
        exact k.isLt
      have hget :
          (fixedSpaceKernel f hmonic).toList[k.val]'hk_lt = w := by
        rw [Vector.getElem_toList]
        rfl
      rw [← hget]
      exact List.getElem_mem hk_lt
    -- w is a kernel polynomial.
    have hw_kernel : IsFixedSpaceKernelPolynomial f hmonic w :=
      fixedSpaceKernel_sound f hmonic k
    -- w has size ≤ basisSize f.
    have hw_size_le : w.size ≤ basisSize f := hbasis_size_le k
    -- Hence f ∣ linearPow w p - w.
    have hw_dvd : f ∣ FpPoly.linearPow w p - w := by
      rw [isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self
        f hmonic w hw_size_le] at hw_kernel
      exact hw_kernel
    -- Apply prime-field product identity.
    have hw_prod :
        f ∣ (ZMod64.values p).foldl
          (fun acc c => acc * (w - FpPoly.C c)) 1 :=
      dvd_primeFieldProduct_witness_of_dvd_linearPow_sub_self hw_dvd
    -- w is not congruent to any constant modulo f.
    have hbasis_pos : 0 < basisSize f := by
      have hgpos : 0 < g.degree?.getD 0 := hg_deg_pos
      omega
    have hw_nonconst : ∀ c : ZMod64 p, ¬ (f ∣ (w - FpPoly.C c)) := by
      intro c hc
      -- (w - C c) ≠ 0 because its leading coefficient at index (w.size - 1) is nonzero.
      have hw_lead : w.coeff (w.size - 1) ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size w (by omega)
      have hC_coeff_high : (FpPoly.C c).coeff (w.size - 1) = 0 := by
        change (DensePoly.C c).coeff (w.size - 1) = 0
        rw [DensePoly.coeff_C]
        have : w.size - 1 ≠ 0 := by omega
        simp [this]; rfl
      have hsub_at_top : (w - FpPoly.C c).coeff (w.size - 1) =
          w.coeff (w.size - 1) - (FpPoly.C c).coeff (w.size - 1) := by
        rw [DensePoly.coeff_sub_ring]
      have hsub_top_ne : (w - FpPoly.C c).coeff (w.size - 1) ≠ 0 := by
        rw [hsub_at_top, hC_coeff_high]
        intro hzero
        apply hw_lead
        have hsubzero : w.coeff (w.size - 1) - (0 : ZMod64 p) =
            w.coeff (w.size - 1) := by grind
        rw [hsubzero] at hzero
        exact hzero
      have hwc_ne_zero : w - FpPoly.C c ≠ 0 := by
        intro hwc_zero
        apply hsub_top_ne
        rw [hwc_zero]
        change (0 : FpPoly p).coeff (w.size - 1) = 0
        rw [DensePoly.coeff_zero]
        rfl
      -- (w - C c).size ≤ basisSize f via coefficient analysis above basisSize f.
      have hwc_size_le : (w - FpPoly.C c).size ≤ basisSize f := by
        apply Classical.byContradiction
        intro hgt
        have hgt : basisSize f < (w - FpPoly.C c).size := Nat.lt_of_not_le hgt
        have hwc_pos : 0 < (w - FpPoly.C c).size := by omega
        have hidx_ge : basisSize f ≤ (w - FpPoly.C c).size - 1 := by omega
        have hlast_ne :
            (w - FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) ≠ 0 :=
          DensePoly.coeff_last_ne_zero_of_pos_size _ hwc_pos
        have hw_zero_top :
            w.coeff ((w - FpPoly.C c).size - 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le _ (Nat.le_trans hw_size_le hidx_ge)
        have hC_zero_top :
            (FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) = 0 := by
          change (DensePoly.C c).coeff ((w - FpPoly.C c).size - 1) = 0
          rw [DensePoly.coeff_C]
          have hne : (w - FpPoly.C c).size - 1 ≠ 0 := by omega
          simp [hne]; rfl
        have hsub_top :
            (w - FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) =
              w.coeff ((w - FpPoly.C c).size - 1) -
                (FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) := by
          rw [DensePoly.coeff_sub_ring]
        rw [hsub_top, hw_zero_top, hC_zero_top] at hlast_ne
        apply hlast_ne
        change (0 : ZMod64 p) - (0 : ZMod64 p) = 0
        grind
      -- (w - C c).degree < basisSize f, so (w - C c) % f = (w - C c).
      have hwc_deg_lt : (w - FpPoly.C c).degree?.getD 0 < basisSize f := by
        by_cases hsize : (w - FpPoly.C c).size = 0
        · -- (w - C c) = 0, contradicting hwc_ne_zero.
          exfalso
          apply hwc_ne_zero
          apply DensePoly.ext_coeff
          intro i
          rw [DensePoly.coeff_zero]
          exact DensePoly.coeff_eq_zero_of_size_le _ (by omega)
        · have hsize_pos : 0 < (w - FpPoly.C c).size := Nat.pos_of_ne_zero hsize
          have hdeg : (w - FpPoly.C c).degree? =
              some ((w - FpPoly.C c).size - 1) := by
            unfold DensePoly.degree?
            simp [hsize]
          rw [hdeg]
          simp
          omega
      have hwc_mod_self : (w - FpPoly.C c) % f = (w - FpPoly.C c) := by
        apply DensePoly.mod_eq_self_of_degree_lt
        change _ < basisSize f
        exact hwc_deg_lt
      have hwc_mod_zero : (w - FpPoly.C c) % f = 0 :=
        DensePoly.mod_eq_zero_of_dvd _ _ hc
      rw [hwc_mod_self] at hwc_mod_zero
      exact hwc_ne_zero hwc_mod_zero
    -- Now apply the executable split.
    have hf_pos : 0 < f.degree?.getD 0 := by
      have : 0 < basisSize f := hbasis_pos
      unfold basisSize at this
      exact this
    obtain ⟨r, hsplit⟩ :=
      exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree
        hf_pos hw_prod hw_nonconst
    have hno_w : kernelWitnessSplit? f w = none := hno_split w hw_mem
    rw [hno_w] at hsplit
    nomatch hsplit

/-! ### Divisor-generalized Berlekamp completeness

The single-polynomial theorem above ranges `hno_split` over `f`'s own kernel.
The executable `berlekampFactor` (`HexBerlekamp/Factor.lean`) computes the
witness set once as `f`'s kernel and splits *every* returned factor `g` with it,
so the per-factor soundness obligation is the divisor-generalized form: `g ∣ f`,
square-free `f`, no `f`-kernel witness splits `g`, conclude `g` irreducible. The
new content is a CRT lift of a `g`-kernel witness to an `f`-kernel witness that
stays nonconstant mod `g`, plus a span-mod-`g` argument moving the nonconstancy
to an `f`-basis element. -/

omit [ZMod64.PrimeModulus p] in
/-- `C a * C b = C (a * b)` for `FpPoly`. -/
private theorem C_mul_C (a b : ZMod64 p) :
    (DensePoly.C a : FpPoly p) * DensePoly.C b = DensePoly.C (a * b) := by
  rw [FpPoly.C_mul_eq_scale]
  rw [show (DensePoly.C b : FpPoly p) = DensePoly.scale b (1 : FpPoly p) from
        (FpPoly.scale_one_poly b).symm]
  rw [FpPoly.scale_scale, FpPoly.scale_one_poly]

omit [ZMod64.PrimeModulus p] in
/-- `C a + C b = C (a + b)` for `FpPoly`. -/
private theorem C_add_C (a b : ZMod64 p) :
    (DensePoly.C a : FpPoly p) + DensePoly.C b = DensePoly.C (a + b) := by
  apply DensePoly.ext_coeff
  intro i
  have h0 : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_add (DensePoly.C a) (DensePoly.C b) i h0,
      DensePoly.coeff_C, DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, if_neg hi]; exact h0

omit [ZMod64.PrimeModulus p] in
/-- The `i`-th coefficient of `q * C c` is `q.coeff i * c`. -/
private theorem coeff_mul_C (q : FpPoly p) (c : ZMod64 p) (i : Nat) :
    (q * DensePoly.C c).coeff i = q.coeff i * c := by
  rw [FpPoly.mul_comm, FpPoly.C_mul_eq_scale]
  have h_zero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ h_zero]
  grind

omit [ZMod64.PrimeModulus p] in
/-- `(a - b) + b = a` for `FpPoly`. -/
private theorem sub_add_cancel_poly (a b : FpPoly p) : a - b + b = a := by
  rw [FpPoly.sub_eq_add_neg, FpPoly.add_assoc, FpPoly.add_left_neg, FpPoly.add_zero]

omit [ZMod64.PrimeModulus p] in
/-- `(x + y) - y = x` for `FpPoly`. -/
private theorem add_sub_cancel_poly (x y : FpPoly p) : x + y - y = x := by
  rw [FpPoly.sub_eq_add_neg, FpPoly.add_assoc, FpPoly.add_right_neg, FpPoly.add_zero]

omit [ZMod64.PrimeModulus p] in
/-- Left distributivity over subtraction for `FpPoly`. -/
private theorem mul_sub_poly (z a b : FpPoly p) :
    z * (a - b) = z * a - z * b := by
  have key : z * a = z * (a - b) + z * b := by
    have h := FpPoly.left_distrib z (a - b) b
    rw [sub_add_cancel_poly a b] at h
    exact h
  rw [key, add_sub_cancel_poly]

omit [ZMod64.PrimeModulus p] in
/-- Right distributivity over subtraction for `FpPoly`. -/
private theorem sub_mul_poly (a b z : FpPoly p) :
    (a - b) * z = a * z - b * z := by
  rw [FpPoly.mul_comm (a - b) z, mul_sub_poly z a b, FpPoly.mul_comm z a,
      FpPoly.mul_comm z b]

omit [ZMod64.PrimeModulus p] in
/-- Polynomial congruence modulo `m` is preserved by addition. -/
private theorem congr_add_of_congr {m a b c d : FpPoly p}
    (hab : DensePoly.Congr a b m) (hcd : DensePoly.Congr c d m) :
    DensePoly.Congr (a + c) (b + d) m := by
  have h0 : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  have heq : (a + c) - (b + d) = (a - b) + (c - d) := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_sub_ring,
        DensePoly.coeff_add a c i h0, DensePoly.coeff_add b d i h0,
        DensePoly.coeff_add (a - b) (c - d) i h0,
        DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring]
    grind
  rw [DensePoly.Congr, heq]
  exact DensePoly.dvd_add_poly hab hcd

omit [ZMod64.PrimeModulus p] in
/-- Polynomial congruence modulo `m` is preserved by right multiplication. -/
private theorem congr_mul_right_of_congr {m a b : FpPoly p} (z : FpPoly p)
    (hab : DensePoly.Congr a b m) :
    DensePoly.Congr (a * z) (b * z) m := by
  rcases hab with ⟨r, hr⟩
  refine ⟨r * z, ?_⟩
  rw [← sub_mul_poly a b z, show a - b = m * r from hr, FpPoly.mul_assoc]

omit [ZMod64.PrimeModulus p] in
/-- The `i`-th coefficient commutes with a `(· + ·)`-`foldl` of polynomials. -/
private theorem coeff_foldl_add {α : Type _} (xs : List α)
    (term : α → FpPoly p) (i : Nat) :
    (xs.foldl (fun acc k => acc + term k) 0).coeff i =
      xs.foldl (fun acc k => acc + (term k).coeff i) 0 := by
  have h0 : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  suffices h : ∀ init : FpPoly p,
      (xs.foldl (fun acc k => acc + term k) init).coeff i =
        xs.foldl (fun acc k => acc + (term k).coeff i) (init.coeff i) by
    have hh := h 0
    rwa [DensePoly.coeff_zero] at hh
  intro init
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (init + term x), DensePoly.coeff_add init (term x) i h0]

omit [ZMod64.PrimeModulus p] in
/-- If every term of a `(· + ·)`-`foldl` is constant modulo `g` (and the
accumulator starts constant), the whole fold is constant modulo `g`. -/
private theorem foldl_congr_const {α : Type _} (g : FpPoly p)
    (term : α → FpPoly p) :
    ∀ (xs : List α),
      (∀ k ∈ xs, ∃ a : ZMod64 p, DensePoly.Congr (term k) (DensePoly.C a) g) →
      ∀ init : FpPoly p, (∃ a, DensePoly.Congr init (DensePoly.C a) g) →
        ∃ a, DensePoly.Congr (xs.foldl (fun acc k => acc + term k) init)
          (DensePoly.C a) g := by
  intro xs
  induction xs with
  | nil => intro _ init hinit; exact hinit
  | cons x xs ih =>
      intro hterms init hinit
      obtain ⟨a0, ha0⟩ := hinit
      simp only [List.foldl_cons]
      apply ih (fun k hk => hterms k (List.mem_cons_of_mem _ hk)) (init + term x)
      obtain ⟨b0, hb0⟩ := hterms x (by simp)
      refine ⟨a0 + b0, ?_⟩
      have hsum := congr_add_of_congr ha0 hb0
      rwa [C_add_C] at hsum

omit [ZMod64.PrimeModulus p] in
/-- `d ∣ a → d ∣ a * z`, the right companion of `DensePoly.dvd_mul_left_poly`. -/
private theorem dvd_mul_right_poly {d a : FpPoly p} (z : FpPoly p) (h : d ∣ a) :
    d ∣ a * z := by
  rcases h with ⟨e, he⟩
  exact ⟨e * z, by rw [he, FpPoly.mul_assoc]⟩

omit [ZMod64.PrimeModulus p] in
/-- Two `(· + ·)`-`folds` with pointwise-equal step functions are equal. -/
private theorem foldl_add_congr_terms {α : Type _} (F G : α → ZMod64 p) :
    ∀ (xs : List α), (∀ k ∈ xs, F k = G k) →
      ∀ init, xs.foldl (fun acc k => acc + F k) init =
        xs.foldl (fun acc k => acc + G k) init := by
  intro xs
  induction xs with
  | nil => intro _ init; rfl
  | cons x xs ih =>
      intro h init
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      exact ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) (init + G x)

/-- Each fixed-space kernel basis polynomial is reduced modulo `f`. -/
private theorem fixedSpaceKernel_get_size_le
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (k : Fin (basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic))) :
    ((fixedSpaceKernel f hmonic).get k).size ≤ basisSize f := by
  have hker_eq :
      (fixedSpaceKernel f hmonic).get k =
        vectorToPoly ((fixedSpaceKernelVectors f hmonic).get k) := by
    unfold fixedSpaceKernel
    exact Vector.getElem_ofFn _
  rw [hker_eq]
  unfold vectorToPoly
  have hle :
      (FpPoly.ofCoeffs ((fixedSpaceKernelVectors f hmonic).get k).toArray).size ≤
        ((fixedSpaceKernelVectors f hmonic).get k).toArray.size :=
    DensePoly.size_ofCoeffs_le _
  have hsz :
      ((fixedSpaceKernelVectors f hmonic).get k).toArray.size = basisSize f :=
    ((fixedSpaceKernelVectors f hmonic).get k).size_toArray
  omega

omit [ZMod64.PrimeModulus p] in
/-- Square-freeness (as the `∀ d` divisor predicate) descends to a factor: if
`g * cof = f` is square-free then so is `g`. -/
private theorem squareFree_predicate_of_mul
    (f g cof : FpPoly p) (hf_eq : g * cof = f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true) :
    ∀ d, d ∣ g → d ∣ DensePoly.derivative g → isUnitPolynomial d = true := by
  intro d hdg hdg'
  apply hsquareFree d
  · rcases hdg with ⟨e, he⟩
    exact ⟨e * cof, by rw [← hf_eq, he, FpPoly.mul_assoc]⟩
  · have hderiv : DensePoly.derivative f =
        DensePoly.derivative g * cof + g * DensePoly.derivative cof := by
      rw [← hf_eq]; exact DensePoly.derivative_mul g cof
    rw [hderiv]
    exact DensePoly.dvd_add_poly (dvd_mul_right_poly cof hdg')
      (dvd_mul_right_poly (DensePoly.derivative cof) hdg)

set_option maxHeartbeats 800000 in
/--
**CRT lift of a kernel witness.** Given `g * cof = f` with `f` square-free and
`g` of positive degree, a `g`-kernel polynomial `hh` nonconstant modulo `g`
lifts to an `f`-kernel polynomial `H` (reduced modulo `f`, hence
`size ≤ basisSize f`) that is still nonconstant modulo `g`. The lift is the CRT
combination `H ≡ hh (mod g)`, `H ≡ 0 (mod cof)`; coprimality of `g` and `cof`
comes from square-freeness.
-/
private theorem exists_fKernel_witness_nonconst_mod_g
    (f g cof : FpPoly p) (hf_eq : g * cof = f) (hf_ne : f ≠ 0)
    (hg_pos : 0 < g.degree?.getD 0)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hh : FpPoly p)
    (hh_dvd : g ∣ (FpPoly.linearPow hh p - hh))
    (hh_nonconst : ∀ c : ZMod64 p, ¬ DensePoly.Congr hh (DensePoly.C c) g) :
    ∃ H : FpPoly p,
      f ∣ (FpPoly.linearPow H p - H) ∧
      H.size ≤ basisSize f ∧
      ∀ c : ZMod64 p, ¬ DensePoly.Congr H (DensePoly.C c) g := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hg_ne : g ≠ 0 := ne_zero_of_pos_degree hg_pos
  have hcof_ne : cof ≠ 0 := by
    intro h; rw [h, FpPoly.mul_zero] at hf_eq; exact hf_ne hf_eq.symm
  have hf_pos : 0 < f.degree?.getD 0 := by
    rw [← hf_eq, FpPoly.degree?_mul_eq_add_degree? g cof hg_ne hcof_ne]; omega
  -- Bezout from square-freeness: `gcd g cof ∣ 1`.
  have hgcd_dvd_one : DensePoly.gcd g cof ∣ (1 : FpPoly p) :=
    common_dvd_one_of_squareFree_mul
      (fun e he hde => hsquareFree e (hf_eq ▸ he) (hf_eq ▸ hde))
      (DensePoly.gcd_dvd_left g cof) (DensePoly.gcd_dvd_right g cof)
  obtain ⟨s, t, hbez⟩ := exists_bezout_eq_one_of_gcd_dvd_one g cof hgcd_dvd_one
  -- CRT combination `H0 ≡ hh (mod g)`, `H0 ≡ 0 (mod cof)`. Generalize the large
  -- `polyCRT` term to an opaque `H0` to avoid `whnf` heartbeat blowups.
  have hH0_g : DensePoly.Congr (DensePoly.polyCRT g cof hh 0 s t) hh g :=
    DensePoly.polyCRT_congr_fst g cof hh 0 s t hbez
  have hH0_cof : DensePoly.Congr (DensePoly.polyCRT g cof hh 0 s t) 0 cof :=
    DensePoly.polyCRT_congr_snd g cof hh 0 s t hbez
  generalize DensePoly.polyCRT g cof hh 0 s t = H0 at hH0_g hH0_cof
  have hmg : H0 % g = hh % g :=
    @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hH0_g
  -- `g ∣ linearPow H0 p - H0`.
  have hg_dvd_H0 : g ∣ (FpPoly.linearPow H0 p - H0) := by
    have c1 : DensePoly.Congr (FpPoly.linearPow H0 p) (FpPoly.linearPow hh p) g :=
      linearPow_congr_of_congr g H0 hh p hH0_g
    have m1 : (FpPoly.linearPow H0 p) % g = (FpPoly.linearPow hh p) % g :=
      @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
        (ZMod64.instDivModLawsZMod64Fp p) _ _ _ c1
    have m2 : (FpPoly.linearPow hh p) % g = hh % g :=
      @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
        (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hh_dvd
    have hmod : (FpPoly.linearPow H0 p) % g = H0 % g := by rw [m1, m2, ← hmg]
    exact @DensePoly.congr_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hmod
  -- `cof ∣ linearPow H0 p - H0`.
  have hcof_dvd_H0 : cof ∣ (FpPoly.linearPow H0 p - H0) :=
    dvd_linearPow_sub_self_of_congr_zero cof H0 hH0_cof
  -- `f ∣ linearPow H0 p - H0`.
  have hf_dvd_H0 : f ∣ (FpPoly.linearPow H0 p - H0) := by
    rw [← hf_eq]
    exact mul_dvd_of_dvd_dvd_common hg_dvd_H0 hcof_dvd_H0
      (fun d hdg hdc => common_dvd_one_of_bezout hbez d hdg hdc)
  refine ⟨H0 % f, ?_, ?_, ?_⟩
  · -- `f ∣ linearPow (H0 % f) p - (H0 % f)`.
    have := (dvd_linearPow_sub_self_mod_iff f H0 1).mp (by simpa using hf_dvd_H0)
    simpa using this
  · -- `(H0 % f).size ≤ basisSize f`.
    rw [basisSize]
    have hlt := DensePoly.mod_degree_lt_of_pos_degree H0 f hf_pos
    by_cases hsize : (H0 % f).size = 0
    · omega
    · have hpos : 0 < (H0 % f).size := Nat.pos_of_ne_zero hsize
      have hdeg_eq : (H0 % f).degree?.getD 0 = (H0 % f).size - 1 := by
        unfold DensePoly.degree?; simp [Nat.ne_of_gt hpos]
      omega
  · -- `H0 % f` is nonconstant modulo `g`.
    intro c hc
    apply hh_nonconst c
    apply @DensePoly.congr_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ _
    have e_hc : (H0 % f) % g = (DensePoly.C c) % g :=
      @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
        (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hc
    have e_modf : DensePoly.Congr (H0 % f) H0 g := by
      have hcongr_f : DensePoly.Congr (H0 % f) H0 f :=
        @DensePoly.congr_mod (ZMod64 p) inferInstance inferInstance inferInstance
          (ZMod64.instDivModLawsZMod64Fp p) H0 f
      exact fp_dvd_trans (⟨cof, hf_eq.symm⟩ : g ∣ f) hcongr_f
    have e_modf' : (H0 % f) % g = H0 % g :=
      @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
        (ZMod64.instDivModLawsZMod64Fp p) _ _ _ e_modf
    exact hmg.symm.trans (e_modf'.symm.trans e_hc)

set_option maxHeartbeats 800000 in
/--
**Span-mod-`g`.** If an `f`-kernel polynomial `H` (reduced mod `f`) is
nonconstant modulo `g`, then some `f`-kernel basis polynomial is nonconstant
modulo `g`. Contrapositive: were every basis polynomial constant mod `g`, then
`H`, being their `F_p`-linear combination
(`fixedSpaceKernelPolynomial_coeffVector_complete`), would be constant mod `g`.
-/
private theorem exists_basis_nonconst_mod_g
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (g : FpPoly p)
    (H : FpPoly p) (hH_kernel : IsFixedSpaceKernelPolynomial f hmonic H)
    (hH_size : H.size ≤ basisSize f)
    (hH_nonconst : ∀ c : ZMod64 p, ¬ DensePoly.Congr H (DensePoly.C c) g) :
    ∃ k : Fin (basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)),
      ∀ c : ZMod64 p,
        ¬ DensePoly.Congr ((fixedSpaceKernel f hmonic).get k) (DensePoly.C c) g := by
  by_cases hall : ∀ k : Fin (basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)),
      ∃ c : ZMod64 p,
        DensePoly.Congr ((fixedSpaceKernel f hmonic).get k) (DensePoly.C c) g
  · -- Every basis polynomial is constant mod `g`; derive that `H` is too.
    exfalso
    obtain ⟨c_coeff, hc_eq⟩ :=
      fixedSpaceKernelPolynomial_coeffVector_complete f hmonic H hH_kernel
    let ndim := basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)
    let term : Fin ndim → FpPoly p := fun k =>
      (fixedSpaceKernel f hmonic).get k * DensePoly.C (c_coeff[k.val]'k.isLt)
    -- The span polynomial `P = Σ_k basis_k · c_coeff[k]` is constant mod `g`.
    have hP_const : ∃ a, DensePoly.Congr
        ((List.finRange ndim).foldl (fun acc k => acc + term k) 0)
        (DensePoly.C a) g := by
      refine foldl_congr_const g term (List.finRange ndim) ?_ 0 ?_
      · intro k _hk
        obtain ⟨a, ha⟩ := hall k
        refine ⟨a * (c_coeff[k.val]'k.isLt), ?_⟩
        have h1 := congr_mul_right_of_congr (DensePoly.C (c_coeff[k.val]'k.isLt)) ha
        rwa [C_mul_C] at h1
      · refine ⟨0, 0, ?_⟩
        have hC0 : (DensePoly.C (0 : ZMod64 p) : FpPoly p) = 0 := by
          apply DensePoly.ext_coeff; intro i
          rw [DensePoly.coeff_C, DensePoly.coeff_zero]; split <;> rfl
        rw [hC0, FpPoly.mul_zero]
        exact FpPoly.sub_self 0
    -- And `H` equals that span polynomial.
    have hHP : H = (List.finRange ndim).foldl (fun acc k => acc + term k) 0 := by
      apply DensePoly.ext_coeff
      intro i
      rw [coeff_foldl_add (List.finRange ndim) term i]
      by_cases hi : i < basisSize f
      · have hget :
            (Matrix.mulVec (Matrix.nullspaceBasisMatrix (fixedSpaceMatrix f hmonic))
                c_coeff)[i]'hi = (coeffVector f H)[i]'hi :=
          congrArg (fun v : Vector (ZMod64 p) (basisSize f) => v[i]'hi) hc_eq
        have hrhs : (coeffVector f H)[i]'hi = H.coeff i := by
          unfold coeffVector; rw [Vector.getElem_ofFn]
        have hlhs :
            (Matrix.mulVec (Matrix.nullspaceBasisMatrix (fixedSpaceMatrix f hmonic))
                c_coeff)[i]'hi =
              (List.finRange ndim).foldl
                (fun acc k => acc +
                  ((Matrix.nullspaceBasisMatrix (fixedSpaceMatrix f hmonic))[i]'hi)[k.val]'k.isLt *
                    c_coeff[k.val]'k.isLt) 0 := by
          unfold Matrix.mulVec Vector.dotProduct Matrix.row
          rw [Vector.getElem_ofFn hi]; rfl
        rw [hlhs, hrhs] at hget
        rw [← hget]
        apply foldl_add_congr_terms
        intro k _hk
        rw [nullspaceBasisMatrix_entry_eq_basis_coeff f hmonic k i hi]
        show ((fixedSpaceKernel f hmonic).get k).coeff i * (c_coeff[k.val]'k.isLt)
          = ((fixedSpaceKernel f hmonic).get k *
              DensePoly.C (c_coeff[k.val]'k.isLt)).coeff i
        rw [coeff_mul_C]
      · have hi' : basisSize f ≤ i := Nat.le_of_not_lt hi
        rw [DensePoly.coeff_eq_zero_of_size_le H (Nat.le_trans hH_size hi')]
        symm
        apply foldl_add_eq_zero_of_terms_zero
        intro k _hk
        have hbz : ((fixedSpaceKernel f hmonic).get k).coeff i = 0 :=
          DensePoly.coeff_eq_zero_of_size_le _
            (Nat.le_trans (fixedSpaceKernel_get_size_le f hmonic k) hi')
        show ((fixedSpaceKernel f hmonic).get k *
            DensePoly.C (c_coeff[k.val]'k.isLt)).coeff i = 0
        rw [coeff_mul_C, hbz]
        simp
    rw [hHP] at hH_nonconst
    obtain ⟨a, ha⟩ := hP_const
    exact hH_nonconst a ha
  · -- Some basis polynomial is nonconstant mod `g`.
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hall
    exact ⟨k, fun c hc => hk ⟨c, hc⟩⟩

set_option maxHeartbeats 800000 in
/--
**Divisor-generalized Berlekamp completeness.** For a monic square-free `f` and
a monic divisor `g ∣ f`, if no fixed-space kernel witness of `f` admits a
Berlekamp split of `g`, then `g` is irreducible. This is the per-factor
soundness obligation of `berlekampFactor`, which splits every returned factor
with `f`'s single shared kernel. The case `f = g` recovers
`irreducible_of_no_kernelWitnessSplit_squareFree`.

The proof assumes a nontrivial factorization `g = a₀ * b₀`, extracts a monic
irreducible factor `g₁ ∣ a₀` with monic cofactor `c₀ = g / g₁`, builds a
`g`-kernel CRT witness `hh` nonconstant mod `g`, lifts it to an `f`-kernel
witness `H` nonconstant mod `g` (`exists_fKernel_witness_nonconst_mod_g`), moves
the nonconstancy to an `f`-basis polynomial `w` (`exists_basis_nonconst_mod_g`),
and feeds `w` to the executable split surface to contradict `hno_split`.
-/
theorem irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd
    (f g : FpPoly p) (hmonic : DensePoly.Monic f) (hg_monic : DensePoly.Monic g)
    (hg_dvd_f : g ∣ f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hno_split : ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
      kernelWitnessSplit? g w = none) :
    FpPoly.Irreducible g := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hf_ne_zero : f ≠ 0 := by
    intro hzero
    have hlead : f.leadingCoeff = 1 := hmonic
    rw [hzero] at hlead
    have hlead_zero : (0 : FpPoly p).leadingCoeff = 0 := by
      exact DensePoly.leadingCoeff_zero
    rw [hlead_zero] at hlead
    exact zmod64_one_ne_zero_local hlead.symm
  have hg_ne_zero : g ≠ 0 := by
    intro hzero
    have hlead : g.leadingCoeff = 1 := hg_monic
    rw [hzero] at hlead
    have hlead_zero : (0 : FpPoly p).leadingCoeff = 0 := by
      exact DensePoly.leadingCoeff_zero
    rw [hlead_zero] at hlead
    exact zmod64_one_ne_zero_local hlead.symm
  refine ⟨hg_ne_zero, ?_⟩
  intro a₀ b₀ hab
  by_cases ha₀_unit : a₀.degree? = some 0
  · exact Or.inl ha₀_unit
  refine Or.inr ?_
  by_cases hb₀_unit : b₀.degree? = some 0
  · exact hb₀_unit
  exfalso
  -- Both factors of `g` are nonconstant.
  have ha₀_ne_zero : a₀ ≠ 0 := factor_ne_zero_of_ne_zero hab hg_ne_zero
  have hb₀_ne_zero : b₀ ≠ 0 := by
    have hba : b₀ * a₀ = g := by rw [FpPoly.mul_comm]; exact hab
    exact factor_ne_zero_of_ne_zero hba hg_ne_zero
  have ha₀_pos : 0 < a₀.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit ha₀_ne_zero ha₀_unit
  have hb₀_pos : 0 < b₀.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit hb₀_ne_zero hb₀_unit
  have ha₀_lt_g : a₀.degree?.getD 0 < basisSize g :=
    factor_degree_lt_basisSize hab ha₀_ne_zero hb₀_pos
  -- `g` is square-free (descent from `f`).
  obtain ⟨cofg, hcofg⟩ := hg_dvd_f
  have hsf_g : ∀ d, d ∣ g → d ∣ DensePoly.derivative g → isUnitPolynomial d = true :=
    squareFree_predicate_of_mul f g cofg hcofg.symm hsquareFree
  -- `g` has positive degree.
  have hg_pos : 0 < g.degree?.getD 0 := by
    have hdeg := FpPoly.degree?_mul_eq_add_degree? a₀ b₀ ha₀_ne_zero hb₀_ne_zero
    rw [hab] at hdeg
    omega
  -- Extract a monic irreducible factor `g₁` of `a₀`, with cofactor `c₀ = g / g₁`.
  obtain ⟨g₁, _hg₁_irr, hg₁_monic, hg₁_dvd_a₀, hg₁_deg_pos, hg₁_deg_le_a₀⟩ :=
    exists_monic_irreducible_factor_of_factor hg_monic hab ha₀_pos
  have hg₁_dvd_g : g₁ ∣ g := by
    rcases hg₁_dvd_a₀ with ⟨r, hr⟩
    refine ⟨r * b₀, ?_⟩
    calc g = a₀ * b₀ := hab.symm
      _ = (g₁ * r) * b₀ := by rw [hr]
      _ = g₁ * (r * b₀) := FpPoly.mul_assoc g₁ r b₀
  have hg₁_ne_zero : g₁ ≠ 0 := ne_zero_of_pos_degree hg₁_deg_pos
  let c₀ : FpPoly p := g / g₁
  have hc_eq : g₁ * c₀ = g := (fp_eq_mul_div_of_dvd hg₁_dvd_g).symm
  have hc₀_ne_zero : c₀ ≠ 0 := by
    intro hzero
    rw [hzero, FpPoly.mul_zero] at hc_eq
    exact hg_ne_zero hc_eq.symm
  have hc₀_monic : DensePoly.Monic c₀ := by
    have hlead : DensePoly.leadingCoeff g =
        DensePoly.leadingCoeff g₁ * DensePoly.leadingCoeff c₀ := by
      rw [← hc_eq]
      exact FpPoly.leadingCoeff_mul g₁ c₀ hg₁_ne_zero hc₀_ne_zero
    have hg_one : DensePoly.leadingCoeff g = 1 := hg_monic
    have hg₁_one : DensePoly.leadingCoeff g₁ = 1 := hg₁_monic
    unfold DensePoly.Monic
    rw [hg₁_one, hg_one] at hlead
    have hone_mul : (1 : ZMod64 p) * DensePoly.leadingCoeff c₀ =
        DensePoly.leadingCoeff c₀ := by grind
    rw [hone_mul] at hlead
    exact hlead.symm
  have hg₁_lt_g : g₁.degree?.getD 0 < basisSize g :=
    Nat.lt_of_le_of_lt hg₁_deg_le_a₀ ha₀_lt_g
  have hc₀_pos : 0 < c₀.degree?.getD 0 := by
    have hdeg_eq : (g₁ * c₀).degree?.getD 0 =
        g₁.degree?.getD 0 + c₀.degree?.getD 0 :=
      FpPoly.degree?_mul_eq_add_degree? g₁ c₀ hg₁_ne_zero hc₀_ne_zero
    rw [hc_eq] at hdeg_eq
    unfold basisSize at hg₁_lt_g
    omega
  -- `g`-kernel CRT witness `hh`, nonconstant mod `g`.
  obtain ⟨hh, hh_dvd, hh_nonconst, hh_size⟩ :=
    exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split
      g₁ c₀ hg₁_monic hc₀_monic hg₁_deg_pos hc₀_pos
      (fun d hd hd' => hsf_g d (hc_eq ▸ hd) (hc_eq ▸ hd'))
  rw [hc_eq] at hh_dvd hh_nonconst
  -- Lift `hh` to an `f`-kernel witness `H`, still nonconstant mod `g`.
  obtain ⟨H, hH_fdvd, hH_size, hH_nonconst⟩ :=
    exists_fKernel_witness_nonconst_mod_g f g cofg hcofg.symm hf_ne_zero
      hg_pos hsquareFree hh hh_dvd hh_nonconst
  have hH_kernel : IsFixedSpaceKernelPolynomial f hmonic H := by
    rw [isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self f hmonic H hH_size]
    exact hH_fdvd
  -- Move nonconstancy to an `f`-basis polynomial `w`.
  obtain ⟨k, hk_nonconst⟩ :=
    exists_basis_nonconst_mod_g f hmonic g H hH_kernel hH_size hH_nonconst
  let w : FpPoly p := (fixedSpaceKernel f hmonic).get k
  have hw_mem : w ∈ (fixedSpaceKernel f hmonic).toList := by
    have hk_lt : k.val < (fixedSpaceKernel f hmonic).toList.length := by
      rw [Vector.length_toList]; exact k.isLt
    have hget : (fixedSpaceKernel f hmonic).toList[k.val]'hk_lt = w := by
      rw [Vector.getElem_toList]; rfl
    rw [← hget]; exact List.getElem_mem hk_lt
  have hw_kernel : IsFixedSpaceKernelPolynomial f hmonic w :=
    fixedSpaceKernel_sound f hmonic k
  have hw_size_le : w.size ≤ basisSize f := fixedSpaceKernel_get_size_le f hmonic k
  have hw_fdvd : f ∣ (FpPoly.linearPow w p - w) := by
    rw [isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self f hmonic w hw_size_le]
      at hw_kernel
    exact hw_kernel
  -- `g ∣ Π_c (w - C c)` (via `g ∣ f`) and `w` nonconstant mod `g`.
  have hw_gdvd : g ∣ (FpPoly.linearPow w p - w) :=
    fp_dvd_trans (⟨cofg, hcofg⟩ : g ∣ f) hw_fdvd
  have hw_prod : g ∣ (ZMod64.values p).foldl
      (fun acc c => acc * (w - FpPoly.C c)) 1 :=
    dvd_primeFieldProduct_witness_of_dvd_linearPow_sub_self hw_gdvd
  have hw_nonconst : ∀ c : ZMod64 p, ¬ (g ∣ (w - FpPoly.C c)) :=
    fun c hc => hk_nonconst c hc
  -- The executable split surface produces a split of `g`, contradicting `hno_split`.
  obtain ⟨r, hsplit⟩ :=
    exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree
      hg_pos hw_prod hw_nonconst
  have hno_w : kernelWitnessSplit? g w = none := hno_split w hw_mem
  rw [hno_w] at hsplit
  nomatch hsplit

/--
**Non-monic divisor-generalized Berlekamp completeness.** Drops the monicity
requirement on the divisor `g` of `irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd`
to bare nonzeroness. The factors returned by `berlekampFactor` are raw `gcd`
outputs and so are only monic up to a unit; this is the form the executable
capstone consumes. Positive-degree divisors are normalized to their monic
associate `scale (leadingCoeff g)⁻¹ g`, to which the monic theorem applies after
transporting the no-split fact via `kernelWitnessSplit?_none_scale`; a nonzero
constant divisor is irreducible directly.
-/
theorem irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd_nonmonic
    (f g : FpPoly p) (hmonic : DensePoly.Monic f)
    (hg_ne_zero : g ≠ 0)
    (hg_dvd_f : g ∣ f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hno_split : ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
      kernelWitnessSplit? g w = none) :
    FpPoly.Irreducible g := by
  by_cases hpos : 0 < g.degree?.getD 0
  · -- Positive degree: reduce to the monic associate.
    have hcinv_ne : (DensePoly.leadingCoeff g)⁻¹ ≠ (0 : ZMod64 p) :=
      inv_leadingCoeff_ne_zero_of_pos_degree g hpos
    have hg'_monic :
        DensePoly.Monic (DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g) :=
      FpPoly.scale_inv_leadingCoeff_monic g hpos
    have hg'_dvd_f : DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g ∣ f :=
      fp_dvd_trans (FpPoly.dvd_scale_self_of_ne_zero hcinv_ne g) hg_dvd_f
    have hno_split' : ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
        kernelWitnessSplit? (DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g) w = none :=
      fun w hw => kernelWitnessSplit?_none_scale hcinv_ne g w (hno_split w hw)
    have hirr' : FpPoly.Irreducible (DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g) :=
      irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd f
        (DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g) hmonic hg'_monic hg'_dvd_f
        hsquareFree hno_split'
    exact FpPoly.irreducible_of_scale_of_ne_zero hcinv_ne hirr'
  · -- Degree 0: `g` is a nonzero constant, irreducible by definition.
    refine ⟨hg_ne_zero, ?_⟩
    intro a b hab
    have hg_deg0 : g.degree?.getD 0 = 0 := by omega
    have ha_ne : a ≠ 0 := factor_ne_zero_of_ne_zero hab hg_ne_zero
    have hb_ne : b ≠ 0 := by
      have hba : b * a = g := by rw [FpPoly.mul_comm]; exact hab
      exact factor_ne_zero_of_ne_zero hba hg_ne_zero
    have hdeg := FpPoly.degree?_mul_eq_add_degree? a b ha_ne hb_ne
    rw [hab, hg_deg0] at hdeg
    have ha0 : a.degree?.getD 0 = 0 := by omega
    left
    have ha_size_ne : a.size ≠ 0 := by
      intro hs
      apply ha_ne
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
    have hdeg_some : a.degree? = some (a.size - 1) := by
      unfold DensePoly.degree?
      simp [ha_size_ne]
    rw [hdeg_some] at ha0 ⊢
    simp at ha0
    rw [ha0]

/--
**Executable Berlekamp factor irreducibility.** Every factor returned by
`berlekampFactor` on a monic square-free input is irreducible.  Assembles the
per-factor postconditions of the splitting loop — each factor is nonzero
(`berlekampFactor_factors_ne_zero`), divides `f`
(`berlekampFactor_factors_dvd`), and admits no kernel-witness split
(`kernelWitnessSplit?_none_of_berlekampFactor_factors`) — and feeds them to the
non-monic divisor completeness theorem.
-/
theorem berlekampFactor_factors_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true) :
    ∀ g ∈ (berlekampFactor f hmonic).factors, FpPoly.Irreducible g := by
  intro g hg
  exact irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd_nonmonic f g hmonic
    (berlekampFactor_factors_ne_zero f hmonic g hg)
    (berlekampFactor_factors_dvd f hmonic g hg)
    hsquareFree
    (kernelWitnessSplit?_none_of_berlekampFactor_factors f hmonic g hg)

/--
For a monic square-free `f` whose executable Berlekamp factorization returns
at most one factor, `f` is irreducible. Composes the structural loop lemma
`kernelWitnessSplit?_none_of_berlekampFactor_factors_length_le_one` with the
algebraic completeness theorem
`irreducible_of_no_kernelWitnessSplit_squareFree`.
-/
theorem berlekampFactor_singleton_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hsmall : (berlekampFactor f hmonic).factors.length ≤ 1) :
    FpPoly.Irreducible f :=
  irreducible_of_no_kernelWitnessSplit_squareFree
    f hmonic hsquareFree
    (kernelWitnessSplit?_none_of_berlekampFactor_factors_length_le_one
      f hmonic hsmall)

/--
The executable Berlekamp factor list of a square-free monic input has no
duplicates.  Composes the abstract loop invariant
`Hex.Berlekamp.berlekampFactor_factors_nodup_of_no_squared`
(`HexBerlekamp/Factor.lean`) with the squareness-implies-`isUnitPolynomial`
result `Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd`.
-/
theorem berlekampFactor_factors_nodup
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (berlekampFactor f hmonic).factors.Nodup := by
  apply berlekampFactor_factors_nodup_of_no_squared
  intro g hgg hpos
  have hunit : isUnitPolynomial g = true :=
    isUnitPolynomial_of_squareFree_of_squared_dvd
      (squareFree_common_of_gcd_eq_one hsquareFree) hgg
  have hdeg : g.degree? = some 0 := by
    unfold isUnitPolynomial at hunit
    cases hd : g.degree? with
    | none => rw [hd] at hunit; simp at hunit
    | some k =>
        rw [hd] at hunit
        cases k with
        | zero => rfl
        | succ _ => simp at hunit
  rw [hdeg] at hpos
  simp at hpos


end Berlekamp
end Hex
