/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.Correctness
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

public import HexBerlekampZassenhausMathlib.ScaledSearchCoverage
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.RecombinationMonic
import all HexBerlekampZassenhausMathlib.PrimitivityDegreeCover
import all HexBerlekampZassenhausMathlib.ScaledSearchCoverage

public section
set_option backward.proofsInPublic true

/-!
This module collects size-ordered coverage, both mutual blocks, and `RecoveredSmartSearch`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-!
### Size-ordered (smart) recombination coverage (#8413)

The classical tier runs `Hex.scaledRecombinationSmart`, the size-ordered
budgeted search, not `Hex.scaledRecombinationSearchMod`.  These theorems are the
smart analogue of `RecoveredScaledSearch.covers_of_bound`.  Because the smart
search threads a candidate `budget` that can abandon a factorable sub-target,
the coverage statement is conditional on the search returning `some`, and rests
on a `trustworthy-none` completeness fact: with adequate fuel the only way any
sub-search declines is by exhausting its budget (`b = 0`), which propagates.

Fuel adequacy is `budget + 3 * J.card + 1 ≤ fuel`, maintained across peels; the
wrapper's `fuel = budget + (r+1)(2r+3)` (`Hex.scaledRecombinationSmart`) meets it
at the top.  See `progress/20260701T002411Z_issue-8413-smart-coverage.md`.
-/

/-- Fuel budget for the size-ordered search at `n` remaining lifted factors.
The wrapper `Hex.scaledRecombinationSmart` passes `budget + smartFuelBound r`
(its `(r+1)(2r+3)` term). Quadratic because the size loop's per-level overhead
sums to `O(r²)` over the peel recursion. -/
@[expose]
def smartFuelBound (n : Nat) : Nat := (n + 1) * (2 * n + 3)

/-- Fuel budget for the size/candidate loops at `n` remaining lifted factors;
one `smartFuelBound` step smaller so the `Aux → SizeLoop → CandLoop → Aux` cycle
stays adequate. -/
def smartLoopFuelBound (n : Nat) : Nat := n * (2 * n + 1)

private theorem smartFuelBound_pos (n : Nat) : 0 < smartFuelBound n := by
  unfold smartFuelBound; positivity

private theorem smartLoopFuelBound_add_succ_le (n : Nat) :
    smartLoopFuelBound n + n + 1 ≤ smartFuelBound n := by
  unfold smartLoopFuelBound smartFuelBound; nlinarith [n.zero_le]

private theorem smartFuelBound_le_smartLoopFuelBound {m n : Nat} (h : m + 1 ≤ n) :
    smartFuelBound m ≤ smartLoopFuelBound n := by
  unfold smartFuelBound smartLoopFuelBound; nlinarith [h, m.zero_le, n.zero_le]

/-- Every size-`k` split from `subsetsOfSizeWithComplement` has a length-`k`
selected component. -/
private theorem subsetsOfSizeWithComplement_fst_length {α : Type} :
    ∀ (xs : List α) (k : Nat) {sc : List α × List α},
      sc ∈ Hex.subsetsOfSizeWithComplement xs k → sc.1.length = k
  | xs, 0, sc, hmem => by
      simp only [Hex.subsetsOfSizeWithComplement, List.mem_singleton] at hmem
      subst hmem; rfl
  | [], _ + 1, sc, hmem => by
      simp only [Hex.subsetsOfSizeWithComplement, List.not_mem_nil] at hmem
  | x :: xs, k + 1, sc, hmem => by
      simp only [Hex.subsetsOfSizeWithComplement, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨sc', hsc'_mem, rfl⟩ | ⟨sc', hsc'_mem, rfl⟩
      · have := subsetsOfSizeWithComplement_fst_length xs k hsc'_mem
        simpa using this
      · have := subsetsOfSizeWithComplement_fst_length xs (k + 1) hsc'_mem
        simpa using this

/-- The selected list of a lifted-factor subset has length equal to the subset's
cardinality. -/
private theorem liftedSubsetSelectedList_length (d : Hex.LiftData)
    (S : LiftedFactorSubset d) :
    (liftedSubsetSelectedList d S).length = S.card :=
  LiftedFactorListMatches.length_eq_card
    ((LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList d S _).mpr rfl)

/-- In a `subsetSplits` split, an empty selected component forces the rejected
component to be the whole list. -/
private theorem subsetSplits_snd_eq_of_fst_nil :
    ∀ (xs : List Hex.ZPoly) {s : List Hex.ZPoly × List Hex.ZPoly},
      s ∈ Hex.subsetSplits xs → s.1 = [] → s.2 = xs
  | [], s, hmem, _ => by
      simp only [Hex.subsetSplits, List.mem_singleton] at hmem; rw [hmem]
  | f :: fs, s, hmem, hnil => by
      simp only [Hex.subsetSplits, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨t, ht_mem, rfl⟩ | ⟨t, ht_mem, rfl⟩
      · show f :: t.2 = f :: fs
        rw [subsetSplits_snd_eq_of_fst_nil fs ht_mem hnil]
      · exact absurd hnil (by simp)

/-- Every `subsetSplits` member is a size-`|selected|` split from
`subsetsOfSizeWithComplement`. -/
private theorem subsetSplits_mem_subsetsOfSizeWithComplement :
    ∀ (xs : List Hex.ZPoly) {s : List Hex.ZPoly × List Hex.ZPoly},
      s ∈ Hex.subsetSplits xs → s ∈ Hex.subsetsOfSizeWithComplement xs s.1.length
  | [], s, hmem => by
      simp only [Hex.subsetSplits, List.mem_singleton] at hmem
      subst hmem; simp [Hex.subsetsOfSizeWithComplement]
  | f :: fs, s, hmem => by
      simp only [Hex.subsetSplits, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨t, ht_mem, rfl⟩ | ⟨t, ht_mem, rfl⟩
      · -- reject `f`: `s = (t.1, f :: t.2)`
        have ht := subsetSplits_mem_subsetsOfSizeWithComplement fs ht_mem
        rcases Nat.eq_zero_or_pos t.1.length with h0 | hpos
        · rw [List.length_eq_zero_iff] at h0
          have ht2 := subsetSplits_snd_eq_of_fst_nil fs ht_mem h0
          simp only [h0, List.length_nil, Hex.subsetsOfSizeWithComplement,
            List.mem_singleton, ht2]
        · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
          rw [hm] at ht
          simp only [hm, Hex.subsetsOfSizeWithComplement, List.mem_append, List.mem_map]
          exact Or.inr ⟨t, ht, rfl⟩
      · -- select `f`: `s = (f :: t.1, t.2)`
        have ht := subsetSplits_mem_subsetsOfSizeWithComplement fs ht_mem
        simp only [List.length_cons, Hex.subsetsOfSizeWithComplement,
          List.mem_append, List.mem_map]
        exact Or.inl ⟨t, ht, rfl⟩

/-- Completeness of the size enumeration: a subset `S ⊆ J` containing `J.min'`
(so its selected list starts with `head`) has its `(selected, rejected)` split
enumerated by `subsetsOfSizeWithComplement tail (S.card - 1)`.  The converse of
`subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches`; needed so
the size loop can invoke the candidate-loop completeness at `S_cov`'s size. -/
private theorem liftedSubsetSplit_mem_subsetsOfSizeWithComplement_of_matches
    {d : Hex.LiftData} {J S : LiftedFactorSubset d}
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    (hmatches : LiftedFactorListMatches d J (head :: tail))
    (hne : J.Nonempty) (hSJ : S ⊆ J) (hmin : J.min' hne ∈ S) :
    (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ∈
      (Hex.subsetsOfSizeWithComplement tail (S.card - 1)).map
        (fun sc => (head :: sc.1, sc.2)) := by
  have hmem := liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches hmatches hSJ hne hmin
  rw [Hex.subsetSplitsWithFirst, List.mem_map] at hmem
  obtain ⟨x, hx_mem, hx_eq⟩ := hmem
  have hsel : head :: x.1 = liftedSubsetSelectedList d S :=
    (Prod.mk.injEq .. ▸ hx_eq).1
  have hx1_len : x.1.length = S.card - 1 := by
    have hlen := congrArg List.length hsel
    rw [liftedSubsetSelectedList_length] at hlen
    simp only [List.length_cons] at hlen; omega
  have hx_size := subsetSplits_mem_subsetsOfSizeWithComplement tail hx_mem
  rw [hx1_len] at hx_size
  exact List.mem_map.mpr ⟨x, hx_size, hx_eq⟩

/-! ### Prefilter soundness for the classical candidate loop

`Hex.scaledCandidatePrefilter` may reject a subset only when `exactQuotient?`
provably fails on its candidate
(`scaledCandidatePrefilter_eq_true_of_exactQuotient?_some`), so pruning never
changes the accepted-candidate sequence of
`Hex.scaledRecombinationSmartCandLoop` — the completeness apparatus below
consumes this to dismiss the prefilter-rejected branch on the covering
subset. -/

/-- Reducing the argument mod `m` first does not change the centered
representative. -/
private theorem centeredModNat_emod_left (z : ℤ) (m : ℕ) :
    Hex.centeredModNat (z % (m : ℤ)) m = Hex.centeredModNat z m := by
  unfold Hex.centeredModNat
  by_cases hm : m = 0
  · simp [hm]
  · rw [if_neg hm, if_neg hm]
    have hz : z % (m : ℤ) % Int.ofNat m = z % Int.ofNat m := by
      show z % (m : ℤ) % (m : ℤ) = z % (m : ℤ)
      rw [Int.emod_emod]
    rw [hz]

/-- The running-reduction fold of `Hex.selectedProductResidue` computes the
plain product mod `m`. -/
private theorem foldl_mul_emod_eq (f : Hex.ZPoly → ℤ) (m : ℤ) (sel : List Hex.ZPoly) :
    ∀ a : ℤ, sel.foldl (fun acc g => acc * f g % m) a % m = a * (sel.map f).prod % m := by
  induction sel with
  | nil => intro a; simp
  | cons g tl ih =>
      intro a
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ih (a * f g % m)]
      conv_lhs => rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      rw [mul_assoc]

/-- `Hex.selectedProductResidue` is the centered residue of the plain
coefficient product. -/
private theorem selectedProductResidue_eq_centeredModNat_prod
    (f : Hex.ZPoly → ℤ) (sel : List Hex.ZPoly) (m : ℕ) :
    Hex.selectedProductResidue f sel m =
      Hex.centeredModNat ((sel.map f)).prod m := by
  unfold Hex.selectedProductResidue
  rw [← centeredModNat_emod_left
      (sel.foldl (fun acc g => acc * f g % (m : ℤ)) 1) m,
    foldl_mul_emod_eq f (m : ℤ) sel 1, one_mul, centeredModNat_emod_left]

/-- `Hex.selectedDegreeSum` is the sum of the embedded factors' degrees. -/
private theorem selectedDegreeSum_eq_sum (sel : List Hex.ZPoly) :
    Hex.selectedDegreeSum sel =
      (sel.map fun g => (HexPolyZMathlib.toPolynomial g).natDegree).sum := by
  have haux : ∀ (l : List Hex.ZPoly) (a : ℕ),
      l.foldl (fun n g => n + g.degree?.getD 0) a =
        a + (l.map fun g => g.degree?.getD 0).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons g tl ih =>
        intro a
        rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]
  unfold Hex.selectedDegreeSum
  rw [haux, Nat.zero_add]
  simp [HexPolyMathlib.natDegree_toPolynomial]

private theorem zpoly_leadingCoeff_zero :
    Hex.DensePoly.leadingCoeff (0 : Hex.ZPoly) = 0 := by
  rw [← HexPolyMathlib.leadingCoeff_toPolynomial, HexPolyMathlib.toPolynomial_zero,
    Polynomial.leadingCoeff_zero]

private theorem list_prod_ne_zero_poly (l : List (Polynomial ℤ))
    (h : ∀ p ∈ l, p ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons p tl ih =>
      rw [List.prod_cons]
      exact mul_ne_zero (h p List.mem_cons_self)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

private theorem natDegree_list_prod_of_ne_zero (l : List (Polynomial ℤ))
    (h : ∀ p ∈ l, p ≠ 0) :
    l.prod.natDegree = (l.map Polynomial.natDegree).sum := by
  induction l with
  | nil => simp
  | cons p tl ih =>
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        Polynomial.natDegree_mul (h p List.mem_cons_self)
          (list_prod_ne_zero_poly tl fun q hq => h q (List.mem_cons_of_mem _ hq)),
        ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

private theorem leadingCoeff_list_prod_poly (l : List (Polynomial ℤ)) :
    l.prod.leadingCoeff = (l.map Polynomial.leadingCoeff).prod := by
  induction l with
  | nil => simp
  | cons p tl ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        Polynomial.leadingCoeff_mul, ih]

/-- The subset product's coefficient at the degree sum is the product of the
factors' leading coefficients. Unconditional: when some factor is zero both
sides vanish, and otherwise the coefficient sits at the product's degree. -/
private theorem polyProduct_coeff_selectedDegreeSum (sel : List Hex.ZPoly) :
    (Array.polyProduct sel.toArray).coeff (Hex.selectedDegreeSum sel) =
      (sel.map Hex.DensePoly.leadingCoeff).prod := by
  by_cases hz : ∃ g ∈ sel, g = 0
  · obtain ⟨g, hg_mem, hg_eq⟩ := hz
    have hP0 : Array.polyProduct sel.toArray = 0 := by
      have hpoly : HexPolyZMathlib.toPolynomial (Array.polyProduct sel.toArray) = 0 := by
        rw [polyProduct_toPolynomial]
        refine List.prod_eq_zero ?_
        exact List.mem_map.mpr
          ⟨g, hg_mem, by rw [hg_eq, HexPolyZMathlib.toPolynomial_zero]⟩
      rw [← HexPolyZMathlib.ofPolynomial_toPolynomial (Array.polyProduct sel.toArray),
        hpoly, HexPolyZMathlib.ofPolynomial_zero]
    have hlc0 : (0 : ℤ) ∈ sel.map Hex.DensePoly.leadingCoeff :=
      List.mem_map.mpr ⟨g, hg_mem, by rw [hg_eq]; exact zpoly_leadingCoeff_zero⟩
    rw [hP0, Hex.DensePoly.coeff_zero]
    exact (List.prod_eq_zero hlc0).symm
  · have hz' : ∀ g ∈ sel, g ≠ 0 := fun g hg hg0 => hz ⟨g, hg, hg0⟩
    have hTg_ne : ∀ p ∈ sel.map HexPolyZMathlib.toPolynomial, p ≠ 0 := by
      intro p hp hp0
      obtain ⟨g, hg_mem, rfl⟩ := List.mem_map.mp hp
      apply hz' g hg_mem
      rw [← HexPolyZMathlib.ofPolynomial_toPolynomial g, hp0,
        HexPolyZMathlib.ofPolynomial_zero]
    have hdeg : (HexPolyZMathlib.toPolynomial (Array.polyProduct sel.toArray)).natDegree =
        Hex.selectedDegreeSum sel := by
      rw [polyProduct_toPolynomial]
      rw [natDegree_list_prod_of_ne_zero _ hTg_ne, selectedDegreeSum_eq_sum,
        List.map_map]
      rfl
    have hlead : (HexPolyZMathlib.toPolynomial (Array.polyProduct sel.toArray)).leadingCoeff =
        (sel.map Hex.DensePoly.leadingCoeff).prod := by
      rw [polyProduct_toPolynomial]
      rw [leadingCoeff_list_prod_poly, List.map_map]
      congr 1
      exact List.map_congr_left fun g _ => HexPolyMathlib.leadingCoeff_toPolynomial g
    calc (Array.polyProduct sel.toArray).coeff (Hex.selectedDegreeSum sel)
        = (HexPolyZMathlib.toPolynomial (Array.polyProduct sel.toArray)).coeff
            (Hex.selectedDegreeSum sel) :=
          (HexPolyZMathlib.coeff_toPolynomial _ _).symm
      _ = (HexPolyZMathlib.toPolynomial (Array.polyProduct sel.toArray)).leadingCoeff := by
          rw [← hdeg, Polynomial.coeff_natDegree]
      _ = (sel.map Hex.DensePoly.leadingCoeff).prod := hlead

/-- **Prefilter soundness.** A subset whose candidate passes `exactQuotient?`
also passes `Hex.scaledCandidatePrefilter`: the prefilter only rejects
candidates that provably fail trial division, so pruning preserves the
accepted-candidate sequence (and hence outputs, fixtures, and traces) of the
classical candidate loop. -/
theorem scaledCandidatePrefilter_eq_true_of_exactQuotient?_some
    {coreLc : ℤ} {target : Hex.ZPoly} {modulus : ℕ} {sel : List Hex.ZPoly}
    {quotient : Hex.ZPoly}
    (hq : Hex.exactQuotient? target
        (Hex.normalizeFactorSign (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate coreLc
          (Hex.centeredLiftPoly (Array.polyProduct sel.toArray) modulus)))) =
        some quotient) :
    Hex.scaledCandidatePrefilter coreLc target modulus sel = true := by
  set P := Array.polyProduct sel.toArray with hP_def
  set L := Hex.centeredLiftPoly P modulus with hL_def
  set D := Hex.ZPoly.dilate coreLc L with hD_def
  set pp := Hex.ZPoly.primitivePart D with hpp_def
  set cand := Hex.normalizeFactorSign pp with hcand_def
  have hprod : quotient * cand = target := Hex.exactQuotient?_product hq
  have htarget_poly : HexPolyZMathlib.toPolynomial target =
      HexPolyZMathlib.toPolynomial quotient * HexPolyZMathlib.toPolynomial cand := by
    rw [← HexPolyZMathlib.toPolynomial_mul, hprod]
  have hcoeff0 : target.coeff 0 = quotient.coeff 0 * cand.coeff 0 := by
    have hc := congrArg (fun p => Polynomial.coeff p 0) htarget_poly
    simpa only [HexPolyZMathlib.coeff_toPolynomial, Polynomial.mul_coeff_zero] using hc
  have hcand0_dvd : cand.coeff 0 ∣ target.coeff 0 :=
    ⟨quotient.coeff 0, by rw [hcoeff0, mul_comm]⟩
  have hcand0 : cand.coeff 0 = pp.coeff 0 ∨ cand.coeff 0 = -pp.coeff 0 := by
    rw [hcand_def]
    unfold Hex.normalizeFactorSign
    split
    · right
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) pp 0 (Int.mul_zero _), neg_one_mul]
    · left; rfl
  have hpp0_dvd : pp.coeff 0 ∣ target.coeff 0 := by
    rcases hcand0 with h0 | h0
    · rwa [h0] at hcand0_dvd
    · have hpc : pp.coeff 0 = -cand.coeff 0 := by omega
      rw [hpc]
      exact neg_dvd.mpr hcand0_dvd
  have hL_coeff : ∀ n, L.coeff n = Hex.centeredModNat (P.coeff n) modulus := by
    intro n
    rw [hL_def]
    exact Hex.coeff_centeredLiftPoly P modulus n
  have hlcres : Hex.selectedProductResidue Hex.DensePoly.leadingCoeff sel modulus =
      Hex.centeredModNat ((sel.map Hex.DensePoly.leadingCoeff)).prod modulus :=
    selectedProductResidue_eq_centeredModNat_prod _ sel modulus
  have hL_coeff_top : L.coeff (Hex.selectedDegreeSum sel) =
      Hex.selectedProductResidue Hex.DensePoly.leadingCoeff sel modulus := by
    rw [hL_coeff, hP_def, polyProduct_coeff_selectedDegreeSum, ← hlcres]
  have htrail : Hex.selectedProductResidue (fun g => g.coeff 0) sel modulus =
      L.coeff 0 := by
    have hP0 : P.coeff 0 = (sel.map fun g => g.coeff 0).prod := by
      rw [← HexPolyZMathlib.coeff_toPolynomial, hP_def, polyProduct_toPolynomial,
        Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_list_prod]
      simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun g _ => ?_
      rw [Function.comp_apply, ← Polynomial.coeff_zero_eq_eval_zero,
        HexPolyZMathlib.coeff_toPolynomial]
    rw [selectedProductResidue_eq_centeredModNat_prod, hL_coeff 0, hP0]
  have hD0 : D.coeff 0 = Hex.ZPoly.content D * pp.coeff 0 := by
    conv_lhs => rw [← Hex.DensePoly.content_mul_primitivePart D]
    exact Hex.DensePoly.coeff_scale (R := Int) _ _ 0 (Int.mul_zero _)
  have hD0L : D.coeff 0 = L.coeff 0 := by
    rw [hD_def, Hex.ZPoly.coeff_dilate]
    simp
  unfold Hex.scaledCandidatePrefilter
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · -- degree test
    by_cases hcore0 : coreLc = 0
    · exact Or.inl (Or.inl (Or.inl hcore0))
    by_cases hlc0 : Hex.selectedProductResidue Hex.DensePoly.leadingCoeff sel modulus = 0
    · exact Or.inl (Or.inl (Or.inr hlc0))
    by_cases htarget0 : target = 0
    · exact Or.inl (Or.inr htarget0)
    refine Or.inr ?_
    have hnd : ∀ p : Hex.ZPoly,
        (HexPolyZMathlib.toPolynomial p).natDegree = p.degree?.getD 0 := fun p =>
      HexPolyMathlib.natDegree_toPolynomial p
    have hlcprod_ne : ((sel.map Hex.DensePoly.leadingCoeff)).prod ≠ 0 := by
      intro h0
      apply hlc0
      rw [hlcres, h0, Hex.centeredModNat_zero]
    have hg_ne : ∀ g ∈ sel, g ≠ 0 := by
      intro g hg hg0
      apply hlcprod_ne
      refine List.prod_eq_zero (List.mem_map.mpr ⟨g, hg, ?_⟩)
      rw [hg0]
      exact zpoly_leadingCoeff_zero
    have hTg_ne : ∀ p ∈ sel.map HexPolyZMathlib.toPolynomial, p ≠ 0 := by
      intro p hp hp0
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
      apply hg_ne g hg
      rw [← HexPolyZMathlib.ofPolynomial_toPolynomial g, hp0,
        HexPolyZMathlib.ofPolynomial_zero]
    have hTP_deg : (HexPolyZMathlib.toPolynomial P).natDegree =
        Hex.selectedDegreeSum sel := by
      rw [hP_def, polyProduct_toPolynomial]
      rw [natDegree_list_prod_of_ne_zero _ hTg_ne, selectedDegreeSum_eq_sum,
        List.map_map]
      rfl
    have hTL_deg : (HexPolyZMathlib.toPolynomial L).natDegree =
        Hex.selectedDegreeSum sel := by
      apply le_antisymm
      · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro N hN
        rw [HexPolyZMathlib.coeff_toPolynomial, hL_coeff]
        have hPN : P.coeff N = 0 := by
          rw [← HexPolyZMathlib.coeff_toPolynomial]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (hTP_deg ▸ hN)
        rw [hPN, Hex.centeredModNat_zero]
      · apply Polynomial.le_natDegree_of_ne_zero
        rw [HexPolyZMathlib.coeff_toPolynomial, hL_coeff_top]
        exact hlc0
    have hDtop : D.coeff (Hex.selectedDegreeSum sel) =
        coreLc ^ Hex.selectedDegreeSum sel * L.coeff (Hex.selectedDegreeSum sel) := by
      rw [hD_def, Hex.ZPoly.coeff_dilate]
    have hDtop_ne : D.coeff (Hex.selectedDegreeSum sel) ≠ 0 := by
      rw [hDtop, hL_coeff_top]
      exact mul_ne_zero (pow_ne_zero _ hcore0) hlc0
    have hD_ne : D ≠ 0 := by
      intro h0
      apply hDtop_ne
      rw [h0]
      exact Hex.DensePoly.coeff_zero _
    have hTD_deg : (HexPolyZMathlib.toPolynomial D).natDegree =
        Hex.selectedDegreeSum sel := by
      rw [hD_def, HexPolyZMathlib.natDegree_toPolynomial_dilate coreLc hcore0, hTL_deg]
    have hcontent_ne : Hex.ZPoly.content D ≠ 0 :=
      HexPolyZMathlib.content_ne_zero D hD_ne
    have hTpp_deg : (HexPolyZMathlib.toPolynomial pp).natDegree =
        Hex.selectedDegreeSum sel := by
      have hCD := HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart D
      have hnat := congrArg Polynomial.natDegree hCD
      rw [hTD_deg, Polynomial.natDegree_C_mul hcontent_ne] at hnat
      rw [hpp_def]
      exact hnat.symm
    have hsize : cand.size = pp.size := by
      rw [hcand_def]
      exact size_normalizeFactorSign_eq pp
    have hcand_deg : cand.degree?.getD 0 = pp.degree?.getD 0 := by
      simp only [Hex.DensePoly.degree?, hsize]
    have hTC_deg : (HexPolyZMathlib.toPolynomial cand).natDegree =
        Hex.selectedDegreeSum sel := by
      rw [hnd, hcand_deg, ← hnd, hTpp_deg]
    have hT_ne : HexPolyZMathlib.toPolynomial target ≠ 0 := by
      intro h0
      apply htarget0
      rw [← HexPolyZMathlib.ofPolynomial_toPolynomial target, h0,
        HexPolyZMathlib.ofPolynomial_zero]
    have hTC_ne : HexPolyZMathlib.toPolynomial cand ≠ 0 := by
      intro h0
      apply hT_ne
      rw [htarget_poly, h0, mul_zero]
    have hTQ_ne : HexPolyZMathlib.toPolynomial quotient ≠ 0 := by
      intro h0
      apply hT_ne
      rw [htarget_poly, h0, zero_mul]
    have hT_deg := congrArg Polynomial.natDegree htarget_poly
    rw [Polynomial.natDegree_mul hTQ_ne hTC_ne, hTC_deg, hnd] at hT_deg
    omega
  · -- trailing-coefficient test
    apply Int.emod_eq_zero_of_dvd
    have hdvd_content : Hex.ZPoly.content D ∣
        coreLc ^ Hex.selectedDegreeSum sel *
          Hex.selectedProductResidue Hex.DensePoly.leadingCoeff sel modulus := by
      have hcd : Hex.ZPoly.content D ∣ D.coeff (Hex.selectedDegreeSum sel) :=
        Hex.ZPoly.content_dvd_coeff D _
      rwa [hD_def, Hex.ZPoly.coeff_dilate, hL_coeff, hP_def,
        polyProduct_coeff_selectedDegreeSum, ← hlcres] at hcd
    rw [htrail, ← hD0L, hD0]
    exact mul_dvd_mul hdvd_content hpp0_dvd

mutual

/-- Trustworthy-none completeness for the size-ordered search: with adequate
fuel, a `none` return can only come from budget exhaustion (`b = 0`).  The
witness is `cover_at_min`: if `J` is nonempty its minimum lies in some true
support `S_cov` whose candidate divides `target`, so the search either peels it
(returning `some`) or exhausts its budget reaching it.  Proved mutually with the
size/candidate loops by induction on `fuel`. -/
private theorem smartAux_none_budget_zero
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    {target : Hex.ZPoly} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly} {budget fuel b : Nat}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfuel : budget + smartFuelBound J.card ≤ fuel)
    (h : Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core)
        target (d.p ^ d.k) localFactors budget fuel = (none, b)) :
    b = 0 := by
  unfold Hex.scaledRecombinationSmartAux at h
  split at h
  · -- target = 1: returns (some [], budget), contradicting (none, b)
    simp at h
  · rename_i htarget_ne_one
    split at h
    · -- budget = 0: returns (none, 0)
      simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
    · split at h
      · -- fuel = 0: excluded by positive fuel adequacy
        exfalso; have := smartFuelBound_pos J.card; omega
      · split at h
        · -- localFactors = []: forces `J` empty, hence `target = 1`, contradiction
          exfalso
          -- `J` is empty from the matched list length.
          have hJcard : J.card = 0 := by
            have := LiftedFactorListMatches.length_eq_card hmatches
            simpa using this.symm
          have hJ_empty : J = ∅ := Finset.card_eq_zero.mp hJcard
          -- but `target ≠ 1` forces an irreducible divisor with a representing
          -- subset `S ⊆ J = ∅`, contradicting `not_represents_empty`.
          have htarget_poly_ne : HexPolyZMathlib.toPolynomial target ≠ 0 := by
            intro hzero
            apply zpoly_ne_zero_of_pos_lc htarget_lc_pos
            apply HexPolyZMathlib.equiv.injective
            show HexPolyZMathlib.toPolynomial target = HexPolyZMathlib.toPolynomial 0
            rw [HexPolyZMathlib.toPolynomial_zero]
            exact hzero
          have htarget_poly_nonunit :
              ¬ IsUnit (HexPolyZMathlib.toPolynomial target) := fun hunit =>
            htarget_ne_one
              (zpoly_eq_one_of_toPolynomial_isUnit_of_pos_lc htarget_lc_pos hunit)
          obtain ⟨g, hg_irr_toPoly, hg_dvd_target, hg_norm_sign⟩ :=
            exists_signNormalized_irreducible_factor htarget_poly_nonunit
              htarget_poly_ne
          obtain ⟨S, hSJ, hSrep⟩ :=
            hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
          have hS_empty : S = ∅ := by
            rw [hJ_empty] at hSJ; exact Finset.subset_empty.mp hSJ
          have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_target htarget_dvd_core
          apply not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
            B' (hvalid g hg_dvd_core) hcore_ne hcore_primitive hcore_lc_pos
            hcore_lc_le hd_modulus hpartition hg_dvd_target hg_irr_toPoly hprecision
          rw [← hS_empty]; exact hSrep
        · -- head :: tail: derive `S_cov` via cover-at-min, delegate to size loop
          rename_i head tail
          have hlen : (head :: tail).length = J.card :=
            LiftedFactorListMatches.length_eq_card hmatches
          simp only [List.length_cons] at hlen
          have hJ_ne : J.Nonempty := by
            rw [← Finset.card_pos]; omega
          obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep⟩ := hpartition.cover_at_min hJ_ne
          have hScov_card_pos : 0 < S_cov.card :=
            Finset.card_pos.mpr ⟨_, hmin_in_S_cov⟩
          have hScov_card_le : S_cov.card ≤ J.card := Finset.card_le_card hS_cov_J
          refine smartSizeLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
            hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
            hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
            htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
            hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
            (liftedSubsetSplit_mem_subsetsOfSizeWithComplement_of_matches hmatches
              hJ_ne hS_cov_J hmin_in_S_cov) ?_ ?_ h
          · -- hcontains : (S_cov.card - 1) ∈ List.range (tail.length + 1)
            rw [List.mem_range]; omega
          · -- fuel adequacy for the size loop
            simp only [List.length_range]
            have hb := smartLoopFuelBound_add_succ_le J.card
            omega
termination_by fuel

/-- Size-loop half of trustworthy-none completeness: with `S_cov`'s size still in
the remaining `sizes`, a `none` return has budget `0`.  Delegates to the
candidate loop at `S_cov`'s size and recurses on smaller sizes. -/
private theorem smartSizeLoop_none_budget_zero
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    {target : Hex.ZPoly} {J : LiftedFactorSubset d}
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    {f_cov : Hex.ZPoly} {S_cov : LiftedFactorSubset d}
    {sizes : List Nat} {budget fuel b : Nat}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J (head :: tail))
    (hf_cov_irr : Irreducible (HexPolyZMathlib.toPolynomial f_cov))
    (hf_cov_dvd_target : f_cov ∣ target)
    (hS_cov_J : S_cov ⊆ J)
    (hJ_ne : J.Nonempty)
    (hmin_in_S_cov : J.min' hJ_ne ∈ S_cov)
    (hS_cov_rep : RepresentsIntegerFactorAtLift core d f_cov S_cov)
    (hscov_enum : (liftedSubsetSelectedList d S_cov,
        liftedSubsetSelectedList d (J \ S_cov)) ∈
      (Hex.subsetsOfSizeWithComplement tail (S_cov.card - 1)).map
        (fun sc => (head :: sc.1, sc.2)))
    (hcontains : (S_cov.card - 1) ∈ sizes)
    (hfuel : budget + smartLoopFuelBound J.card + sizes.length ≤ fuel)
    (h : Hex.scaledRecombinationSmartSizeLoop (Hex.DensePoly.leadingCoeff core)
        target (d.p ^ d.k) head tail sizes budget fuel = (none, b)) :
    b = 0 := by
  unfold Hex.scaledRecombinationSmartSizeLoop at h
  split at h
  · -- sizes = []: contradicts `hcontains`
    simp only [List.not_mem_nil] at hcontains
  · rename_i dsize ds
    simp only [List.length_cons] at hfuel
    split at h
    · -- budget = 0: returns (none, 0)
      simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
    · rename_i hbudget_ne
      split at h
      · -- fuel = 0: `budget + … + sizes.length ≤ 0` forces `budget = 0`
        simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
      · rename_i fuel'
        simp only [] at h
        split at h
        · -- CandLoop returned `some`: contradicts the `none` result
          simp at h
        · -- CandLoop returned `(none, cb)`
          rename_i cb hcand
          by_cases hd_eq : dsize = S_cov.card - 1
          · -- at `S_cov`'s size: CandLoop completeness forces `cb = 0`, then budget-zero
            subst hd_eq
            have hcb : cb = 0 :=
              smartCandLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
                hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
                hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
                htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
                hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
                (fun s hs => hs) hscov_enum (by omega) hcand
            rw [hcb, Hex.scaledRecombinationSmartSizeLoop_budget_zero] at h
            simp only [Prod.mk.injEq] at h; omega
          · -- other size: recurse on `ds` (`S_cov`'s size is still in `ds`)
            have hcb_le := Hex.scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ hcand
            refine smartSizeLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
              hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
              hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
              htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
              hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
              hscov_enum ?_ (by omega) h
            rcases List.mem_cons.mp hcontains with hh | ht
            · exact absurd hh.symm hd_eq
            · exact ht
termination_by fuel

/-- Candidate-loop half of trustworthy-none completeness: `S_cov`'s split is the
unique divider among the same-size `splits` (containment + equal cardinality), so
a `none` return has budget `0` — either budget ran out before reaching it, or its
recursive `Aux` declined and (by `smartAux_none_budget_zero`) with budget `0`. -/
private theorem smartCandLoop_none_budget_zero
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    {target : Hex.ZPoly} {J : LiftedFactorSubset d}
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    {f_cov : Hex.ZPoly} {S_cov : LiftedFactorSubset d}
    {splits : List (List Hex.ZPoly × List Hex.ZPoly)} {budget fuel b : Nat}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J (head :: tail))
    (hf_cov_irr : Irreducible (HexPolyZMathlib.toPolynomial f_cov))
    (hf_cov_dvd_target : f_cov ∣ target)
    (hS_cov_J : S_cov ⊆ J)
    (hJ_ne : J.Nonempty)
    (hmin_in_S_cov : J.min' hJ_ne ∈ S_cov)
    (hS_cov_rep : RepresentsIntegerFactorAtLift core d f_cov S_cov)
    (hsplits_enum : ∀ split ∈ splits,
      split ∈ (Hex.subsetsOfSizeWithComplement tail (S_cov.card - 1)).map
        (fun sc => (head :: sc.1, sc.2)))
    (hscov_mem : (liftedSubsetSelectedList d S_cov,
        liftedSubsetSelectedList d (J \ S_cov)) ∈ splits)
    (hfuel : budget + smartLoopFuelBound J.card ≤ fuel)
    (h : Hex.scaledRecombinationSmartCandLoop (Hex.DensePoly.leadingCoeff core)
        target (d.p ^ d.k) splits budget fuel = (none, b)) :
    b = 0 := by
  unfold Hex.scaledRecombinationSmartCandLoop at h
  split at h
  · -- splits = []: `S_cov`'s split cannot be a member
    simp only [List.not_mem_nil] at hscov_mem
  · rename_i split rest
    split at h
    · -- budget = 0: returns (none, 0)
      simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
    · rename_i hbudget_ne
      split at h
      · -- fuel = 0: `budget + smartLoopFuelBound J.card ≤ 0` forces `budget = 0`
        simp only [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; omega
      · rename_i fuel'
        -- Shared facts: `f_cov = cand(S_cov)` is recorded and divides `target`.
        have hrec_eq : liftedRecoveryCandidate core d S_cov = f_cov :=
          hpartition.liftedRecoveryCandidate_eq hf_cov_irr hf_cov_dvd_target hS_cov_J
            hS_cov_rep
        have hcand_scov_eq :
            Hex.normalizeFactorSign (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate
              (Hex.DensePoly.leadingCoeff core) (Hex.centeredLiftPoly
                (Array.polyProduct (liftedSubsetSelectedList d S_cov).toArray)
                (d.p ^ d.k)))) = liftedRecoveryCandidate core d S_cov := by
          unfold liftedRecoveryCandidate
          rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
        obtain ⟨hf_cov_primitive, hf_cov_lc_pos⟩ :=
          representsIntegerFactorAtLift_primitive_of_bound B' hcore_lc_le hcore_ne
            hcore_primitive hcore_lc_pos hd_liftedFactor_monic hpartition hf_cov_irr
            hf_cov_dvd_target htarget_dvd_core hS_cov_J hS_cov_rep hprecision
        have hf_cov_natDeg_pos :
            0 < (HexPolyZMathlib.toPolynomial f_cov).natDegree := by
          rw [← hrec_eq, natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum_of_bound
            B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision S_cov]
          exact Finset.sum_pos (fun i _ => hd_liftedFactor_natDegree_pos i)
            ⟨J.min' hJ_ne, hmin_in_S_cov⟩
        have hf_cov_degree_pos : 0 < f_cov.degree?.getD 0 := by
          rw [← HexPolyMathlib.natDegree_toPolynomial]; exact hf_cov_natDeg_pos
        obtain ⟨quotient_scov, hquot_scov, hmul_scov⟩ :=
          exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
            hrec_eq hf_cov_lc_pos hf_cov_degree_pos hf_cov_dvd_target
        have hrecord_scov : Hex.shouldRecordPolynomialFactor
            (liftedRecoveryCandidate core d S_cov) = true :=
          shouldRecord_liftedRecoveryCandidate_of_eq_factor hrec_eq hf_cov_irr
        simp only [] at h
        -- Peel the prefilter guard: on the covering split it must pass
        -- (`f_cov`'s candidate divides `target`), and elsewhere rejection
        -- just recurses on the remaining splits.
        by_cases hpre : Hex.scaledCandidatePrefilter (Hex.DensePoly.leadingCoeff core)
            target (d.p ^ d.k) split.1 = true
        swap
        · rw [if_neg hpre] at h
          rcases List.mem_cons.mp hscov_mem with hsplit_eq | hscov_rest
          · -- split = scovSplit: its candidate divides, so the prefilter accepts
            exfalso
            have hsplit1 : split.1 = liftedSubsetSelectedList d S_cov := by
              rw [← hsplit_eq]
            rw [hsplit1] at hpre
            exact hpre (scaledCandidatePrefilter_eq_true_of_exactQuotient?_some
              (by rw [hcand_scov_eq]; exact hquot_scov))
          · exact smartCandLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
              hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
              hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
              htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
              hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
              (fun s hs => hsplits_enum s (List.mem_cons_of_mem _ hs)) hscov_rest
              (by omega) h
        rw [if_pos hpre] at h
        split at h
        · -- candidate is recorded
          rename_i hrecord
          split at h
          · -- exactQuotient? = some quotient (candidate divides `target`)
            rename_i quotient hquot
            split at h
            · -- Aux returned `some`: contradicts the `none` result
              simp at h
            · -- Aux returned `(none, ab)`: candidate is `f_cov`, so `ab = 0`
              rename_i ab haux
              -- Identify `split`'s subset `T`; its candidate divides, so `T = S_cov`.
              have hsplit_in :
                  split ∈ (Hex.subsetsOfSizeWithComplement tail (S_cov.card - 1)).map
                    (fun sc => (head :: sc.1, sc.2)) :=
                hsplits_enum split List.mem_cons_self
              obtain ⟨sc, hsc_mem, hsc_eq⟩ := List.mem_map.mp hsplit_in
              obtain ⟨T, hTJ, hmin_in_T, hTsel, hTrej, hTprod, hTcand⟩ :=
                subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches
                  core d hmatches hJ_ne rfl hsc_mem
              have hsplit1 : split.1 = head :: sc.1 := by rw [← hsc_eq]
              have hsplit2 : split.2 = sc.2 := by rw [← hsc_eq]
              rw [hsplit1, hTcand] at hrecord hquot
              -- `T` has the same cardinality as `S_cov`, and `S_cov ⊆ T`, so `T = S_cov`.
              have hsc1_len : sc.1.length = S_cov.card - 1 :=
                subsetsOfSizeWithComplement_fst_length tail (S_cov.card - 1) hsc_mem
              have hScov_pos : 0 < S_cov.card := Finset.card_pos.mpr ⟨_, hmin_in_S_cov⟩
              have hT_card : T.card = S_cov.card := by
                have hlen := congrArg List.length hTsel
                rw [liftedSubsetSelectedList_length] at hlen
                simp only [List.length_cons] at hlen
                omega
              have hcand_dvd_target : liftedRecoveryCandidate core d T ∣ target := by
                refine ⟨quotient, ?_⟩
                rw [Hex.DensePoly.mul_comm_poly (S := Int)]
                exact (Hex.exactQuotient?_product hquot).symm
              have hcand_dvd_core : liftedRecoveryCandidate core d T ∣ core :=
                zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
              have hvalid'_T : ∀ g : Hex.ZPoly,
                  HexPolyZMathlib.toPolynomial g ∈
                    UniqueFactorizationMonoid.normalizedFactors
                      (HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T)) →
                  ∀ i, (g.coeff i).natAbs ≤ B' := by
                intro g hg_mem
                have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
                    HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) :=
                  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
                have hg_dvd_cand : g ∣ liftedRecoveryCandidate core d T := by
                  rcases hg_poly_dvd with ⟨r, hr⟩
                  refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
                  apply HexPolyZMathlib.equiv.injective
                  simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
                    HexPolyZMathlib.toPolynomial_ofPolynomial]
                  exact hr
                exact hvalid g (zpoly_dvd_trans hg_dvd_cand hcand_dvd_core)
              obtain ⟨f', S', hf'_irr, hf'_dvd_target, hS'_J, hmin_in_S', hS'_rep, hS'_sub_T⟩ :=
                coverAtMin_representingSubset_subset_of_liftedRecoveryCandidate_dvd_of_bound
                  B' hcore_lc_le hvalid'_T hcore_ne hcore_primitive hcore_lc_pos
                  hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
                  htarget_dvd_core hTJ hJ_ne hmin_in_T hrecord hquot
              have hassoc : Associated (HexPolyZMathlib.toPolynomial f_cov)
                  (HexPolyZMathlib.toPolynomial f') := by
                by_contra hnot_assoc
                exact (Finset.disjoint_left.mp
                  (hpartition.pairwise_disjoint hf_cov_irr hf_cov_dvd_target hS_cov_J
                    hS_cov_rep hf'_irr hf'_dvd_target hS'_J hS'_rep hnot_assoc)
                  hmin_in_S_cov hmin_in_S')
              have hSeq : S_cov = S' :=
                hpartition.unique_up_to_associated hf_cov_irr hf_cov_dvd_target hS_cov_J
                  hS_cov_rep hf'_irr hf'_dvd_target hS'_J hS'_rep hassoc
              have hS_cov_sub_T : S_cov ⊆ T := hSeq ▸ hS'_sub_T
              have hT_eq : T = S_cov :=
                (Finset.eq_of_subset_of_card_le hS_cov_sub_T (by omega)).symm
              -- With `T = S_cov`, `quotient = quotient_scov`, so `Aux` decline gives `ab = 0`.
              rw [hT_eq] at hquot hTrej
              rw [hquot_scov] at hquot
              have hquot_eq_scov : quotient = quotient_scov := (Option.some.inj hquot).symm
              subst quotient
              have hquot_mul : quotient_scov * f_cov = target := by
                rw [← hrec_eq]; exact hmul_scov
              have hquot_dvd_target : quotient_scov ∣ target := ⟨f_cov, hquot_mul.symm⟩
              have hquot_dvd_core : quotient_scov ∣ core :=
                zpoly_dvd_trans hquot_dvd_target htarget_dvd_core
              have hquot_primitive : Hex.ZPoly.Primitive quotient_scov :=
                zpoly_primitive_of_dvd_primitive_basic htarget_primitive hquot_dvd_target
              have hquot_lc_pos : 0 < Hex.DensePoly.leadingCoeff quotient_scov :=
                zpoly_left_pos_lc_of_mul_eq_of_pos_lc hquot_mul hf_cov_lc_pos htarget_lc_pos
              have hpartition_new :
                  LiftedFactorSubsetPartition core d (J \ S_cov) quotient_scov :=
                liftedFactorSubsetPartition_transport hpartition hquot_mul hS_cov_rep
                  hS_cov_J hf_cov_irr hf_cov_dvd_target
              have hsdiff_lt : (J \ S_cov).card < J.card := by
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
                exact ⟨J.min' hJ_ne, J.min'_mem hJ_ne,
                  fun hc => (Finset.mem_sdiff.mp hc).2 hmin_in_S_cov⟩
              rw [hsplit2, hTrej] at haux
              have hab : ab = 0 := by
                refine smartAux_none_budget_zero B' hcore_lc_le hvalid hcore_ne
                  hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
                  hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
                  hquot_primitive hquot_lc_pos hquot_dvd_core hpartition_new
                  LiftedFactorListMatches.sdiff_of_subset ?_ haux
                -- fuel adequacy for the `quotient` recursion
                have hbound := smartFuelBound_le_smartLoopFuelBound
                  (m := (J \ S_cov).card) (n := J.card) (by omega)
                omega
              rw [hab] at h
              rw [Hex.scaledRecombinationSmartCandLoop_budget_zero] at h
              simp only [Prod.mk.injEq] at h; omega
          · -- exactQuotient? = none: candidate doesn't divide, so `split ≠ scovSplit`
            rename_i hquot_none
            rcases List.mem_cons.mp hscov_mem with hsplit_eq | hscov_rest
            · -- split = scovSplit: candidate is `f_cov`, which divides — contradiction
              exfalso
              have hsplit1 : split.1 = liftedSubsetSelectedList d S_cov := by
                rw [← hsplit_eq]
              rw [hsplit1, hcand_scov_eq, hquot_scov] at hquot_none
              exact absurd hquot_none (Option.some_ne_none _)
            · exact smartCandLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
                hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
                hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
                htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
                hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
                (fun s hs => hsplits_enum s (List.mem_cons_of_mem _ hs)) hscov_rest
                (by omega) h
        · -- candidate not recorded: so `split ≠ scovSplit` (`f_cov` is recorded)
          rename_i hrecord_false
          rcases List.mem_cons.mp hscov_mem with hsplit_eq | hscov_rest
          · -- split = scovSplit: candidate is `f_cov`, which is recorded — contradiction
            exfalso
            have hsplit1 : split.1 = liftedSubsetSelectedList d S_cov := by
              rw [← hsplit_eq]
            rw [hsplit1, hcand_scov_eq] at hrecord_false
            simp [hrecord_scov] at hrecord_false
          · exact smartCandLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
              hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
              hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
              htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
              hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
              (fun s hs => hsplits_enum s (List.mem_cons_of_mem _ hs)) hscov_rest
              (by omega) h
termination_by fuel

end

mutual

/-- Conditional coverage for the size-ordered search: when it returns `some
result`, every irreducible factor of `target` is an associate of some emitted
factor.  The smart analogue of `RecoveredScaledSearch.covers_of_bound`, proved by
`fuel` induction: the peeled subset is exactly the `cover_at_min` true support
`S_cov` (containment gives `S_cov ⊆ T`; a coarser `T` would leave `S_cov`'s
recursion declining with budget `0` by `smartAux_none_budget_zero`, propagating
to overall `none`), so the emitted head is the irreducible `cover_at_min` factor
and the tail covers the quotient by induction. -/
private theorem smartAux_covers_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    {target : Hex.ZPoly} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly} {budget fuel : Nat}
    {result : List Hex.ZPoly} {b : Nat}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfuel : budget + smartFuelBound J.card ≤ fuel)
    (h : Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core)
        target (d.p ^ d.k) localFactors budget fuel = (some result, b)) :
    ∀ factor : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  intro factor hfactor_irr hfactor_dvd
  unfold Hex.scaledRecombinationSmartAux at h
  split at h
  · -- target = 1: no irreducible divides `1`
    exfalso
    rename_i htarget_eq
    have hdvd_one : HexPolyZMathlib.toPolynomial factor ∣ (1 : Polynomial ℤ) := by
      rw [show (1 : Polynomial ℤ) = HexPolyZMathlib.toPolynomial 1 from
        toPolynomial_one_zpoly.symm]
      rw [htarget_eq] at hfactor_dvd
      exact HexPolyMathlib.toPolynomial_dvd hfactor_dvd
    exact hfactor_irr.not_isUnit (isUnit_of_dvd_one hdvd_one)
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · -- head :: tail: derive `S_cov`, delegate to the size loop
          rename_i head tail
          have hlen : (head :: tail).length = J.card :=
            LiftedFactorListMatches.length_eq_card hmatches
          simp only [List.length_cons] at hlen
          have hJ_ne : J.Nonempty := by rw [← Finset.card_pos]; omega
          obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep⟩ := hpartition.cover_at_min hJ_ne
          have hScov_card_pos : 0 < S_cov.card :=
            Finset.card_pos.mpr ⟨_, hmin_in_S_cov⟩
          have hScov_card_le : S_cov.card ≤ J.card := Finset.card_le_card hS_cov_J
          refine smartSizeLoop_covers_of_bound B' hcore_lc_le hvalid hcore_ne
            hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
            hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
            htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
            hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
            (liftedSubsetSplit_mem_subsetsOfSizeWithComplement_of_matches hmatches
              hJ_ne hS_cov_J hmin_in_S_cov) List.pairwise_lt_range ?_ ?_ h factor
            hfactor_irr hfactor_dvd
          · rw [List.mem_range]; omega
          · simp only [List.length_range]
            have hb := smartLoopFuelBound_add_succ_le J.card
            omega
termination_by fuel

/-- Size-loop half of conditional coverage. -/
private theorem smartSizeLoop_covers_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    {target : Hex.ZPoly} {J : LiftedFactorSubset d}
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    {f_cov : Hex.ZPoly} {S_cov : LiftedFactorSubset d}
    {sizes : List Nat} {budget fuel : Nat} {result : List Hex.ZPoly} {b : Nat}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J (head :: tail))
    (hf_cov_irr : Irreducible (HexPolyZMathlib.toPolynomial f_cov))
    (hf_cov_dvd_target : f_cov ∣ target)
    (hS_cov_J : S_cov ⊆ J)
    (hJ_ne : J.Nonempty)
    (hmin_in_S_cov : J.min' hJ_ne ∈ S_cov)
    (hS_cov_rep : RepresentsIntegerFactorAtLift core d f_cov S_cov)
    (hscov_enum : (liftedSubsetSelectedList d S_cov,
        liftedSubsetSelectedList d (J \ S_cov)) ∈
      (Hex.subsetsOfSizeWithComplement tail (S_cov.card - 1)).map
        (fun sc => (head :: sc.1, sc.2)))
    (hsorted : List.Pairwise (· < ·) sizes)
    (hcontains : (S_cov.card - 1) ∈ sizes)
    (hfuel : budget + smartLoopFuelBound J.card + sizes.length ≤ fuel)
    (h : Hex.scaledRecombinationSmartSizeLoop (Hex.DensePoly.leadingCoeff core)
        target (d.p ^ d.k) head tail sizes budget fuel = (some result, b)) :
    ∀ factor : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  intro factor hfactor_irr hfactor_dvd
  unfold Hex.scaledRecombinationSmartSizeLoop at h
  split at h
  · simp at h
  · rename_i dsize ds
    simp only [List.length_cons] at hfuel
    split at h
    · simp at h
    · rename_i hbudget_ne
      split at h
      · simp at h
      · rename_i fuel'
        simp only [] at h
        split at h
        · -- CandLoop peeled at size `dsize`: delegate to candidate-loop coverage
          rename_i res cb hcand
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨hres, _⟩ := h
          subst hres
          have hk_le : dsize ≤ S_cov.card - 1 := by
            rcases List.mem_cons.mp hcontains with hh | ht
            · omega
            · exact le_of_lt ((List.pairwise_cons.mp hsorted).1 _ ht)
          exact smartCandLoop_covers_of_bound B' hcore_lc_le hvalid hcore_ne
            hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
            hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
            htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
            hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
            hk_le (fun s hs => hs) (by omega) hcand factor hfactor_irr hfactor_dvd
        · -- CandLoop returned `(none, cb)`: recurse on `ds`
          rename_i cb hcand
          have hcb_le := Hex.scaledRecombinationSmartCandLoop_budget_le _ _ _ _ _ _ _ _ hcand
          by_cases hd_eq : dsize = S_cov.card - 1
          · subst hd_eq
            have hcb : cb = 0 :=
              smartCandLoop_none_budget_zero B' hcore_lc_le hvalid hcore_ne
                hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
                hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
                htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
                hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
                (fun s hs => hs) hscov_enum (by omega) hcand
            rw [hcb, Hex.scaledRecombinationSmartSizeLoop_budget_zero] at h
            simp at h
          · refine smartSizeLoop_covers_of_bound B' hcore_lc_le hvalid hcore_ne
              hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
              hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
              htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
              hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
              hscov_enum (List.pairwise_cons.mp hsorted).2 ?_ (by omega) h factor
              hfactor_irr hfactor_dvd
            rcases List.mem_cons.mp hcontains with hh | ht
            · exact absurd hh.symm hd_eq
            · exact ht
termination_by fuel

/-- Candidate-loop half of conditional coverage. -/
private theorem smartCandLoop_covers_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    {target : Hex.ZPoly} {J : LiftedFactorSubset d}
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    {f_cov : Hex.ZPoly} {S_cov : LiftedFactorSubset d}
    {splits : List (List Hex.ZPoly × List Hex.ZPoly)} {budget fuel : Nat}
    {result : List Hex.ZPoly} {b : Nat}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J (head :: tail))
    (hf_cov_irr : Irreducible (HexPolyZMathlib.toPolynomial f_cov))
    (hf_cov_dvd_target : f_cov ∣ target)
    (hS_cov_J : S_cov ⊆ J)
    (hJ_ne : J.Nonempty)
    (hmin_in_S_cov : J.min' hJ_ne ∈ S_cov)
    (hS_cov_rep : RepresentsIntegerFactorAtLift core d f_cov S_cov)
    {k : Nat} (hk_le : k ≤ S_cov.card - 1)
    (hsplits_enum : ∀ split ∈ splits,
      split ∈ (Hex.subsetsOfSizeWithComplement tail k).map
        (fun sc => (head :: sc.1, sc.2)))
    (hfuel : budget + smartLoopFuelBound J.card ≤ fuel)
    (h : Hex.scaledRecombinationSmartCandLoop (Hex.DensePoly.leadingCoeff core)
        target (d.p ^ d.k) splits budget fuel = (some result, b)) :
    ∀ factor : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  intro factor hfactor_irr hfactor_dvd
  unfold Hex.scaledRecombinationSmartCandLoop at h
  split at h
  · simp at h
  · rename_i split rest
    split at h
    · simp at h
    · rename_i hbudget_ne
      split at h
      · simp at h
      · rename_i fuel'
        simp only [] at h
        by_cases hpre : Hex.scaledCandidatePrefilter (Hex.DensePoly.leadingCoeff core)
            target (d.p ^ d.k) split.1 = true
        swap
        · -- prefilter rejected the subset: recurse on `rest`
          rw [if_neg hpre] at h
          exact smartCandLoop_covers_of_bound B' hcore_lc_le hvalid hcore_ne
            hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
            hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
            htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
            hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
            hk_le (fun s hs => hsplits_enum s (List.mem_cons_of_mem _ hs))
            (by omega) h factor hfactor_irr hfactor_dvd
        rw [if_pos hpre] at h
        split at h
        · -- candidate recorded
          rename_i hrecord
          split at h
          · -- exactQuotient? = some quotient: candidate divides
            rename_i quotient hquot
            -- Shared facts and `T = S_cov` (mirrors CandLoop completeness case 1).
            have hrec_eq : liftedRecoveryCandidate core d S_cov = f_cov :=
              hpartition.liftedRecoveryCandidate_eq hf_cov_irr hf_cov_dvd_target hS_cov_J
                hS_cov_rep
            obtain ⟨hf_cov_primitive, hf_cov_lc_pos⟩ :=
              representsIntegerFactorAtLift_primitive_of_bound B' hcore_lc_le hcore_ne
                hcore_primitive hcore_lc_pos hd_liftedFactor_monic hpartition hf_cov_irr
                hf_cov_dvd_target htarget_dvd_core hS_cov_J hS_cov_rep hprecision
            have hf_cov_natDeg_pos :
                0 < (HexPolyZMathlib.toPolynomial f_cov).natDegree := by
              rw [← hrec_eq, natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum_of_bound
                B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision S_cov]
              exact Finset.sum_pos (fun i _ => hd_liftedFactor_natDegree_pos i)
                ⟨J.min' hJ_ne, hmin_in_S_cov⟩
            have hf_cov_degree_pos : 0 < f_cov.degree?.getD 0 := by
              rw [← HexPolyMathlib.natDegree_toPolynomial]; exact hf_cov_natDeg_pos
            obtain ⟨quotient_scov, hquot_scov, hmul_scov⟩ :=
              exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
                hrec_eq hf_cov_lc_pos hf_cov_degree_pos hf_cov_dvd_target
            have hsplit_in :
                split ∈ (Hex.subsetsOfSizeWithComplement tail k).map
                  (fun sc => (head :: sc.1, sc.2)) :=
              hsplits_enum split List.mem_cons_self
            obtain ⟨sc, hsc_mem, hsc_eq⟩ := List.mem_map.mp hsplit_in
            obtain ⟨T, hTJ, hmin_in_T, hTsel, hTrej, hTprod, hTcand⟩ :=
              subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches
                core d hmatches hJ_ne rfl hsc_mem
            have hsplit1 : split.1 = head :: sc.1 := by rw [← hsc_eq]
            have hsplit2 : split.2 = sc.2 := by rw [← hsc_eq]
            have hcand_raw :
                Hex.normalizeFactorSign (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate
                  (Hex.DensePoly.leadingCoeff core) (Hex.centeredLiftPoly
                    (Array.polyProduct split.1.toArray) (d.p ^ d.k)))) =
                  liftedRecoveryCandidate core d T := by
              rw [hsplit1]; exact hTcand
            rw [hsplit1, hTcand] at hrecord hquot
            have hsc1_len : sc.1.length = k :=
              subsetsOfSizeWithComplement_fst_length tail k hsc_mem
            have hScov_pos : 0 < S_cov.card := Finset.card_pos.mpr ⟨_, hmin_in_S_cov⟩
            have hT_card : T.card = k + 1 := by
              have hlen := congrArg List.length hTsel
              rw [liftedSubsetSelectedList_length] at hlen
              simp only [List.length_cons] at hlen; omega
            have hcand_dvd_target : liftedRecoveryCandidate core d T ∣ target := by
              refine ⟨quotient, ?_⟩
              rw [Hex.DensePoly.mul_comm_poly (S := Int)]
              exact (Hex.exactQuotient?_product hquot).symm
            have hcand_dvd_core : liftedRecoveryCandidate core d T ∣ core :=
              zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
            have hvalid'_T : ∀ g : Hex.ZPoly,
                HexPolyZMathlib.toPolynomial g ∈
                  UniqueFactorizationMonoid.normalizedFactors
                    (HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T)) →
                ∀ i, (g.coeff i).natAbs ≤ B' := by
              intro g hg_mem
              have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
                  HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) :=
                UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
              have hg_dvd_cand : g ∣ liftedRecoveryCandidate core d T := by
                rcases hg_poly_dvd with ⟨r, hr⟩
                refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
                apply HexPolyZMathlib.equiv.injective
                simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
                  HexPolyZMathlib.toPolynomial_ofPolynomial]
                exact hr
              exact hvalid g (zpoly_dvd_trans hg_dvd_cand hcand_dvd_core)
            obtain ⟨f', S', hf'_irr, hf'_dvd_target, hS'_J, hmin_in_S', hS'_rep, hS'_sub_T⟩ :=
              coverAtMin_representingSubset_subset_of_liftedRecoveryCandidate_dvd_of_bound
                B' hcore_lc_le hvalid'_T hcore_ne hcore_primitive hcore_lc_pos
                hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
                htarget_dvd_core hTJ hJ_ne hmin_in_T hrecord hquot
            have hassoc : Associated (HexPolyZMathlib.toPolynomial f_cov)
                (HexPolyZMathlib.toPolynomial f') := by
              by_contra hnot_assoc
              exact (Finset.disjoint_left.mp
                (hpartition.pairwise_disjoint hf_cov_irr hf_cov_dvd_target hS_cov_J
                  hS_cov_rep hf'_irr hf'_dvd_target hS'_J hS'_rep hnot_assoc)
                hmin_in_S_cov hmin_in_S')
            have hSeq : S_cov = S' :=
              hpartition.unique_up_to_associated hf_cov_irr hf_cov_dvd_target hS_cov_J
                hS_cov_rep hf'_irr hf'_dvd_target hS'_J hS'_rep hassoc
            have hS_cov_sub_T : S_cov ⊆ T := hSeq ▸ hS'_sub_T
            have hT_eq : T = S_cov :=
              (Finset.eq_of_subset_of_card_le hS_cov_sub_T (by omega)).symm
            rw [hT_eq] at hquot hTrej
            rw [hquot_scov] at hquot
            have hquot_eq_scov : quotient = quotient_scov := (Option.some.inj hquot).symm
            subst quotient
            have hquot_mul : quotient_scov * f_cov = target := by
              rw [← hrec_eq]; exact hmul_scov
            have hquot_dvd_target : quotient_scov ∣ target := ⟨f_cov, hquot_mul.symm⟩
            have hquot_dvd_core : quotient_scov ∣ core :=
              zpoly_dvd_trans hquot_dvd_target htarget_dvd_core
            have hquot_primitive : Hex.ZPoly.Primitive quotient_scov :=
              zpoly_primitive_of_dvd_primitive_basic htarget_primitive hquot_dvd_target
            have hquot_lc_pos : 0 < Hex.DensePoly.leadingCoeff quotient_scov :=
              zpoly_left_pos_lc_of_mul_eq_of_pos_lc hquot_mul hf_cov_lc_pos htarget_lc_pos
            have hpartition_new :
                LiftedFactorSubsetPartition core d (J \ S_cov) quotient_scov :=
              liftedFactorSubsetPartition_transport hpartition hquot_mul hS_cov_rep
                hS_cov_J hf_cov_irr hf_cov_dvd_target
            have hsdiff_lt : (J \ S_cov).card < J.card := by
              apply Finset.card_lt_card
              rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
              exact ⟨J.min' hJ_ne, J.min'_mem hJ_ne,
                fun hc => (Finset.mem_sdiff.mp hc).2 hmin_in_S_cov⟩
            have hfuel_new : (budget - 1) + smartFuelBound (J \ S_cov).card ≤ fuel' := by
              have hbound := smartFuelBound_le_smartLoopFuelBound
                (m := (J \ S_cov).card) (n := J.card) (by omega)
              omega
            split at h
            · -- Aux = (some sub, ab): PEEL, `result = f_cov :: sub`
              rename_i ab haux
              rw [hsplit2, hTrej] at haux
              simp only [Prod.mk.injEq, Option.some.injEq] at h
              obtain ⟨hresult, _⟩ := h
              subst hresult
              -- `factor ∣ target = quotient_scov * f_cov`
              have hfactor_prime : Prime (HexPolyZMathlib.toPolynomial factor) :=
                UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
              have hfactor_dvd_prod :
                  HexPolyZMathlib.toPolynomial factor ∣
                    HexPolyZMathlib.toPolynomial quotient_scov *
                      HexPolyZMathlib.toPolynomial f_cov := by
                rw [← HexPolyZMathlib.toPolynomial_mul, hquot_mul]
                exact HexPolyMathlib.toPolynomial_dvd hfactor_dvd
              rcases hfactor_prime.dvd_or_dvd hfactor_dvd_prod with hdvd_q | hdvd_fcov
              · -- factor divides the quotient: covered by the recursive `Aux`
                have hfactor_dvd_q : factor ∣ quotient_scov := by
                  rcases hdvd_q with ⟨r, hr⟩
                  refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
                  apply HexPolyZMathlib.equiv.injective
                  simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
                    HexPolyZMathlib.toPolynomial_ofPolynomial]
                  exact hr
                obtain ⟨emitted, hemitted_mem, hemitted_assoc⟩ :=
                  smartAux_covers_of_bound B' hcore_lc_le hvalid hcore_ne hcore_primitive
                    hcore_lc_pos hd_modulus hd_liftedFactor_monic
                    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
                    hquot_primitive hquot_lc_pos hquot_dvd_core hpartition_new
                    LiftedFactorListMatches.sdiff_of_subset hfuel_new haux factor
                    hfactor_irr hfactor_dvd_q
                exact ⟨emitted, List.mem_cons_of_mem _ hemitted_mem, hemitted_assoc⟩
              · -- factor is associated to the emitted head `f_cov`
                refine ⟨_, List.mem_cons_self, ?_⟩
                rw [hcand_raw, hT_eq, hrec_eq]
                exact (hfactor_irr.associated_of_dvd hf_cov_irr hdvd_fcov).symm
            · -- Aux = (none, ab): completeness forces `ab = 0`, contradicting `some`
              rename_i ab haux
              rw [hsplit2, hTrej] at haux
              have hab : ab = 0 :=
                smartAux_none_budget_zero B' hcore_lc_le hvalid hcore_ne hcore_primitive
                  hcore_lc_pos hd_modulus hd_liftedFactor_monic
                  hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
                  hquot_primitive hquot_lc_pos hquot_dvd_core hpartition_new
                  LiftedFactorListMatches.sdiff_of_subset hfuel_new haux
              rw [hab, Hex.scaledRecombinationSmartCandLoop_budget_zero] at h
              simp at h
          · -- exactQuotient? = none: recurse on `rest`
            rename_i hquot_none
            exact smartCandLoop_covers_of_bound B' hcore_lc_le hvalid hcore_ne
              hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
              hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
              htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
              hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
              hk_le (fun s hs => hsplits_enum s (List.mem_cons_of_mem _ hs))
              (by omega) h factor hfactor_irr hfactor_dvd
        · -- candidate not recorded: recurse on `rest`
          rename_i hrecord_false
          exact smartCandLoop_covers_of_bound B' hcore_lc_le hvalid hcore_ne
            hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
            hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
            htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
            hf_cov_irr hf_cov_dvd_target hS_cov_J hJ_ne hmin_in_S_cov hS_cov_rep
            hk_le (fun s hs => hsplits_enum s (List.mem_cons_of_mem _ hs))
            (by omega) h factor hfactor_irr hfactor_dvd
termination_by fuel

end

/-- Bound-parameterized public conditional coverage for the size-ordered
classical recombination search: the same statement as `RecoveredSmartSearch.covers`
but with the abstract coefficient bound `B'` surfaced as a parameter, together
with its leading-coefficient bound and all-divisors validity.  This exposes the
private `smartAux_covers_of_bound` so callers whose lift precision is controlled
by a *different* bound than `defaultFactorCoeffBound core` (for instance a factor
of a larger `f` bounded by `defaultFactorCoeffBound f` via Mignotte) can still
use coverage.  `RecoveredSmartSearch.covers` is the `B' = defaultFactorCoeffBound
core` specialization. -/
theorem RecoveredSmartSearch.covers_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {budget fuel : Nat}
      {result : List Hex.ZPoly} {b : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      budget + smartFuelBound J.card ≤ fuel →
      Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors budget fuel = (some result, b) →
      ∀ factor : Hex.ZPoly,
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ target →
        ∃ emitted ∈ result,
          Associated (HexPolyZMathlib.toPolynomial emitted)
            (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors budget fuel result b htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel h
  exact smartAux_covers_of_bound B' hcore_lc_le hvalid hcore_ne hcore_primitive
    hcore_lc_pos hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
    hd_liftedFactor_inj hprecision htarget_primitive htarget_lc_pos htarget_dvd_core
    hpartition hmatches hfuel h

/-- Public conditional coverage for the size-ordered classical recombination
search (smart analogue of `RecoveredScaledSearch.covers`): when the search
returns `some result`, every irreducible factor of `target` is an associate of
some emitted factor.  The abstract bound is instantiated at
`Hex.ZPoly.defaultFactorCoeffBound core`. -/
theorem RecoveredSmartSearch.covers
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {budget fuel : Nat}
      {result : List Hex.ZPoly} {b : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      budget + smartFuelBound J.card ≤ fuel →
      Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors budget fuel = (some result, b) →
      ∀ factor : Hex.ZPoly,
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ target →
        ∃ emitted ∈ result,
          Associated (HexPolyZMathlib.toPolynomial emitted)
            (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors budget fuel result b htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel h
  exact RecoveredSmartSearch.covers_of_bound (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
    (defaultFactorCoeffBound_valid core hcore_ne) hcore_ne hcore_primitive hcore_lc_pos
    hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
    hprecision htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
    hfuel h

/-- Bound-parameterized public trustworthy-none completeness: the same statement
as `RecoveredSmartSearch.trustworthyNone` but with the abstract coefficient bound
`B'` surfaced as a parameter, exposing the private `smartAux_none_budget_zero`.
`RecoveredSmartSearch.trustworthyNone` is the `B' = defaultFactorCoeffBound core`
specialization. -/
theorem RecoveredSmartSearch.trustworthyNone_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {budget fuel b : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      budget + smartFuelBound J.card ≤ fuel →
      Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors budget fuel = (none, b) →
      b = 0 := by
  intro target J localFactors budget fuel b htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel h
  exact smartAux_none_budget_zero B' hcore_lc_le hvalid hcore_ne hcore_primitive
    hcore_lc_pos hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
    hd_liftedFactor_inj hprecision htarget_primitive htarget_lc_pos htarget_dvd_core
    hpartition hmatches hfuel h

/-- Public trustworthy-none completeness: with adequate fuel a `none` return of
the size-ordered search can only come from budget exhaustion (`b = 0`). -/
theorem RecoveredSmartSearch.trustworthyNone
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {budget fuel b : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      budget + smartFuelBound J.card ≤ fuel →
      Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors budget fuel = (none, b) →
      b = 0 := by
  intro target J localFactors budget fuel b htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel h
  exact RecoveredSmartSearch.trustworthyNone_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
    (defaultFactorCoeffBound_valid core hcore_ne) hcore_ne hcore_primitive hcore_lc_pos
    hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
    hprecision htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
    hfuel h

end

end HexBerlekampZassenhausMathlib
