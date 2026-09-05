/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.CombinationIterator
public import HexBerlekampZassenhaus.Classical.Search
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.ModularPolynomial

public section
set_option backward.proofsInPublic true

/-!
# Completeness of direct head-forced recombination

The executable search enumerates indexed lifted supports.  This file proves
that every true support survives the cheap prefilters and reaches exact
division, then identifies accepted supports through the modular partition.
-/

namespace HexBerlekampZassenhausMathlib

/-- A successful head search occurs no later than any known successful
cardinality level.  The proof uses the streaming iterator completeness theorem
at that known level; a later result would require that level to have been
exhausted, which is impossible. -/
theorem findDirectHead_found_le
    (coreLc : Int) (target : Hex.ZPoly) (basis : Hex.LiftData)
    (head : Hex.DirectLiftedIndex basis)
    (tail : List (Hex.DirectLiftedIndex basis))
    {trueSelected trueRemaining :
      List (Hex.DirectLiftedIndex basis)}
    {trueLevel : Nat}
    (htrueMem :
      (trueSelected, trueRemaining) ∈
        Hex.subsetsOfSizeWithComplement tail trueLevel)
    {trueCandidate trueQuotient : Hex.ZPoly}
    (htrue :
      Hex.tryDirectSplit coreLc target basis
          (head :: trueSelected) =
        some (trueCandidate, trueQuotient)) :
    ∀ (levels : List Nat),
      List.Pairwise (· < ·) levels →
      trueLevel ∈ levels →
      ∀ budget candidates completed split budget' candidates' completed',
        Hex.findDirectHead coreLc target basis head tail levels
            budget candidates completed =
          .found split budget' candidates' completed' →
        ∃ level selected remaining,
          (selected, remaining) ∈
              Hex.subsetsOfSizeWithComplement tail level ∧
            split.selected = head :: selected ∧
            split.remaining = remaining ∧
            Hex.tryDirectSplit coreLc target basis split.selected =
              some (split.candidate, split.quotient) ∧
            level ≤ trueLevel := by
  intro levels
  induction levels with
  | nil =>
      intro _ hmem
      simp at hmem
  | cons level levels ih =>
      intro hsorted hcontains budget candidates completed split
        budget' candidates' completed' hfind
      simp only [Hex.findDirectHead] at hfind
      split at hfind
      · contradiction
      · generalize hscan :
          Hex.scanDirectLevel coreLc target basis head tail level = result
          at hfind
        cases result with
        | found foundSplit tried =>
            cases hfind
            obtain ⟨selected, remaining, hmem, hselected, hremaining, heval⟩ :=
              scanDirectCombinations_found coreLc target basis
                (Hex.liftSupport basis) (Hex.targetImage target) head tail level [] []
                ((Hex.directLiftedFactor basis head).degree?.getD 0)
                ((Hex.directLiftedFactor basis head).coeff 0 %
                  (Hex.liftModulus basis : Int))
                split tried
                (by simp [Hex.directSelectedDegree,
                  Hex.directSelectedFactors])
                (by simp [Hex.directSelectedTrail,
                  Hex.directSelectedFactors])
                (by simpa [Hex.scanDirectLevel] using hscan)
            refine ⟨level, selected, remaining, hmem, ?_, ?_, heval, ?_⟩
            · simpa using hselected
            · simpa using hremaining
            · rcases List.mem_cons.mp hcontains with hlevel | hrest
              · omega
              · exact Nat.le_of_lt
                  ((List.pairwise_cons.mp hsorted).1 trueLevel hrest)
        | exhausted tried =>
            by_cases heq : level = trueLevel
            · subst level
              obtain ⟨foundSplit, foundTried, hfound⟩ :=
                scanDirectCombinations_finds coreLc target basis
                  (Hex.liftSupport basis) (Hex.targetImage target) head tail trueLevel
                  [] []
                  ((Hex.directLiftedFactor basis head).degree?.getD 0)
                  ((Hex.directLiftedFactor basis head).coeff 0 %
                    (Hex.liftModulus basis : Int))
                  trueSelected trueRemaining trueCandidate trueQuotient
                  (by simp [Hex.directSelectedDegree,
                    Hex.directSelectedFactors])
                  (by simp [Hex.directSelectedTrail,
                    Hex.directSelectedFactors])
                  htrueMem (by simpa using htrue)
              have hfoundLevel :
                  Hex.scanDirectLevel coreLc target basis head tail trueLevel =
                    .found foundSplit foundTried := by
                simpa [Hex.scanDirectLevel] using hfound
              rw [hfoundLevel] at hscan
              contradiction
            · have hcontains' : trueLevel ∈ levels := by
                rcases List.mem_cons.mp hcontains with hlevel | hrest
                · exact False.elim (heq hlevel.symm)
                · exact hrest
              exact ih (List.pairwise_cons.mp hsorted).2 hcontains'
                (budget - tried) (candidates + tried)
                (completed.push level) split budget' candidates' completed'
                hfind


private theorem foldl_mul_emod_eq
    (f : α → Int) (m : Int) (xs : List α) :
    ∀ a : Int,
      xs.foldl (fun acc x => acc * f x % m) a % m =
        a * (xs.map f).prod % m := by
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
      intro a
      rw [List.foldl_cons, List.map_cons, List.prod_cons,
        ih (a * f x % m)]
      conv_lhs => rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      rw [mul_assoc]

private theorem directSelectedTrail_emod_eq_prod_emod
    (basis : Hex.LiftData)
    (selected : List (Hex.DirectLiftedIndex basis)) :
    Hex.directSelectedTrail basis selected % (Hex.liftModulus basis : Int) =
      ((Hex.directSelectedFactors basis selected).map
        (fun g => g.coeff 0)).prod % (Hex.liftModulus basis : Int) := by
  unfold Hex.directSelectedTrail
  simpa using
    (foldl_mul_emod_eq (fun g : Hex.ZPoly => g.coeff 0)
      (Hex.liftModulus basis : Int)
      (Hex.directSelectedFactors basis selected) 1)

private theorem polyProduct_coeff_zero (xs : List Hex.ZPoly) :
    (Array.polyProduct xs.toArray).coeff 0 =
      (xs.map (fun g => g.coeff 0)).prod := by
  rw [← HexPolyZMathlib.coeff_toPolynomial, polyProduct_toPolynomial,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_list_prod]
  simp only [List.map_map]
  congr 1
  exact List.map_congr_left fun g _ => by
    rw [Function.comp_apply, ← Polynomial.coeff_zero_eq_eval_zero,
      HexPolyZMathlib.coeff_toPolynomial]

private theorem directSelectedDegree_eq_sum
    (basis : Hex.LiftData)
    (selected : List (Hex.DirectLiftedIndex basis)) :
    Hex.directSelectedDegree basis selected =
      (selected.map fun i =>
        (HexPolyZMathlib.toPolynomial
          (liftedFactor basis i)).natDegree).sum := by
  have haux : ∀ (xs : List (Hex.DirectLiftedIndex basis)) (a : Nat),
      xs.foldl
          (fun sum i =>
            sum + (Hex.directLiftedFactor basis i).degree?.getD 0) a =
        a + (xs.map fun i =>
          (Hex.directLiftedFactor basis i).degree?.getD 0).sum := by
    intro xs
    induction xs with
    | nil => intro a; simp
    | cons x xs ih =>
        intro a
        rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]
  unfold Hex.directSelectedDegree Hex.directSelectedFactors
  rw [List.foldl_map, haux, Nat.zero_add]
  simp only [Hex.directLiftedFactor]
  congr 1
  exact List.map_congr_left fun i _ => by
    exact (HexPolyMathlib.natDegree_toPolynomial (liftedFactor basis i)).symm

/-- A true modular support passes both cheap direct-candidate prefilters. -/
theorem directCandidatePrefilter_trueSupport
    {core target factor quotient : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    (facts : DirectLiftFacts core B data)
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (htarget_ne : target ≠ 0)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    {selected :
      List (Hex.DirectLiftedIndex
        (Hex.ZPoly.directLiftData core B data))}
    (hnodup : selected.Nodup)
    (hcandidate :
      directSupportCandidate core B data
          (modPSubsetOfLiftedSubset data
            (Hex.ZPoly.directLiftData core B data)
            (henselLiftData_liftedFactors_size_eq
              (Hex.ZPoly.monicTarget core data.p
                (Hex.precisionForCoeffBound B data.p))
              (Hex.precisionForCoeffBound B data.p) data)
            selected.toFinset) =
        factor)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ target)
    (hproduct : quotient * factor = target) :
    Hex.directCandidatePrefilter
        (Hex.DensePoly.leadingCoeff core) target
        (Hex.LiftModulus.ofNat
          (Hex.liftModulus (Hex.ZPoly.directLiftData core B data)))
        (Hex.directSelectedDegree (Hex.ZPoly.directLiftData core B data) selected)
        (Hex.directSelectedTrail (Hex.ZPoly.directLiftData core B data) selected) =
      true := by
  let d := Hex.ZPoly.directLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  let T : LiftedFactorSubset d := selected.toFinset
  have hcand :
      Hex.directCandidate (Hex.DensePoly.leadingCoeff core)
          (Hex.liftModulus d) (Hex.directSelectedFactors d selected) =
        factor := by
    rw [show Hex.liftModulus d = d.p ^ d.k from rfl,
      directCandidate_indexed_eq core d selected hnodup]
    have htransport :
        liftedSubsetOfModPSubset data d hsize
            (modPSubsetOfLiftedSubset data d hsize T) = T :=
      liftedSubset_modPSubset data d hsize T
    simpa [directSupportCandidate, d, hsize, T, htransport] using hcandidate
  have hfactor_ne : factor ≠ 0 := by
    intro hzero
    exact hfactor_irr.ne_zero
      (by rw [hzero]; exact HexPolyZMathlib.toPolynomial_zero)
  have hdegree_candidate :
      (HexPolyZMathlib.toPolynomial factor).natDegree =
        ∑ i ∈ T,
          (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
    rw [← hcand, show Hex.liftModulus d = d.p ^ d.k from rfl,
      directCandidate_indexed_eq core d selected hnodup]
    exact natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum
      hcore_ne hcore_lc_pos facts.liftedMonic hprecision T
  have hdegree_list :
      Hex.directSelectedDegree d selected =
        ∑ i ∈ T,
          (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
    rw [directSelectedDegree_eq_sum]
    exact (List.sum_toFinset
      (f := fun i : Hex.DirectLiftedIndex d =>
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
      hnodup).symm
  have hdegree :
      Hex.directSelectedDegree d selected ≤ target.degree?.getD 0 := by
    rw [hdegree_list, ← hdegree_candidate]
    exact natDegree_toPolynomial_le_degree_getD_of_dvd
      target factor htarget_ne hfactor_dvd
  have htrail :
      Hex.centeredModNat
          (Hex.DensePoly.leadingCoeff core *
            Hex.directSelectedTrail d selected)
          (Hex.liftModulus d) =
        (Hex.centeredLiftPoly
          (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
            (Array.polyProduct
              (Hex.directSelectedFactors d selected).toArray))
          (Hex.liftModulus d)).coeff 0 := by
    rw [Hex.coeff_centeredLiftPoly,
      Hex.DensePoly.coeff_scale (R := Int)
        (Hex.DensePoly.leadingCoeff core)
        (Array.polyProduct
          (Hex.directSelectedFactors d selected).toArray) 0
        (Int.mul_zero _),
      polyProduct_coeff_zero,
      ]
    have hres :=
      directSelectedTrail_emod_eq_prod_emod d selected
    calc
      Hex.centeredModNat
          (Hex.DensePoly.leadingCoeff core *
            Hex.directSelectedTrail d selected)
          (Hex.liftModulus d) =
        Hex.centeredModNat
          ((Hex.DensePoly.leadingCoeff core *
            Hex.directSelectedTrail d selected) %
              (Hex.liftModulus d : Int))
          (Hex.liftModulus d) := by
            rw [Hex.centeredModNat_emod_self]
      _ = Hex.centeredModNat
          ((Hex.DensePoly.leadingCoeff core *
            ((Hex.directSelectedFactors d selected).map
              (fun g => g.coeff 0)).prod) %
              (Hex.liftModulus d : Int))
          (Hex.liftModulus d) := by
            congr 1
            rw [Int.mul_emod, hres, ← Int.mul_emod]
      _ = Hex.centeredModNat
          (Hex.DensePoly.leadingCoeff core *
            ((Hex.directSelectedFactors d selected).map
              (fun g => g.coeff 0)).prod)
          (Hex.liftModulus d) := by
            rw [Hex.centeredModNat_emod_self]
  have htrail_dvd :
      Hex.centeredModNat
          (Hex.DensePoly.leadingCoeff core *
            Hex.directSelectedTrail d selected)
          (Hex.liftModulus d) ∣
        Hex.DensePoly.leadingCoeff core * target.coeff 0 := by
    let product :=
      Array.polyProduct (Hex.directSelectedFactors d selected).toArray
    let scaled :=
      Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) product
    let raw := Hex.centeredLiftPoly scaled (Hex.liftModulus d)
    let pp := Hex.ZPoly.primitivePart raw
    have hnorm : Hex.normalizeFactorSign pp = factor := by
      simpa [Hex.directCandidate, product, scaled, raw, pp] using hcand
    have hproduct_monic : Hex.DensePoly.Monic product := by
      apply polyProduct_monic_of_all_monic
      intro g hg
      rw [List.toList_toArray] at hg
      simp only [Hex.directSelectedFactors, List.mem_map] at hg
      obtain ⟨i, _, rfl⟩ := hg
      exact facts.liftedMonic i
    have hscaled_lc :
        Hex.DensePoly.leadingCoeff scaled =
          Hex.DensePoly.leadingCoeff core := by
      unfold scaled
      rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
        (Hex.DensePoly.leadingCoeff core) product (ne_of_gt hcore_lc_pos),
        show Hex.DensePoly.leadingCoeff product = 1 from hproduct_monic,
        mul_one]
    have hraw_lc :
        Hex.DensePoly.leadingCoeff raw =
          Hex.DensePoly.leadingCoeff core := by
      unfold raw
      calc
        Hex.DensePoly.leadingCoeff
            (Hex.centeredLiftPoly scaled (Hex.liftModulus d)) =
            Hex.DensePoly.leadingCoeff scaled :=
          leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound
            (show 0 < Hex.DensePoly.leadingCoeff scaled by
              rw [hscaled_lc]; exact hcore_lc_pos)
            (show (Hex.DensePoly.leadingCoeff scaled).natAbs ≤
                Hex.ZPoly.defaultFactorCoeffBound core by
              rw [hscaled_lc]
              exact defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
            (by
              change 2 * Hex.ZPoly.defaultFactorCoeffBound core <
                data.p ^ Hex.precisionForCoeffBound B data.p
              exact hprecision)
        _ = Hex.DensePoly.leadingCoeff core := hscaled_lc
    have hraw_size : 0 < raw.size := by
      apply Hex.ZPoly.size_pos_of_ne_zero
      intro hzero
      rw [hzero] at hraw_lc
      simp at hraw_lc
      exact (ne_of_gt hcore_lc_pos) hraw_lc.symm
    have hcontent_dvd_core :
        Hex.ZPoly.content raw ∣ Hex.DensePoly.leadingCoeff core := by
      rw [← hraw_lc,
        Hex.DensePoly.leadingCoeff_eq_coeff_last raw hraw_size]
      exact Hex.ZPoly.content_dvd_coeff raw (raw.size - 1)
    have hpp0_dvd_factor0 : pp.coeff 0 ∣ factor.coeff 0 := by
      rw [← hnorm]
      unfold Hex.normalizeFactorSign
      split
      · rw [Hex.DensePoly.coeff_scale (R := Int) (-1) pp 0
            (Int.mul_zero _)]
        simp
      · exact dvd_rfl
    have hraw_coeff :
        raw.coeff 0 =
          Hex.ZPoly.content raw * pp.coeff 0 := by
      conv_lhs => rw [← Hex.ZPoly.content_mul_primitivePart raw]
      exact Hex.DensePoly.coeff_scale (R := Int)
        (Hex.ZPoly.content raw) pp 0 (Int.mul_zero _)
    have htarget_coeff :
        target.coeff 0 = quotient.coeff 0 * factor.coeff 0 := by
      have hcoeff := congrArg (fun p : Polynomial Int => p.coeff 0)
        (congrArg HexPolyZMathlib.toPolynomial hproduct)
      simpa [HexPolyZMathlib.toPolynomial_mul, Polynomial.mul_coeff_zero,
        HexPolyZMathlib.coeff_toPolynomial] using hcoeff.symm
    obtain ⟨a, ha⟩ := hcontent_dvd_core
    obtain ⟨b, hb⟩ := hpp0_dvd_factor0
    refine ⟨a * quotient.coeff 0 * b, ?_⟩
    rw [htrail, hraw_coeff, ha, htarget_coeff, hb]
    ring
  unfold Hex.directCandidatePrefilter Hex.directDegreePrefilter
  rw [Hex.directTrailingPrefilter_eq]
  simp only [Hex.LiftModulus.nat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · simpa [ne_of_gt hcore_lc_pos, htarget_ne] using hdegree
  · simpa [Hex.intDivides_eq] using
      (Int.emod_eq_zero_of_dvd htrail_dvd)

/-- A recovered true support reaches the successful exact-division leaf of the
executable iterator. -/
theorem tryDirectSplit_trueSupport
    {core target factor quotient : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    (facts : DirectLiftFacts core B data)
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (htarget_ne : target ≠ 0)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    {selected :
      List (Hex.DirectLiftedIndex
        (Hex.ZPoly.directLiftData core B data))}
    (hnodup : selected.Nodup)
    (hcandidate :
      directSupportCandidate core B data
          (modPSubsetOfLiftedSubset data
            (Hex.ZPoly.directLiftData core B data)
            (henselLiftData_liftedFactors_size_eq
              (Hex.ZPoly.monicTarget core data.p
                (Hex.precisionForCoeffBound B data.p))
              (Hex.precisionForCoeffBound B data.p) data)
            selected.toFinset) =
        factor)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ target)
    (hfactor_lc_pos : 0 < Hex.DensePoly.leadingCoeff factor)
    (hfactor_degree_pos : 0 < factor.degree?.getD 0)
    (hproduct : quotient * factor = target) :
    Hex.tryDirectSplit
        (Hex.DensePoly.leadingCoeff core) target
        (Hex.ZPoly.directLiftData core B data) selected =
      some (factor, quotient) := by
  let d := Hex.ZPoly.directLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  have hcand :
      Hex.directCandidate (Hex.DensePoly.leadingCoeff core)
          (Hex.liftModulus d) (Hex.directSelectedFactors d selected) =
        factor := by
    rw [show Hex.liftModulus d = d.p ^ d.k from rfl,
      directCandidate_indexed_eq core d selected hnodup]
    have htransport :
        liftedSubsetOfModPSubset data d hsize
            (modPSubsetOfLiftedSubset data d hsize selected.toFinset) =
          selected.toFinset :=
      liftedSubset_modPSubset data d hsize selected.toFinset
    simpa [directSupportCandidate, d, hsize, htransport] using hcandidate
  have hpre :=
    directCandidatePrefilter_trueSupport facts hcore_ne hcore_lc_pos
      htarget_ne hprecision hnodup hcandidate hfactor_irr hfactor_dvd hproduct
  have hrecord : Hex.shouldRecordPolynomialFactor factor = true := by
    have hne_zero : factor ≠ 0 := by
      intro hzero
      rw [hzero] at hfactor_degree_pos
      simp [Hex.DensePoly.degree?] at hfactor_degree_pos
    have hne_one : factor ≠ 1 := by
      intro hone
      rw [hone] at hfactor_degree_pos
      change 0 <
        (Hex.DensePoly.C (1 : Int)).degree?.getD 0 at hfactor_degree_pos
      rw [Hex.DensePoly.degree?_C_getD] at hfactor_degree_pos
      omega
    have hne_neg_one : factor ≠ Hex.DensePoly.C (-1 : Int) := by
      intro hneg
      rw [hneg] at hfactor_degree_pos
      rw [Hex.DensePoly.degree?_C_getD] at hfactor_degree_pos
      omega
    unfold Hex.shouldRecordPolynomialFactor
    simp [hne_zero, hne_one, hne_neg_one]
  have hquot :
      Hex.exactQuotient? target factor = some quotient :=
    Hex.exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
      hfactor_lc_pos hfactor_degree_pos hproduct
  unfold Hex.tryDirectSplit Hex.tryDirectCandidate
    Hex.directCandidateAfterPrefilter
  have hcand_prepared :
      Hex.directCandidate (Hex.DensePoly.leadingCoeff core)
          (Hex.LiftModulus.ofNat (Hex.liftModulus d)).nat
          (Hex.directSelectedFactors d selected) =
        factor := hcand
  rw [hpre]
  simp only [ite_true]
  rw [hcand_prepared, hrecord, hquot]
  rfl

/-- Any successful indexed split containing the distinguished modular index
contains the whole true support of the corresponding irreducible factor. -/
theorem tryDirectSplit_containsSupport
    {core target factor candidate quotient : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    {J S : ModPFactorSubset data}
    (hpartition : DirectSupportPartition core B data J target)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ target)
    (hSJ : S ⊆ J)
    (hfactor_rep : RepresentsIntegerFactorModP data factor S)
    (hrecover : directSupportCandidate core B data S = factor)
    {selected :
      List (Hex.DirectLiftedIndex
        (Hex.ZPoly.directLiftData core B data))}
    (hnodup : selected.Nodup)
    (htry :
      Hex.tryDirectSplit (Hex.DensePoly.leadingCoeff core) target
          (Hex.ZPoly.directLiftData core B data) selected =
        some (candidate, quotient))
    {i : ModPFactorIndex data} (hiS : i ∈ S)
    (hiSelected :
      i ∈ modPSubsetOfLiftedSubset data
        (Hex.ZPoly.directLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset) :
    S ⊆
      modPSubsetOfLiftedSubset data
        (Hex.ZPoly.directLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset := by
  let d := Hex.ZPoly.directLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  let T : ModPFactorSubset data :=
    modPSubsetOfLiftedSubset data d hsize selected.toFinset
  obtain ⟨hcandidate, hproduct⟩ := tryDirectSplit_some htry
  have hcandidate_eq :
      directSupportCandidate core B data T = candidate := by
    rw [hcandidate, show Hex.liftModulus d = d.p ^ d.k from rfl,
      directCandidate_indexed_eq core d selected hnodup]
    have htransport :
        liftedSubsetOfModPSubset data d hsize T = selected.toFinset := by
      exact liftedSubset_modPSubset data d hsize selected.toFinset
    simp [directSupportCandidate, d, T, htransport]
  have hcandidate_dvd :
      directSupportCandidate core B data T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [hcandidate_eq]
    rw [← hproduct]
    exact Hex.DensePoly.mul_comm_poly quotient candidate
  exact hpartition.supportSubsetCandidate hval facts hcore_degree_pos
    hprecision hgcd hfactor_irr hfactor_dvd hSJ hfactor_rep hrecover
    hiS (by simpa [T, d, hsize] using hiSelected) hcandidate_dvd

/-- At or below the true support cardinality, a successful head-containing
split is exactly that support. -/
theorem tryDirectSplit_eqSupport_of_card_le
    {core target factor candidate quotient : Hex.ZPoly}
    {B : Nat} {data : Hex.PrimeChoiceData}
    {J S : ModPFactorSubset data}
    (hpartition : DirectSupportPartition core B data J target)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ target)
    (hSJ : S ⊆ J)
    (hfactor_rep : RepresentsIntegerFactorModP data factor S)
    (hrecover : directSupportCandidate core B data S = factor)
    {selected :
      List (Hex.DirectLiftedIndex
        (Hex.ZPoly.directLiftData core B data))}
    (hnodup : selected.Nodup)
    (htry :
      Hex.tryDirectSplit (Hex.DensePoly.leadingCoeff core) target
          (Hex.ZPoly.directLiftData core B data) selected =
        some (candidate, quotient))
    {i : ModPFactorIndex data} (hiS : i ∈ S)
    (hiSelected :
      i ∈ modPSubsetOfLiftedSubset data
        (Hex.ZPoly.directLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset)
    (hcard :
      (modPSubsetOfLiftedSubset data
        (Hex.ZPoly.directLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset).card ≤ S.card) :
    modPSubsetOfLiftedSubset data
        (Hex.ZPoly.directLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset =
      S := by
  have hsub :=
    tryDirectSplit_containsSupport hpartition hval facts hcore_degree_pos
      hprecision hgcd hfactor_irr hfactor_dvd hSJ hfactor_rep hrecover
      hnodup htry hiS hiSelected
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

end HexBerlekampZassenhausMathlib
