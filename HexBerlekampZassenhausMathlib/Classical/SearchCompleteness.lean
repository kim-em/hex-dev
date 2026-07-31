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
              scanDirectCombinations_found coreLc target basis head
                tail level [] [] split tried
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
                scanDirectCombinations_finds coreLc target basis head
                  tail trueLevel [] [] trueSelected trueRemaining
                  trueCandidate trueQuotient htrueMem (by simpa using htrue)
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

private theorem centeredModNat_emod_left (z : Int) (m : Nat) :
    Hex.centeredModNat (z % (m : Int)) m = Hex.centeredModNat z m := by
  unfold Hex.centeredModNat
  by_cases hm : m = 0
  · simp [hm]
  · rw [if_neg hm, if_neg hm]
    have hz : z % (m : Int) % Int.ofNat m = z % Int.ofNat m := by
      show z % (m : Int) % (m : Int) = z % (m : Int)
      rw [Int.emod_emod]
    rw [hz]

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

private theorem directSelectedTrail_eq_centered_prod
    (basis : Hex.LiftData)
    (selected : List (Hex.DirectLiftedIndex basis)) :
    Hex.centeredModNat
        (Hex.directSelectedTrail basis selected)
        (Hex.liftModulus basis) =
      Hex.centeredModNat
        ((Hex.directSelectedFactors basis selected).map
          (fun g => g.coeff 0)).prod
        (Hex.liftModulus basis) := by
  unfold Hex.directSelectedTrail
  rw [← centeredModNat_emod_left
      ((Hex.directSelectedFactors basis selected).foldl
        (fun residue factor =>
          residue * factor.coeff 0 % (Hex.liftModulus basis : Int)) 1)
      (Hex.liftModulus basis),
    foldl_mul_emod_eq (fun g : Hex.ZPoly => g.coeff 0)
      (Hex.liftModulus basis)
      (Hex.directSelectedFactors basis selected) 1,
    one_mul, centeredModNat_emod_left]

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
        (Hex.ZPoly.coreLiftData core B data))}
    (hnodup : selected.Nodup)
    (hcandidate :
      directSupportCandidate core B data
          (modPSubsetOfLiftedSubset data
            (Hex.ZPoly.coreLiftData core B data)
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
        (Hex.liftModulus (Hex.ZPoly.coreLiftData core B data))
        (Hex.directSelectedDegree (Hex.ZPoly.coreLiftData core B data) selected)
        (Hex.directSelectedTrail (Hex.ZPoly.coreLiftData core B data) selected) =
      true := by
  let d := Hex.ZPoly.coreLiftData core B data
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
  have htrail_safe :
      Hex.centeredModNat
          (Hex.DensePoly.leadingCoeff core *
            Hex.directSelectedTrail d selected)
          (Hex.liftModulus d) ≠ 0 ∨
        target.coeff 0 = 0 := by
    by_cases hraw0 :
        Hex.centeredModNat
            (Hex.DensePoly.leadingCoeff core *
              Hex.directSelectedTrail d selected)
            (Hex.liftModulus d) = 0
    · right
      let raw :=
        Hex.centeredLiftPoly
          (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
            (Array.polyProduct
              (Hex.directSelectedFactors d selected).toArray))
          (Hex.liftModulus d)
      let pp := Hex.ZPoly.primitivePart raw
      have hnorm : Hex.normalizeFactorSign pp = factor := by
        simpa [Hex.directCandidate, raw, pp] using hcand
      have hpp_ne : pp ≠ 0 := by
        intro hzero
        apply hfactor_ne
        rw [← hnorm, hzero]
        rfl
      have hraw_ne : raw ≠ 0 := by
        intro hzero
        apply hpp_ne
        change Hex.ZPoly.primitivePart raw = 0
        rw [hzero]
        rfl
      have hcontent_ne : Hex.ZPoly.content raw ≠ 0 :=
        HexPolyZMathlib.content_ne_zero raw hraw_ne
      have hraw_coeff :
          raw.coeff 0 =
            Hex.ZPoly.content raw * pp.coeff 0 := by
        conv_lhs => rw [← Hex.ZPoly.content_mul_primitivePart raw]
        exact Hex.DensePoly.coeff_scale (R := Int)
          (Hex.ZPoly.content raw) pp 0 (Int.mul_zero _)
      have hpp0 : pp.coeff 0 = 0 := by
        have hz : raw.coeff 0 = 0 := by
          rw [← htrail]
          exact hraw0
        rw [hraw_coeff] at hz
        exact (mul_eq_zero.mp hz).resolve_left hcontent_ne
      have hfactor0 : factor.coeff 0 = 0 := by
        rw [← hnorm]
        unfold Hex.normalizeFactorSign
        split
        · rw [Hex.DensePoly.coeff_scale (R := Int) (-1) pp 0
              (Int.mul_zero _), hpp0, mul_zero]
        · exact hpp0
      have hcoeff := congrArg (fun p : Polynomial Int => p.coeff 0)
        (congrArg HexPolyZMathlib.toPolynomial hproduct)
      rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.mul_coeff_zero,
        HexPolyZMathlib.coeff_toPolynomial,
        HexPolyZMathlib.coeff_toPolynomial, hfactor0,
        HexPolyZMathlib.coeff_toPolynomial, mul_zero] at hcoeff
      exact hcoeff.symm
    · exact Or.inl hraw0
  unfold Hex.directCandidatePrefilter
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · simpa [ne_of_gt hcore_lc_pos, htarget_ne] using hdegree
  · rcases htrail_safe with htrail_ne | htarget0
    · exact Or.inl (by simpa using htrail_ne)
    · exact Or.inr htarget0

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
        (Hex.ZPoly.coreLiftData core B data))}
    (hnodup : selected.Nodup)
    (hcandidate :
      directSupportCandidate core B data
          (modPSubsetOfLiftedSubset data
            (Hex.ZPoly.coreLiftData core B data)
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
        (Hex.ZPoly.coreLiftData core B data) selected =
      some (factor, quotient) := by
  let d := Hex.ZPoly.coreLiftData core B data
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
  rw [hpre]
  simp only [if_true]
  rw [hcand, hrecord, hquot]
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
        (Hex.ZPoly.coreLiftData core B data))}
    (hnodup : selected.Nodup)
    (htry :
      Hex.tryDirectSplit (Hex.DensePoly.leadingCoeff core) target
          (Hex.ZPoly.coreLiftData core B data) selected =
        some (candidate, quotient))
    {i : ModPFactorIndex data} (hiS : i ∈ S)
    (hiSelected :
      i ∈ modPSubsetOfLiftedSubset data
        (Hex.ZPoly.coreLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset) :
    S ⊆
      modPSubsetOfLiftedSubset data
        (Hex.ZPoly.coreLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset := by
  let d := Hex.ZPoly.coreLiftData core B data
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
        (Hex.ZPoly.coreLiftData core B data))}
    (hnodup : selected.Nodup)
    (htry :
      Hex.tryDirectSplit (Hex.DensePoly.leadingCoeff core) target
          (Hex.ZPoly.coreLiftData core B data) selected =
        some (candidate, quotient))
    {i : ModPFactorIndex data} (hiS : i ∈ S)
    (hiSelected :
      i ∈ modPSubsetOfLiftedSubset data
        (Hex.ZPoly.coreLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset)
    (hcard :
      (modPSubsetOfLiftedSubset data
        (Hex.ZPoly.coreLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data)
        selected.toFinset).card ≤ S.card) :
    modPSubsetOfLiftedSubset data
        (Hex.ZPoly.coreLiftData core B data)
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
