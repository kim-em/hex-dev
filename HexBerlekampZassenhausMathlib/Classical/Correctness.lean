/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.SearchCompleteness
public import HexBerlekampZassenhaus.Classical.Engine
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent

public section
set_option backward.proofsInPublic true

/-!
# Correctness of the direct classical search

The recursive invariant says that the executable list of remaining lifted
indices is exactly the lift of the remaining modular support.  The
minimal-head theorem then identifies every accepted split with one irreducible
integer factor and transports the invariant to the exact quotient.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

private theorem zpoly_dvd_trans
    {a b c : Hex.ZPoly} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨q * v, ?_⟩
  rw [hv, hq]
  exact Hex.DensePoly.mul_assoc_poly (S := Int) _ _ _

/-- An irreducible divisor of a primitive integer polynomial has positive
executable degree.  Constant irreducibles are excluded by primitivity of the
target. -/
theorem degree_pos_of_irreducible_dvd_primitive
    {core factor : Hex.ZPoly}
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    0 < factor.degree?.getD 0 := by
  rw [← HexPolyMathlib.natDegree_toPolynomial]
  rcases Nat.eq_zero_or_pos
      (HexPolyZMathlib.toPolynomial factor).natDegree with hzero | hpos
  · exfalso
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hzero
    have hdvd_poly :
        HexPolyZMathlib.toPolynomial factor ∣
          HexPolyZMathlib.toPolynomial core :=
      HexPolyMathlib.toPolynomial_dvd hdvd
    have hcore_poly_prim :
        (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
      HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive core hcore_prim
    have hCa_dvd : Polynomial.C a ∣
        HexPolyZMathlib.toPolynomial core := by
      rw [ha]
      exact hdvd_poly
    have ha_unit : IsUnit a := hcore_poly_prim a hCa_dvd
    exact hirr.not_isUnit (by
      rw [← ha]
      exact Polynomial.isUnit_C.mpr ha_unit)
  · exact hpos

/-- Proof state corresponding to one invocation of `searchDirectAux`. -/
structure DirectSearchInvariant
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (support : ModPFactorSubset data)
    (target : Hex.ZPoly)
    (localFactors :
      List (Hex.DirectLiftedIndex (Hex.ZPoly.coreLiftData core B data))) :
    Prop where
  targetNe : target ≠ 0
  targetDvdCore : target ∣ core
  partition : DirectSupportPartition core B data support target
  localNodup : localFactors.Nodup
  localSupport :
    localFactors.toFinset =
      liftedSubsetOfModPSubset data (Hex.ZPoly.coreLiftData core B data)
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data) support

set_option maxHeartbeats 1000000

/-- The accepted head split is precisely the irreducible support containing
the head, and its remaining list is the exact support complement. -/
theorem findDirectHead_correct
    {core target : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    {J : ModPFactorSubset data}
    {head : Hex.DirectLiftedIndex (Hex.ZPoly.coreLiftData core B data)}
    {tail : List
      (Hex.DirectLiftedIndex (Hex.ZPoly.coreLiftData core B data))}
    (state : DirectSearchInvariant core B data J target (head :: tail))
    {budget candidates : Nat} {completed : Array Nat}
    {split : Hex.DirectSplit (Hex.ZPoly.coreLiftData core B data)}
    {budget' candidates' : Nat} {completed' : Array Nat}
    (hfind :
      Hex.findDirectHead (Hex.DensePoly.leadingCoeff core) target
          (Hex.ZPoly.coreLiftData core B data) head tail
          (List.range (tail.length + 1)) budget candidates completed =
        .found split budget' candidates' completed') :
    ∃ (factor : Hex.ZPoly) (S : ModPFactorSubset data),
      Irreducible (HexPolyZMathlib.toPolynomial factor) ∧
      factor ∣ target ∧
      S ⊆ J ∧
      RepresentsIntegerFactorModP data factor S ∧
      Hex.normalizeFactorSign factor = factor ∧
      split.candidate = factor ∧
      split.quotient * factor = target ∧
      split.selected.toFinset =
        liftedSubsetOfModPSubset data
          (Hex.ZPoly.coreLiftData core B data)
          (henselLiftData_liftedFactors_size_eq
            (Hex.ZPoly.monicTarget core data.p
              (Hex.precisionForCoeffBound B data.p))
            (Hex.precisionForCoeffBound B data.p) data) S ∧
      split.remaining.toFinset =
        liftedSubsetOfModPSubset data
          (Hex.ZPoly.coreLiftData core B data)
          (henselLiftData_liftedFactors_size_eq
            (Hex.ZPoly.monicTarget core data.p
              (Hex.precisionForCoeffBound B data.p))
            (Hex.precisionForCoeffBound B data.p) data)
          (J \ S) ∧
      split.remaining.Nodup := by
  classical
  let d := Hex.ZPoly.coreLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  let headMod : ModPFactorIndex data :=
    modPIndexOfLiftedIndex data d hsize head
  have hheadLift :
      head ∈ liftedSubsetOfModPSubset data d hsize J := by
    rw [← state.localSupport]
    simp
  have hheadIndex :
      liftedIndexOfModPIndex data d hsize headMod = head := by
    apply Fin.ext
    rfl
  have hheadMod : headMod ∈ J := by
    rw [← liftedIndex_mem_liftedSubset_iff data d hsize]
    simpa [hheadIndex] using hheadLift
  obtain ⟨factor, S, hfactor_irr, hfactor_dvd, hSsub,
      hheadS, hfactor_rep, hfactor_norm, hrecover⟩ :=
    state.partition.coverHead headMod hheadMod
  let liftS : LiftedFactorSubset d :=
    liftedSubsetOfModPSubset data d hsize S
  let trueSelected := tail.filter (fun i => decide (i ∈ liftS))
  let trueRemaining := tail.filter (fun i => decide (i ∉ liftS))
  have htail_nodup : tail.Nodup :=
    (List.nodup_cons.mp state.localNodup).2
  have hhead_mem_liftS : head ∈ liftS := by
    rw [← hheadIndex]
    exact
      (liftedIndex_mem_liftedSubset_iff data d hsize S headMod).mpr hheadS
  have hliftS_sub :
      liftS ⊆ (head :: tail).toFinset := by
    rw [state.localSupport]
    intro i hi
    simp only [liftS, liftedSubsetOfModPSubset, Finset.mem_map] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨j, hSsub hj, rfl⟩
  have htrueSupport :
      (head :: trueSelected).toFinset = liftS := by
    ext i
    simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
      trueSelected, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨_, hi⟩)
      · exact hhead_mem_liftS
      · exact hi
    · intro hi
      have hilocal := hliftS_sub hi
      simp only [List.mem_toFinset, List.mem_cons] at hilocal
      rcases hilocal with rfl | hitail
      · exact Or.inl rfl
      · exact Or.inr ⟨hitail, hi⟩
  have htrue_nodup : (head :: trueSelected).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, htail_nodup.filter _⟩
    intro hmem
    exact (List.nodup_cons.mp state.localNodup).1
      (List.mem_of_mem_filter hmem)
  have htrueMem :
      (trueSelected, trueRemaining) ∈
        Hex.subsetsOfSizeWithComplement tail trueSelected.length := by
    simpa [trueRemaining] using
      (filter_split_mem_subsetsOfSizeWithComplement
        (fun i : Hex.DirectLiftedIndex d => decide (i ∈ liftS)) tail)
  have hfactor_core : factor ∣ core :=
    zpoly_dvd_trans hfactor_dvd state.targetDvdCore
  have hfactor_degree :
      0 < factor.degree?.getD 0 :=
    degree_pos_of_irreducible_dvd_primitive hcore_prim hfactor_irr hfactor_core
  have hfactor_ne : factor ≠ 0 := by
    intro hz
    rw [hz] at hfactor_degree
    simp [Hex.DensePoly.degree?] at hfactor_degree
  have hfactor_lc_pos :
      0 < Hex.DensePoly.leadingCoeff factor :=
    leadingCoeff_pos_of_normalized hfactor_ne hfactor_norm
  have hfactor_dvd' : factor ∣ target := hfactor_dvd
  obtain ⟨quotient, hquotient⟩ := hfactor_dvd
  have hproduct : quotient * factor = target := by
    rw [Hex.DensePoly.mul_comm_poly, hquotient]
  have hsupportInverse :
      modPSubsetOfLiftedSubset data d hsize
          (head :: trueSelected).toFinset = S := by
    rw [htrueSupport]
    exact modPSubset_liftedSubset data d hsize S
  have htrueTry :
      Hex.tryDirectSplit (Hex.DensePoly.leadingCoeff core) target d
          (head :: trueSelected) =
        some (factor, quotient) := by
    apply tryDirectSplit_trueSupport facts hcore_ne hcore_lc_pos
      state.targetNe hrecovery htrue_nodup
    · rw [hsupportInverse]
      exact hrecover
    · exact hfactor_irr
    · exact hfactor_dvd'
    · exact hfactor_lc_pos
    · exact hfactor_degree
    · exact hproduct
  obtain ⟨level, selected, remaining, henum, hselected, hremaining,
      htry, hlevel⟩ :=
    findDirectHead_found_le (Hex.DensePoly.leadingCoeff core) target d
      head tail htrueMem htrueTry (List.range (tail.length + 1))
      List.pairwise_lt_range (by
        exact List.mem_range.mpr
          (Nat.lt_succ_of_le (List.length_filter_le _ _)))
      budget candidates completed split budget' candidates' completed' hfind
  obtain ⟨hselectedNodup, hremainingNodup, hdisjoint, hunion, hlength⟩ :=
    subsetsOfSizeWithComplement_structure tail selected remaining level
      htail_nodup henum
  have hsplitNodup : split.selected.Nodup := by
    rw [hselected]
    exact List.nodup_cons.mpr
      ⟨fun hi => (List.nodup_cons.mp state.localNodup).1
        ((Hex.subsetsOfSizeWithComplement_mem tail level
          (selected, remaining) henum).1 head hi),
       hselectedNodup⟩
  let T : ModPFactorSubset data :=
    modPSubsetOfLiftedSubset data d hsize split.selected.toFinset
  have hheadT : headMod ∈ T := by
    rw [← liftedIndex_mem_liftedSubset_iff data d hsize T headMod]
    rw [hheadIndex, liftedSubset_modPSubset]
    rw [hselected]
    simp
  have hTcardEq : T.card = split.selected.toFinset.card := by
    have h := congrArg Finset.card
      (liftedSubset_modPSubset data d hsize split.selected.toFinset)
    simpa [liftedSubsetOfModPSubset] using h
  have hTcard : T.card ≤ S.card := by
    rw [hTcardEq,
      List.toFinset_card_of_nodup hsplitNodup, hselected, List.length_cons,
      hlength]
    have htrueCard :
        S.card = (head :: trueSelected).length := by
      rw [← Finset.card_map (modPIndexToLiftedEmbedding data d hsize),
        ← show liftS = Finset.map
          (modPIndexToLiftedEmbedding data d hsize) S from rfl,
        ← htrueSupport, List.toFinset_card_of_nodup htrue_nodup]
    rw [htrueCard, List.length_cons]
    omega
  have hTeq : T = S :=
    tryDirectSplit_eqSupport_of_card_le state.partition hval facts
      hcore_degree_pos hprecision hgcd hfactor_irr hfactor_dvd' hSsub
      hfactor_rep hrecover hsplitNodup htry hheadS
      (by simpa [T] using hheadT) (by simpa [T] using hTcard)
  obtain ⟨hcandidate, hsplitProduct⟩ := tryDirectSplit_some htry
  have hcandidate_eq : split.candidate = factor := by
    rw [hcandidate, show Hex.liftModulus d = d.p ^ d.k from rfl,
      directCandidate_indexed_eq core d split.selected hsplitNodup]
    have htransport :
        liftedSubsetOfModPSubset data d hsize T = split.selected.toFinset :=
      liftedSubset_modPSubset data d hsize split.selected.toFinset
    rw [← hrecover, ← hTeq]
    simp [directSupportCandidate, d, T, hsize, htransport]
  have hremainingSupport :
      split.remaining.toFinset =
        liftedSubsetOfModPSubset data d hsize (J \ S) := by
    rw [hremaining]
    have hall :
        (head :: selected).toFinset ∪ remaining.toFinset =
          (head :: tail).toFinset := by
      simpa [hunion, Finset.insert_union] using
        congrArg (Finset.insert head) hunion
    have hselectedSupport :
        (head :: selected).toFinset = liftS := by
      calc
        (head :: selected).toFinset = split.selected.toFinset := by
          rw [hselected]
        _ = liftedSubsetOfModPSubset data d hsize T :=
          (liftedSubset_modPSubset data d hsize
            split.selected.toFinset).symm
        _ = liftedSubsetOfModPSubset data d hsize S := by rw [hTeq]
        _ = liftS := rfl
    have hfullDisjoint :
        Disjoint (head :: selected).toFinset remaining.toFinset := by
      rw [Finset.disjoint_left]
      intro i hiSel hiRem
      simp only [List.toFinset_cons, Finset.mem_insert] at hiSel
      rcases hiSel with hiEq | hiSelected
      · have hiTail :=
          (Hex.subsetsOfSizeWithComplement_mem tail level
            (selected, remaining) henum).2 i
            (by simpa using hiRem)
        exact (List.nodup_cons.mp state.localNodup).1 (hiEq ▸ hiTail)
      · exact Finset.disjoint_left.mp hdisjoint hiSelected hiRem
    rw [hselectedSupport] at hall
    have hlocal :
        (head :: tail).toFinset =
          liftedSubsetOfModPSubset data d hsize J :=
      state.localSupport
    rw [hlocal] at hall
    apply Finset.Subset.antisymm
    · intro i hi
      have hiLocal : i ∈
          liftedSubsetOfModPSubset data d hsize J := by
        rw [← hall]
        exact Finset.mem_union_right liftS hi
      have hiNotS : i ∉ liftS := by
        intro hiS
        exact Finset.disjoint_left.mp hfullDisjoint
          (by simpa [hselectedSupport] using hiS) hi
      simp only [liftedSubsetOfModPSubset, Finset.mem_map] at hiLocal ⊢
      obtain ⟨j, hj, rfl⟩ := hiLocal
      refine ⟨j, Finset.mem_sdiff.mpr ⟨hj, ?_⟩, rfl⟩
      intro hjS
      apply hiNotS
      change modPIndexToLiftedEmbedding data d hsize j ∈
        liftedSubsetOfModPSubset data d hsize S
      exact Finset.mem_map.mpr ⟨j, hjS, rfl⟩
    · intro i hi
      simp only [liftedSubsetOfModPSubset, Finset.mem_map,
        Finset.mem_sdiff] at hi
      obtain ⟨j, ⟨hjJ, hjS⟩, rfl⟩ := hi
      have hiLocal :
          modPIndexToLiftedEmbedding data d hsize j ∈
            liftedSubsetOfModPSubset data d hsize J :=
        Finset.mem_map.mpr ⟨j, hjJ, rfl⟩
      rw [← hall] at hiLocal
      rcases Finset.mem_union.mp hiLocal with hiLiftS | hiRemaining
      · exact False.elim (hjS (by
          simpa [liftS, liftedSubsetOfModPSubset] using hiLiftS))
      · exact hiRemaining
  refine ⟨factor, S, hfactor_irr, hfactor_dvd', hSsub, hfactor_rep, hfactor_norm,
    hcandidate_eq, ?_, ?_, ?_, ?_⟩
  · simpa [hcandidate_eq] using hsplitProduct
  · rw [← hTeq]
    exact (liftedSubset_modPSubset data d hsize split.selected.toFinset).symm
  · simpa [d, hsize] using hremainingSupport
  · simpa [hremaining] using hremainingNodup

/-- Semantic contract for a completed direct recursive search. -/
structure DirectFactorListSpec
    (target : Hex.ZPoly) (factors : List Hex.ZPoly) : Prop where
  product : Array.polyProduct factors.toArray = target
  irreducible :
    ∀ factor ∈ factors,
      Irreducible (HexPolyZMathlib.toPolynomial factor)
  normalized :
    ∀ factor ∈ factors, Hex.normalizeFactorSign factor = factor
  degreePos :
    ∀ factor ∈ factors, 0 < factor.degree?.getD 0

/-- Every completed recursive direct search is an irreducible factorization of
its current target.  A resource decline has no mathematical claim. -/
theorem searchDirectAux_factored
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization core data)
    (facts : DirectLiftFacts core B data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hrecovery :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1) :
    ∀ {fuel target localFactors budget stats factors budget' stats'}
      {J : ModPFactorSubset data},
      DirectSearchInvariant core B data J target localFactors →
      Hex.searchDirectAux (Hex.DensePoly.leadingCoeff core)
          (Hex.ZPoly.coreLiftData core B data)
          fuel target localFactors budget stats =
        .factored factors budget' stats' →
      DirectFactorListSpec target factors := by
  intro fuel
  induction fuel with
  | zero =>
      intro target localFactors budget stats factors budget' stats' J
        state hrun
      simp [Hex.searchDirectAux] at hrun
  | succ fuel ih =>
      intro target localFactors budget stats factors budget' stats' J
        state hrun
      simp only [Hex.searchDirectAux] at hrun
      by_cases hone : target = 1
      · rw [if_pos hone] at hrun
        cases hrun
        refine
          { product := by simpa using hone.symm
            irreducible := by simp
            normalized := by simp
            degreePos := by simp }
      · rw [if_neg hone] at hrun
        cases localFactors with
        | nil => simp at hrun
        | cons head tail =>
            simp only at hrun
            generalize hfind :
                Hex.findDirectHead (Hex.DensePoly.leadingCoeff core) target
                    (Hex.ZPoly.coreLiftData core B data) head tail
                    (List.range (tail.length + 1)) budget 0 #[] = headResult
              at hrun
            cases headResult with
            | declined reason remainingBudget candidates completed =>
                simp only at hrun
                contradiction
            | found split remainingBudget candidates completed =>
                simp only at hrun
                let nextStats : Hex.ClassicalStats :=
                  { stats with
                    candidatesTried := stats.candidatesTried + candidates
                    completedLevels := stats.completedLevels ++ completed }
                generalize hnext :
                    Hex.searchDirectAux (Hex.DensePoly.leadingCoeff core)
                        (Hex.ZPoly.coreLiftData core B data) fuel
                        split.quotient split.remaining remainingBudget
                        nextStats = nextResult at hrun
                cases nextResult with
                | declined reason finalBudget finalStats =>
                    simp only at hrun
                    contradiction
                | factored rest finalBudget finalStats =>
                    simp only at hrun
                    cases hrun
                    obtain ⟨factor, S, hfactorIrr, hfactorDvd, hSJ,
                        hfactorRep, hfactorNorm, hcandidate, hproduct,
                        hselectedSupport, hremainingSupport,
                        hremainingNodup⟩ :=
                      findDirectHead_correct hcore_prim hcore_ne hcore_lc_pos
                        hcore_degree_pos hval facts hprecision hrecovery hgcd
                        state hfind
                    have hquotientNe : split.quotient ≠ 0 := by
                      intro hzero
                      apply state.targetNe
                      rw [← hproduct, hzero, Hex.DensePoly.zero_mul]
                    have hquotientDvdTarget : split.quotient ∣ target :=
                      ⟨factor, hproduct.symm⟩
                    have hquotientDvdCore : split.quotient ∣ core :=
                      zpoly_dvd_trans hquotientDvdTarget state.targetDvdCore
                    have hnextState :
                        DirectSearchInvariant core B data (J \ S)
                          split.quotient split.remaining :=
                      { targetNe := hquotientNe
                        targetDvdCore := hquotientDvdCore
                        partition := state.partition.remove hproduct
                          hfactorRep hSJ hfactorIrr hfactorDvd
                        localNodup := hremainingNodup
                        localSupport := hremainingSupport }
                    have hrest :=
                      ih hnextState hnext
                    have hfactorCore : factor ∣ core :=
                      zpoly_dvd_trans hfactorDvd state.targetDvdCore
                    have hfactorDegree : 0 < factor.degree?.getD 0 :=
                      degree_pos_of_irreducible_dvd_primitive
                        hcore_prim hfactorIrr hfactorCore
                    refine
                      { product := ?_
                        irreducible := ?_
                        normalized := ?_
                        degreePos := ?_ }
                    · rw [Hex.ZPoly.polyProduct_cons_toArray, hcandidate,
                        hrest.product]
                      rw [Hex.DensePoly.mul_comm_poly]
                      exact hproduct
                    · intro g hg
                      simp only [List.mem_cons] at hg
                      rcases hg with rfl | hg
                      · simpa [hcandidate] using hfactorIrr
                      · exact hrest.irreducible g hg
                    · intro g hg
                      simp only [List.mem_cons] at hg
                      rcases hg with rfl | hg
                      · simpa [hcandidate] using hfactorNorm
                      · exact hrest.normalized g hg
                    · intro g hg
                      simp only [List.mem_cons] at hg
                      rcases hg with rfl | hg
                      · simpa [hcandidate] using hfactorDegree
                      · exact hrest.degreePos g hg

/-- End-to-end contract for the public direct search over the one full lifted
basis. -/
theorem searchDirect_factored
    {core : Hex.ZPoly} {B : Nat} {data : Hex.PrimeChoiceData}
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (hcore_squarefree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB : B = Hex.ZPoly.defaultFactorCoeffBound core)
    (hval : ModPFactorization core data)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    {budget : Nat} {stats : Hex.ClassicalStats}
    {factors : List Hex.ZPoly} {budget' : Nat}
    {stats' : Hex.ClassicalStats}
    (hrun :
      Hex.searchDirect (Hex.DensePoly.leadingCoeff core) core
          (Hex.ZPoly.coreLiftData core B data) budget stats =
        .factored factors budget' stats') :
    DirectFactorListSpec core factors := by
  let d := Hex.ZPoly.coreLiftData core B data
  let hsize : d.liftedFactors.size = data.factorsModP.size :=
    henselLiftData_liftedFactors_size_eq
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (Hex.precisionForCoeffBound B data.p) data
  have hcore_ne : core ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hrecover :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p := by
    rw [← hB]
    exact Hex.precisionForCoeffBound_spec hval.prime.two_le B
  have hgenuine := directLiftFacts core B data hval
    (Hex.ZPoly.size_pos_of_ne_zero core hcore_ne) hprecision hgcd
  have hinitial :
      DirectSearchInvariant core B data Finset.univ core
        (List.finRange d.liftedFactors.size) := by
    refine
      { targetNe := hcore_ne
        targetDvdCore := Hex.DensePoly.dvd_refl_poly core
        partition := directSupportPartition_initial core B data
          hcore_prim hcore_lc_pos hcore_degree_pos hcore_squarefree hB
          hval hprecision hgcd
        localNodup := List.nodup_finRange _
        localSupport := ?_ }
    rw [List.toFinset_finRange]
    change Finset.univ =
      liftedSubsetOfModPSubset data d hsize Finset.univ
    symm
    apply Finset.eq_univ_of_forall
    intro i
    let j := modPIndexOfLiftedIndex data d hsize i
    have hij : liftedIndexOfModPIndex data d hsize j = i := by
      apply Fin.ext
      rfl
    rw [← hij, liftedIndex_mem_liftedSubset_iff data d hsize]
    exact Finset.mem_univ _
  unfold Hex.searchDirect at hrun
  exact searchDirectAux_factored hcore_prim hcore_ne hcore_lc_pos
    hcore_degree_pos hval hgenuine hprecision hrecover hgcd
    hinitial hrun

/-- The executable validity guard is implied by the proved direct-search
contract. -/
theorem validDirectFactors_of_spec
    {core : Hex.ZPoly} {factors : List Hex.ZPoly}
    (hcore_degree_pos : 0 < core.degree?.getD 0)
    (h : DirectFactorListSpec core factors) :
    Hex.validDirectFactors core factors = true := by
  have hcore_ne_one : core ≠ 1 := by
    intro hone
    rw [hone] at hcore_degree_pos
    change 0 < (Hex.DensePoly.C (1 : Int)).degree?.getD 0 at hcore_degree_pos
    rw [Hex.DensePoly.degree?_C_getD] at hcore_degree_pos
    omega
  have hfactors_ne : factors ≠ [] := by
    intro hempty
    subst factors
    have hproduct := h.product
    rw [Hex.ZPoly.polyProduct_empty] at hproduct
    exact hcore_ne_one hproduct.symm
  have hcontent :
      ∀ factor ∈ factors, Hex.ZPoly.content factor = 1 := by
    intro factor hfactor
    have hdegree := h.degreePos factor hfactor
    have hirr := h.irreducible factor hfactor
    have hprimitive :
        (HexPolyZMathlib.toPolynomial factor).IsPrimitive :=
      hirr.isPrimitive (by
        rw [HexPolyMathlib.natDegree_toPolynomial]
        omega)
    have hpolyContent :
        (HexPolyZMathlib.toPolynomial factor).content = 1 :=
      Polynomial.isPrimitive_iff_content_eq_one.mp hprimitive
    rwa [HexPolyZMathlib.toPolynomial_content] at hpolyContent
  unfold Hex.validDirectFactors
  simp only [decide_eq_true_eq,
    List.all_eq_true, Bool.and_eq_true]
  refine ⟨?_, h.degreePos⟩
  refine ⟨?_, h.normalized⟩
  refine ⟨?_, hcontent⟩
  exact ⟨by simpa using hfactors_ne, h.product⟩

/-- A successful run of the sole classical engine is an irreducible
factorization of its indexed direct-coordinate core. -/
theorem factorDirectCore_factored
    (core : Hex.CoreProblem)
    (hcore_prim : Hex.ZPoly.Primitive core.poly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hcore_degree_pos : 0 < core.poly.degree?.getD 0)
    (hcore_squarefree :
      Squarefree (HexPolyZMathlib.toPolynomial core.poly))
    {budget : Nat} {factors : Array Hex.ZPoly}
    {stats : Hex.ClassicalStats}
    (hrun : Hex.factorDirectCore core budget = .factored factors stats) :
    DirectFactorListSpec core.poly factors.toList := by
  unfold Hex.factorDirectCore at hrun
  generalize hplan : Hex.directPrimePlan? core = plan? at hrun
  cases plan? with
  | none => simp at hrun
  | some modular =>
      have hval :=
        directPrimePlan_modPFactorization core modular hplan
          hcore_prim hcore_lc_pos hcore_degree_pos
      let B := Hex.ZPoly.defaultFactorCoeffBound core.poly
      have hcore_ne : core.poly ≠ 0 :=
        zpoly_ne_zero_of_pos_lc hcore_lc_pos
      have hBpos : 0 < B :=
        Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
      have hprecision :
          1 ≤ Hex.precisionForCoeffBound B modular.data.p := by
        have hrecover :=
          Hex.precisionForCoeffBound_spec hval.prime.two_le B
        by_contra hnot
        have hk : Hex.precisionForCoeffBound B modular.data.p = 0 := by
          omega
        rw [hk, pow_zero] at hrecover
        omega
      letI := modular.data.bounds
      have hadm :
          Hex.leadingCoeffAdmissible core.poly modular.data.p :=
        Hex.isGoodPrime_leadingCoeffAdmissible core.poly modular.data.p
          hval.good
      have hcast :
          ((Hex.DensePoly.leadingCoeff core.poly : Int) :
            ZMod modular.data.p) ≠ 0 := by
        have hpolyCast :=
          (IntReductionMod.intCast_zmod_leadingCoeff_ne_zero_iff_leadingCoeffModP_ne_zero
            (p := modular.data.p) (f := core.poly)).mpr hadm
        simpa [HexPolyMathlib.leadingCoeff_toPolynomial] using hpolyCast
      have hgcd :
          Int.gcd (Hex.DensePoly.leadingCoeff core.poly)
            (Int.ofNat
              (modular.data.p ^
                Hex.precisionForCoeffBound B modular.data.p)) = 1 :=
        gcd_primePow_eq_one_of_cast_ne_zero
          (Hex.DensePoly.leadingCoeff core.poly) modular.data.p
          (Hex.precisionForCoeffBound B modular.data.p)
          (natPrime_of_hexNatPrime hval.prime) hcast
      simp only [Hex.DirectLiftedBasis.data,
        Hex.DirectLiftPlan.coeffBound] at hrun
      generalize hsearch :
          Hex.searchDirect (Hex.DensePoly.leadingCoeff core.poly) core.poly
              (Hex.ZPoly.coreLiftData core.poly B modular.data) budget
              { prime := modular.prime
                primeProbes := modular.probes.size
                liftedFactorCount :=
                  (Hex.ZPoly.coreLiftData core.poly B modular.data).liftedFactors.size
                henselLifts := 1 } = result at hrun
      cases result with
      | declined reason budget' stats' => simp at hrun
      | factored found budget' stats' =>
          simp only at hrun
          have hspec :=
            searchDirect_factored hcore_prim hcore_lc_pos hcore_degree_pos
              hcore_squarefree (B := B) rfl hval hprecision hgcd hsearch
          have hvalid :=
            validDirectFactors_of_spec hcore_degree_pos hspec
          rw [hvalid] at hrun
          cases hrun
          simpa using hspec

end HexBerlekampZassenhausMathlib
