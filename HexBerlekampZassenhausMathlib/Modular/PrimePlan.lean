/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Modular.PrimePlan
public import HexBerlekampZassenhausMathlib.ModPFactorization
public import HexBerlekampZassenhausMathlib.ModPPartition
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.ModPPartition
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent

public section
set_option backward.proofsInPublic true

/-!
# Correctness of the direct prime plan

Two things are proved here beyond the selected trial's semantic bundle.

The subset-degree bitset a probe records is given its meaning: index `i` is
true exactly when some sub-multiset of the recorded modular factor degrees
sums to `i`.  The planner scores primes with these Booleans, and anything that
*rejects* on them needs the specification, not the fold.

The retained trials -- the selected one and every other successful trial the
planner kept -- then get the same modular facts as the selected one, and from
those follows the statement a degree filter would consume: reduction at a
retained good prime preserves the degree of an integer divisor of the input
and factors it as a subproduct of that prime's modular irreducibles, so the
divisor's degree is marked reachable at *every* retained probe.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-! ## The subset-degree bitset -/

/-- One `directDegreeBitsStep` entry, at any index the step records. -/
private theorem directDegreeBitsStep_getElem?
    (maxDegree : Nat) (reachable : Array Bool) (degree i : Nat)
    (hi : i ≤ maxDegree) :
    (Hex.directDegreeBitsStep maxDegree reachable degree)[i]?.getD false =
      (reachable[i]?.getD false ||
        (decide (degree ≤ i) && reachable[i - degree]?.getD false)) := by
  have hlt : i < (List.range (maxDegree + 1)).length := by simp; omega
  simp only [Hex.directDegreeBitsStep, Array.getElem?_map, List.getElem?_toArray]
  rw [List.getElem?_eq_getElem hlt]
  simp

/-- A sub-multiset of `degree ::ₘ pre` either avoids the new degree entirely or
uses it once and leaves a sub-multiset of `pre` summing to the remainder. -/
private theorem exists_le_cons_iff (pre : List Nat) (degree i : Nat) :
    (∃ S ≤ (degree ::ₘ (pre : Multiset Nat)), S.sum = i) ↔
      ((∃ S ≤ (pre : Multiset Nat), S.sum = i) ∨
        (degree ≤ i ∧ ∃ S ≤ (pre : Multiset Nat), S.sum = i - degree)) := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    by_cases hmem : degree ∈ S
    · refine Or.inr ⟨?_, S.erase degree, ?_, ?_⟩
      · exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) degree hmem
      · have herase : S.erase degree ≤ (degree ::ₘ (pre : Multiset Nat)).erase degree :=
          Multiset.erase_le_erase degree hS
        rwa [Multiset.erase_cons_head] at herase
      · have hcons : (degree ::ₘ S.erase degree).sum = S.sum := by
          rw [Multiset.cons_erase hmem]
        rw [Multiset.sum_cons] at hcons
        omega
    · exact Or.inl ⟨S, (Multiset.le_cons_of_notMem hmem).mp hS, rfl⟩
  · rintro (⟨S, hS, rfl⟩ | ⟨hle, S, hS, hsum⟩)
    · exact ⟨S, hS.trans (Multiset.le_cons_self _ _), rfl⟩
    · refine ⟨degree ::ₘ S, Multiset.cons_le_cons _ hS, ?_⟩
      rw [Multiset.sum_cons, hsum]
      omega

/-- The fold invariant: an array recording the sub-multiset sums of a processed
prefix records the sums of that prefix extended by the whole remaining list. -/
private theorem foldl_directDegreeBitsStep_spec (maxDegree : Nat) :
    ∀ (degrees : List Nat) (reachable : Array Bool) (pre : List Nat),
      (∀ i ≤ maxDegree,
        (reachable[i]?.getD false = true ↔
          ∃ S ≤ (pre : Multiset Nat), S.sum = i)) →
      ∀ i ≤ maxDegree,
        ((degrees.foldl (Hex.directDegreeBitsStep maxDegree) reachable)[i]?.getD
            false = true ↔
          ∃ S ≤ ((pre ++ degrees : List Nat) : Multiset Nat), S.sum = i) := by
  intro degrees
  induction degrees with
  | nil => intro reachable pre hpre i hi; simpa using hpre i hi
  | cons degree degrees ih =>
      intro reachable pre hpre i hi
      have hstep : ∀ j ≤ maxDegree,
          ((Hex.directDegreeBitsStep maxDegree reachable degree)[j]?.getD false =
              true ↔
            ∃ S ≤ ((pre ++ [degree] : List Nat) : Multiset Nat), S.sum = j) := by
        intro j hj
        rw [directDegreeBitsStep_getElem? maxDegree reachable degree j hj]
        have hcoe : ((pre ++ [degree] : List Nat) : Multiset Nat) =
            degree ::ₘ (pre : Multiset Nat) := by
          simp [← Multiset.coe_add, Multiset.cons_coe]
          exact Multiset.add_comm _ _
        rw [hcoe, exists_le_cons_iff]
        rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact or_congr (hpre j hj)
          (and_congr_right fun _ => hpre (j - degree) (by omega))
      have := ih (Hex.directDegreeBitsStep maxDegree reachable degree)
        (pre ++ [degree]) hstep i hi
      simpa using this

/-- The initial bitset records exactly the empty sub-multiset. -/
private theorem directDegreeBits_init_spec (maxDegree : Nat) :
    ∀ i ≤ maxDegree,
      (((#[true] ++ Array.replicate maxDegree false) : Array Bool)[i]?.getD
          false = true ↔
        ∃ S ≤ (([] : List Nat) : Multiset Nat), S.sum = i) := by
  intro i hi
  have hnil : (∃ S ≤ (([] : List Nat) : Multiset Nat), S.sum = i) ↔ i = 0 := by
    constructor
    · rintro ⟨S, hS, rfl⟩
      simpa using congrArg Multiset.sum (Multiset.le_zero.mp (by simpa using hS))
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  rw [hnil]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · have hfalse :
        ((#[true] ++ Array.replicate maxDegree false : Array Bool))[i]?.getD
          false = false := by
      rcases Nat.lt_or_ge i (maxDegree + 1) with hlt | hge
      · rw [Array.getElem?_eq_getElem (by simp; omega)]
        simp [Array.getElem_append, Nat.not_lt.mpr hpos]
      · rw [Array.getElem?_eq_none (by simp; omega)]
        rfl
    simp [hfalse]
    omega

/-- `Hex.directDegreeBits` means what its name says: index `i` is true exactly
when some sub-multiset of the recorded degrees sums to `i`.

The bound `i ≤ maxDegree` is the array's own range; outside it the fold records
nothing, and no degree of a divisor of a degree-`maxDegree` polynomial lands
there. -/
theorem directDegreeBits_getElem?_iff
    (maxDegree : Nat) (degrees : Array Nat) (i : Nat) (hi : i ≤ maxDegree) :
    (Hex.directDegreeBits maxDegree degrees)[i]?.getD false = true ↔
      ∃ S ≤ (degrees.toList : Multiset Nat), S.sum = i := by
  have := foldl_directDegreeBitsStep_spec maxDegree degrees.toList
    (#[true] ++ Array.replicate maxDegree false) []
    (directDegreeBits_init_spec maxDegree) i hi
  simpa [Hex.directDegreeBits, Array.foldl_toList] using this

/-! ## The retained trials -/

/-- The complete proof-facing contract of a direct prime probe.  Consumers
need the semantic factorization, the cached Berlekamp form for the singleton
certificate, and the small-prime bound used by the CLD resultant estimate. -/
structure DirectPrimeFacts
    (core : Hex.ZPoly) (data : Hex.PrimeChoiceData) : Prop where
  /-- The cached modular factorization is mathematically valid. -/
  factorization : ModPFactorization core data
  /-- The cached factors have the required Berlekamp certificate form. -/
  berlekampForm : Hex.factorsModPBerlekampForm core data
  /-- The prime lies within the range used by the resultant estimate. -/
  p_le : data.p ≤ 500

/-- Every retained trial -- not only the selected one -- describes the
normalized modular image of the plan's own indexed polynomial. -/
theorem directPrimePlan_probes_modPFactorization
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ∀ probe ∈ plan.probes, ModPFactorization core.poly probe.data := by
  intro probe hmem
  exact modPFactorization_of_probePrimeData
    (Hex.directPrimePlan?_probes_trial core plan hplan probe hmem).1
    hprim hlc_pos hpos

/-- Every retained trial supplies exactly the modular facts the classical and
lattice proof cones consume. -/
theorem directPrimePlan_probes_facts
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ∀ probe ∈ plan.probes, DirectPrimeFacts core.poly probe.data := by
  intro probe hmem
  exact
    { factorization :=
        directPrimePlan_probes_modPFactorization core plan hplan hprim hlc_pos
          hpos probe hmem
      berlekampForm :=
        Hex.probePrimeData?_form core.poly probe.candidate probe.data
          (Hex.directPrimePlan?_probes_trial core plan hplan probe hmem).1
      p_le := Hex.directPrimePlan?_probes_p_le_500 core plan hplan probe hmem }

/-- A selected direct plan describes the normalized modular image of its own
indexed polynomial. -/
theorem directPrimePlan_modPFactorization
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ModPFactorization core.poly plan.data :=
  directPrimePlan_probes_modPFactorization core plan hplan hprim hlc_pos hpos
    plan.selected plan.selected_mem_probes

/-- A successful direct plan supplies exactly the modular facts used by the
classical and lattice proof cones. -/
theorem directPrimePlan_facts
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    DirectPrimeFacts core.poly plan.data :=
  directPrimePlan_probes_facts core plan hplan hprim hlc_pos hpos
    plan.selected plan.selected_mem_probes

end HexBerlekampZassenhausMathlib
