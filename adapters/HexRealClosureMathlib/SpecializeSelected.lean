/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeSample
public import HexSignDet.SelectedSigns

public section

namespace Hex.RealClosure.Specialize
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

variable {F : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]
variable {Ctx : Type u} [DecidableEq Ctx] {context : Ctx}

/-- Checked selected-sign evidence realizes all requested signs at the unique
root with the descriptor's specialized query prefix. Uniqueness excludes every
other root with that prefix, even if its remaining signs would differ. -/
theorem selected_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (d : Descriptor (Hex.RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context)
    (qs : List (Hex.DensePoly (Hex.RationalFn F))) (s : SelectedSigns d qs) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∃ x,
      x ∈ Tarski.rootsIn
        (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding d.raw.head t))
        ((d.raw.lower.specialize embedding t).map (fun x : ℝ => x))
        ((d.raw.upper.specialize embedding t).map (fun x : ℝ => x)) ∧
      signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
        (d.raw.queries.map (fun q => polynomial embedding q t)) x = d.raw.signs ∧
      signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
        (qs.map (fun q => polynomial embedding q t)) x = s.values.toList ∧
      ∀ y, y ∈ Tarski.rootsIn
        (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding d.raw.head t))
        ((d.raw.lower.specialize embedding t).map (fun x : ℝ => x))
        ((d.raw.upper.specialize embedding t).map (fun x : ℝ => x)) →
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (d.raw.queries.map (fun q => polynomial embedding q t)) y = d.raw.signs → y = x := by
  classical
  obtain ⟨accepted, rows⟩ := s.check_eq
  have row : (d.raw.signs ++ s.values.toList, 1) ∈ (s.evidence.table accepted).rows.toList := by
    have member := List.mem_singleton_self (d.raw.signs ++ s.values.toList, (1 : Nat))
    rw [← rows] at member
    exact (List.mem_filter.mp member).1
  have one := SignTable.count_mem (s.evidence.table accepted) row
  obtain ⟨η₁, positive₁, counts⟩ := counts_near embedding ordered context d.raw.head
    d.raw.lower d.raw.upper (d.raw.queries ++ qs) s.evidence accepted
  obtain ⟨η₂, positive₂, realize⟩ := realizeReplay embedding ordered context d.raw.head
    d.raw.lower d.raw.upper (d.raw.queries ++ qs) s.evidence accepted
    (d.raw.signs ++ s.values.toList) one
  refine ⟨min η₁ η₂, lt_min positive₁ positive₂, fun t ht small => ?_⟩
  have small₁ := lt_of_lt_of_le small (min_le_left _ _)
  have small₂ := lt_of_lt_of_le small (min_le_right _ _)
  obtain ⟨x, hx, unique⟩ := realize t ht small₂
  have length := d.raw.wellFormed_length (RawDescriptor.check_eq d.accepted).1
  have first_signs := congrArg (List.take d.raw.queries.length) hx.2
  have suffix := congrArg (List.drop d.raw.queries.length) hx.2
  have left_take : (d.raw.signs ++ s.values.toList).take d.raw.queries.length = d.raw.signs := by
    rw [← length]
    simp
  have left_drop : (d.raw.signs ++ s.values.toList).drop d.raw.queries.length = s.values.toList := by
    rw [← length]
    simp
  rw [left_take] at first_signs
  rw [left_drop] at suffix
  refine ⟨x, hx.1, ?_, ?_, fun y hy hp => ?_⟩
  · simpa [signsAt] using first_signs
  · simpa [signsAt] using suffix
  · let condition := signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
      ((d.raw.queries ++ qs).map (fun q => polynomial embedding q t)) y
    have cardinal := counts t ht small₁ condition
    have positive : 0 < (s.evidence.table accepted).count condition := by
      rw [← cardinal]
      apply Finset.card_pos.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
    obtain ⟨n, member⟩ := (s.evidence.table accepted).mem_of_count_pos positive
    have taken : condition.take d.raw.queries.length = d.raw.signs := by
      simpa [condition, signsAt] using hp
    have filtered : (condition, n) ∈ (s.evidence.table accepted).rows.toList.filter
        (fun row => decide (row.1.take d.raw.queries.length = d.raw.signs)) :=
      List.mem_filter.mpr ⟨member, by simp [taken]⟩
    rw [rows] at filtered
    have equal : condition = d.raw.signs ++ s.values.toList :=
      congrArg Prod.fst (List.mem_singleton.mp filtered)
    exact unique y ⟨hy, equal⟩

/-- info: 'Hex.RealClosure.Specialize.selected_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.selected_near

end Hex.RealClosure.Specialize
