/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Reduction

public section

namespace Hex.SignDet

variable {E : Type u} [Zero E] [DecidableEq E]

/-- Indexed reductions of the original queries, shared by all moment rows.
The list retains duplicate queries as separate positions. -/
structure QueryReduction (E : Type u) [Zero E] [DecidableEq E] where
  steps : List (ReductionStep E)

instance : DecidableEq (QueryReduction E) := fun a b =>
  decidable_of_iff (a.steps = b.steps) (by cases a; cases b; simp only [QueryReduction.mk.injEq])

/-- Reduced query operands in their original order. -/
@[expose] def QueryReduction.queries (r : QueryReduction E) : List (DensePoly E) :=
  r.steps.map (·.next)

/-- Rebind a contiguous sublist to local query positions. Only indices change;
the polynomial witnesses are reused without another division. -/
@[expose] def QueryReduction.slice (r : QueryReduction E) (start count : Nat) : QueryReduction E :=
  ⟨((r.steps.drop start).take count).zipIdx.map fun (s, i) => {s with index := i}⟩

/-- Original or preprocessed factors, according to the supplied evidence. -/
@[expose] def QueryReduction.operands (qs : List (DensePoly E))
    (r : Option (QueryReduction E)) : List (DensePoly E) :=
  match r with
  | none => qs
  | some r => r.queries

variable [One E] [Add E] [Sub E] [Mul E]

/-- Replay every original query once, including its exact positional index.
Length mismatches and reordered witnesses are rejected. -/
@[expose] def QueryReduction.checkFrom (sign : E → Int) (p : DensePoly E) :
    Nat → List (DensePoly E) → List (ReductionStep E) → Bool
  | _, [], [] => true
  | i, q :: qs, s :: ss => s.check sign p 1 q i && checkFrom sign p (i + 1) qs ss
  | _, _, _ => false

/-- Query reduction is used only for positive-degree heads. -/
@[expose] def QueryReduction.check (sign : E → Int) (p : DensePoly E)
    (qs : List (DensePoly E)) (r : QueryReduction E) : Bool :=
  decide (0 < p.natDegree) && checkFrom sign p 0 qs r.steps

theorem QueryReduction.checkFrom_bounds {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {ss : List (ReductionStep E)} {i : Nat}
    (h : checkFrom sign p i qs ss = true) :
    ss.length = qs.length ∧ ∀ s ∈ ss, s.next.isZero = true ∨ s.next.natDegree < p.natDegree := by
  induction qs generalizing ss i with
  | nil => cases ss <;> simp_all [checkFrom]
  | cons q qs ih =>
    cases ss with
    | nil => simp [checkFrom] at h
    | cons s ss =>
      simp only [checkFrom, Bool.and_eq_true] at h
      obtain ⟨hlen, hbounds⟩ := ih h.2
      refine ⟨by simp only [List.length_cons, hlen], ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact (ReductionStep.check_eq h.1).2.2.2.1
      · exact hbounds t ht

/-- All shared operands retain their original positions and have the degree
bound required by reduced moment multiplication. Zero factors are explicit. -/
theorem QueryReduction.check_bounds {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {r : QueryReduction E} (h : r.check sign p qs = true) :
    r.queries.length = qs.length ∧
      ∀ q ∈ r.queries, q.isZero = true ∨ q.natDegree < p.natDegree := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨hlen, hbounds⟩ := checkFrom_bounds h.2
  refine ⟨by simpa only [queries, List.length_map] using hlen, ?_⟩
  intro q hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  exact hbounds s hs

theorem QueryReduction.checkFrom_take {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {ss : List (ReductionStep E)} {i : Nat}
    (h : checkFrom sign p i qs ss = true) (k : Nat) :
    checkFrom sign p i (qs.take k) (ss.take k) = true := by
  induction k generalizing qs ss i with
  | zero => rfl
  | succ k ih =>
    cases qs <;> cases ss <;> simp_all only [checkFrom, Bool.and_eq_true,
      List.take_nil, List.take_succ_cons, Bool.false_eq_true, and_self]

theorem QueryReduction.checkFrom_drop {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {ss : List (ReductionStep E)} {i : Nat}
    (h : checkFrom sign p i qs ss = true) (k : Nat) :
    checkFrom sign p (i + k) (qs.drop k) (ss.drop k) = true := by
  induction k generalizing qs ss i with
  | zero => simpa using h
  | succ k ih =>
    cases qs with
    | nil => cases ss <;> simp_all [checkFrom]
    | cons q qs =>
      cases ss with
      | nil => simp [checkFrom] at h
      | cons s ss =>
        simp only [checkFrom, Bool.and_eq_true] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih h.2

theorem QueryReduction.checkFrom_reindex {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {ss : List (ReductionStep E)} {i : Nat}
    (h : checkFrom sign p i qs ss = true) (j : Nat) :
    checkFrom sign p j qs (ss.zipIdx j |>.map fun (s, k) => {s with index := k}) = true := by
  induction qs generalizing ss i j with
  | nil => cases ss <;> simp_all [checkFrom]
  | cons q qs ih =>
    cases ss with
    | nil => simp [checkFrom] at h
    | cons s ss =>
      simp only [checkFrom, Bool.and_eq_true] at h
      simp only [List.zipIdx_cons, List.map_cons, checkFrom, Bool.and_eq_true]
      refine ⟨?_, ih h.2 (j + 1)⟩
      simpa only [ReductionStep.check, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, true_and, and_assoc] using (ReductionStep.check_eq h.1).2

/-- Restricting accepted preprocessing to a contiguous child list preserves
acceptance after rebinding its positions. No division is rerun. -/
theorem QueryReduction.slice_checks {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {r : QueryReduction E}
    (h : r.check sign p qs = true) (start count : Nat) :
    (r.slice start count).check sign p ((qs.drop start).take count) = true := by
  simp only [check, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, checkFrom_reindex (checkFrom_take (checkFrom_drop h.2 start) count) 0⟩

variable [Neg E] [Inv E]

/-- Preprocess each query once with the shared positive pseudo-division
producer. Subsequent moment reductions use only these reduced operands. -/
@[expose] def QueryReduction.buildFrom (sign : E → Int) (p : DensePoly E) :
    Nat → List (DensePoly E) → List (ReductionStep E)
  | _, [] => []
  | i, q :: qs => ReductionStep.build sign p 1 q i :: buildFrom sign p (i + 1) qs

@[expose] def QueryReduction.build (sign : E → Int) (p : DensePoly E)
    (qs : List (DensePoly E)) : QueryReduction E :=
  ⟨buildFrom sign p 0 qs⟩

end Hex.SignDet
