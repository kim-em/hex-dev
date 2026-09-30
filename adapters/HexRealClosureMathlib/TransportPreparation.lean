/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportClosedReduction
public import HexSignDet.QueryReduction

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- Interpret each query reduction without changing its positional index. -/
@[expose] def preparation (read : E → K) (r : Hex.SignDet.QueryReduction E) :
    Hex.SignDet.QueryReduction K := ⟨r.steps.map (reductionStep read)⟩

/-- Shared reduced operands retain their order, including duplicate queries. -/
theorem preparation_queries (read : E → K) (r : Hex.SignDet.QueryReduction E) :
    (preparation read r).queries = r.queries.map (polynomial read) := by
  simp only [preparation, Hex.SignDet.QueryReduction.queries, List.map_map]
  rfl

/-- The chosen query operands interpret both direct and preprocessed evidence. -/
theorem preparation_operands (read : E → K) (qs : List (Hex.DensePoly E))
    (r : Option (Hex.SignDet.QueryReduction E)) :
    Hex.SignDet.QueryReduction.operands (qs.map (polynomial read)) (r.map (preparation read)) =
      (Hex.SignDet.QueryReduction.operands qs r).map (polynomial read) := by
  cases r with
  | none => rfl
  | some r => exact preparation_queries read r

variable [One E] [Add E] [Sub E] [Mul E]

/-- Arithmetic and scale signs for the exact paired query witnesses.
Length mismatches are rejected by the native checker, independently of this data. -/
@[expose] def PreparationData (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (p : Hex.DensePoly E) : List (Hex.DensePoly E) → List (Hex.SignDet.ReductionStep E) → Prop
  | [], [] => True
  | q :: qs, s :: ss => ReductionStepData read sourceSign targetSign p 1 q s ∧
      PreparationData read sourceSign targetSign p qs ss
  | _, _ => True

/-- Replay all literal query witnesses at their original positions. -/
theorem preparation_from_check (read : E → K) (zero : read 0 = 0) (one : read 1 = 1)
    (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E)
    (qs : List (Hex.DensePoly E)) (ss : List (Hex.SignDet.ReductionStep E)) (i : Nat)
    (data : PreparationData read sourceSign targetSign p qs ss)
    (accepted : Hex.SignDet.QueryReduction.checkFrom sourceSign p i qs ss = true) :
    Hex.SignDet.QueryReduction.checkFrom targetSign (polynomial read p) i
      (qs.map (polynomial read)) (ss.map (reductionStep read)) = true := by
  induction qs generalizing ss i with
  | nil => cases ss <;> simp_all only [Hex.SignDet.QueryReduction.checkFrom, List.map_nil, Bool.false_eq_true]
  | cons q qs ih =>
    cases ss with
    | nil => simp only [Hex.SignDet.QueryReduction.checkFrom, Bool.false_eq_true] at accepted
    | cons s ss =>
      simp only [Hex.SignDet.QueryReduction.checkFrom, Bool.and_eq_true] at accepted
      simp only [List.map_cons, Hex.SignDet.QueryReduction.checkFrom, Bool.and_eq_true]
      have first := reduction_step_check read zero sourceSign targetSign p 1 q i s data.1 accepted.1
      rw [polynomial_one read zero one] at first
      exact ⟨first, ih ss (i + 1) data.2 accepted.2⟩

/-- The complete native preprocessing check transports without another division. -/
theorem preparation_check (read : E → K) (zero : read 0 = 0) (one : read 1 = 1)
    (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E)
    (qs : List (Hex.DensePoly E)) (r : Hex.SignDet.QueryReduction E)
    (head : Leading read p) (data : PreparationData read sourceSign targetSign p qs r.steps)
    (accepted : r.check sourceSign p qs = true) :
    (preparation read r).check targetSign (polynomial read p) (qs.map (polynomial read)) = true := by
  simp only [Hex.SignDet.QueryReduction.check, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  exact ⟨by simpa only [polynomial_degree read zero p head] using accepted.1,
    preparation_from_check read zero one sourceSign targetSign p qs r.steps 0 data accepted.2⟩

omit [DecidableEq K] in
/-- Closure derives each preprocessing step from membership of its literal
query, next representative, quotient and scales. -/
theorem PreparationData.of_closed [NatCast E] (read : E → K) (S : E → Prop)
    (data : Closed read S) (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E)
    (qs : List (Hex.DensePoly E)) (ss : List (Hex.SignDet.ReductionStep E))
    (head : Leading read p) (hp : ∀ i < p.size, S (p.coeff i))
    (hq : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i))
    (domain : ∀ s ∈ ss, ReductionDomain S s)
    (signs : ∀ s ∈ ss, ReductionSigns read sourceSign targetSign s) :
    PreparationData read sourceSign targetSign p qs ss := by
  induction qs generalizing ss with
  | nil => cases ss <;> exact trivial
  | cons q qs ih =>
    cases ss with
    | nil => exact trivial
    | cons s ss =>
      have member : s ∈ s :: ss := by simp
      have stored := domain s member
      have scaleSigns := signs s member
      refine ⟨⟨head, ?_, scaleSigns.left, scaleSigns.right⟩, ?_⟩
      · exact ProductIdentity.of_closed read S data p 1 q s.next _ _ _ hp
          (fun i _ => data.coeff_one read S i) (hq q (by simp))
          stored.next stored.left stored.quotient stored.right
      · exact ih ss (fun q member => hq q (List.mem_cons_of_mem _ member))
          (fun step member => domain step (List.mem_cons_of_mem _ member))
          (fun step member => signs step (List.mem_cons_of_mem _ member))

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.preparation_queries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.preparation_queries
/-- info: 'Hex.RealClosure.Transport.preparation_operands' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.preparation_operands
/-- info: 'Hex.RealClosure.Transport.preparation_from_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.preparation_from_check
/-- info: 'Hex.RealClosure.Transport.preparation_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.preparation_check

/-- info: 'Hex.RealClosure.Transport.PreparationData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.PreparationData.of_closed
