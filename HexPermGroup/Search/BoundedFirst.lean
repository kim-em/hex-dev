/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Probe
public import HexPermGroup.Search.Witness

public section

namespace Hex.PermGroup.Search

namespace BoundedFirst

variable {G : Group n} {test : Perm n → Bool} {budget : Budget}

inductive Decision (C : Pruner G test) (t : Node G) (budget : Budget) where
  | found (p : Element G) (inside : t.Contains p.val) (satisfies : test p.val = true) (meter : Meter budget)
  | absent (certificate : Certificate C.Reason) (checked : checkFailure C t certificate = true) (meter : Meter budget)
  | incomplete (failure : Exhausted budget)

@[expose] def finish (C : Pruner G test) (t : Node G) (certificate : Unit → Certificate C.Reason)
    (checked : checkFailure C t (certificate ()) = true) (m : Meter budget) : Decision C t budget :=
  match m.spend .certificates 1 with
  | .error failure => .incomplete failure
  | .ok meter => .absent (certificate ()) checked meter

inductive Children (C : Pruner G test) {size : Nat} (nodes : Fin size → Node G)
    (k : Nat) (hk : k ≤ size) (budget : Budget) where
  | found (i : Fin k) (p : Element G)
      (inside : (nodes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).Contains p.val)
      (satisfies : test p.val = true) (meter : Meter budget)
  | absent (certificates : Vector (Certificate C.Reason) k)
      (checked : ∀ i : Fin k,
        checkFailure C (nodes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) certificates[i.val] = true)
      (meter : Meter budget)
  | incomplete (failure : Exhausted budget)

@[expose] def collect (C : Pruner G test) {size : Nat} (nodes : Fin size → Node G)
    (visit : Meter budget → ∀ i : Fin size, Decision C (nodes i) budget)
    (m : Meter budget) (k : Nat) (hk : k ≤ size) : Children C nodes k hk budget :=
  match k with
  | 0 => .absent #v[] (fun i => Fin.elim0 i) m
  | k + 1 =>
    match collect C nodes visit m k (Nat.le_trans (Nat.le_succ k) hk) with
    | .incomplete failure => .incomplete failure
    | .found i p hp ht meter => .found ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩ p hp ht meter
    | .absent certificates checked meter =>
      match visit meter ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ with
      | .incomplete failure => .incomplete failure
      | .found p hp ht meter => .found ⟨k, Nat.lt_succ_self _⟩ p hp ht meter
      | .absent certificate hc meter =>
        .absent (certificates.push certificate) (by
          intro i
          by_cases hi : i.val < k
          · rw [Vector.getElem_push_lt hi]
            exact checked ⟨i.val, hi⟩
          · have he : i.val = k := by omega
            simp only [he, Vector.getElem_push_eq]
            exact hc) meter

/-- Exhaustion propagates immediately without becoming a negative answer.
Successful leaves stop child traversal before constructing a witness program. -/
@[expose] def visit (C : Pruner G test) (Q : Evaluator test budget) (t : Node G) (m : Meter budget) :
    Decision C t budget :=
  match m.spend .nodes 1 with
  | .error failure => .incomplete failure
  | .ok meter =>
    match C.refineWith t meter with
    | .exhausted failure => .incomplete failure
    | .ok (some reason) meter =>
      finish C t (fun _ => .rejected reason.val) (by simpa only [checkFailure] using reason.property) meter
    | .ok none meter =>
      match hs : t.suffix with
      | .leaf S words =>
        match meter.spend .refinements 1 with
        | .error failure => .incomplete failure
        | .ok meter =>
          match Q t.rep.val meter with
          | .exhausted failure => .incomplete failure
          | .ok value meter =>
            if hp : value.val = true then
              .found t.rep t.contains_rep (value.property.symm.trans hp) meter
            else finish C t (fun _ => .leaf) (by
              have ht := value.property.symm.trans (Bool.eq_false_iff.mpr hp)
              simp only [checkFailure, hs, ht, Bool.not_false]) meter
      | .cons level tail =>
        match collect C (t.child hs) (fun m i => visit C Q (t.child hs i) m)
            meter level.orbit.points.size (Nat.le_refl _) with
        | .incomplete failure => .incomplete failure
        | .found i p hp ht meter => .found p ((t.contains_children hs p.val).mpr ⟨i, hp⟩) ht meter
        | .absent certificates checked meter =>
          finish C t (fun _ => .branch certificates.toArray) (by
            rw [checkFailure_branch C t hs]
            simp only [Vector.size_toArray]
            exact decide_eq_true checked) meter
termination_by t.suffix.length
decreasing_by
  all_goals
    change tail.length < t.suffix.length
    rw [hs]
    exact Nat.lt_succ_self _

end BoundedFirst

/-- Incomplete existence search exposes no negative answer. A complete answer
retains either its checked witness or its full nonexistence certificate. -/
inductive AnswerOutcome {G : Group n} {test : Perm n → Bool} (C : Pruner G test) (budget : Budget) where
  | complete (answer : Answer C) (meter : Meter budget)
  | incomplete (failure : Exhausted budget)

@[expose] def firstWith (budget : Budget) {G : Group n} {test : Perm n → Bool} (C : Pruner G test)
    (Q : Evaluator test budget) : AnswerOutcome C budget :=
  match BoundedFirst.visit C Q (Node.root G) (_root_.Hex.PermGroup.Execution.Meter.empty budget) with
  | .incomplete failure => .incomplete failure
  | .absent certificate checked meter => .complete (.absent certificate checked) meter
  | .found p _ hp meter =>
    match Witness.ofElementWith p hp meter with
    | .exhausted failure => .incomplete failure
    | .ok witness meter => .complete (.found witness) meter

end Hex.PermGroup.Search
