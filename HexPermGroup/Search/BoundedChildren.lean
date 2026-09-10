/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Probe
public import HexPermGroup.Search.Accumulator

public section

namespace Hex.PermGroup.Search.Bounded

variable {G : Group n} {P : Predicate n} {budget : Budget}

inductive Status (C : Constraint G P) (t : Node G) (a : Accumulator G P) (budget : Budget) where
  | complete (certificate : Certificate C.Reason) (checked : checkTree C a.group t certificate = true)
      (meter : Meter budget)
  | incomplete (failure : Exhausted budget)

/-- Even on exhaustion the accumulated subgroup remains checked, satisfies
the predicate, and contains every generator found before the stopping point. -/
structure Result (C : Constraint G P) (t : Node G) (a : Accumulator G P) (budget : Budget) where
  acc : Accumulator G P
  grows : a.group.IsSubgroup acc.group
  status : Status C t acc budget

@[expose] def Result.stop (C : Constraint G P) (t : Node G) (a : Accumulator G P)
    (failure : Exhausted budget) : Result C t a budget :=
  ⟨a, fun _ hp => hp, .incomplete failure⟩

/-- Reserve a certificate node before constructing it. Failure preserves the
current subgroup, including any successful leaf just inserted into it. -/
@[expose] def Result.finish (C : Constraint G P) (t : Node G) (a b : Accumulator G P)
    (grows : a.group.IsSubgroup b.group) (certificate : Unit → Certificate C.Reason)
    (checked : checkTree C b.group t (certificate ()) = true) (m : Meter budget) : Result C t a budget :=
  match m.spend .certificates 1 with
  | .error failure => ⟨b, grows, .incomplete failure⟩
  | .ok meter => ⟨b, grows, .complete (certificate ()) checked meter⟩

inductive ChildrenStatus (C : Constraint G P) {size : Nat} (nodes : Fin size → Node G)
    (k : Nat) (hk : k ≤ size) (a : Accumulator G P) (budget : Budget) where
  | complete (certificates : Vector (Certificate C.Reason) k)
      (checked : ∀ i : Fin k,
        checkTree C a.group (nodes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) certificates[i.val] = true)
      (meter : Meter budget)
  | incomplete (failure : Exhausted budget)

structure Children (C : Constraint G P) {size : Nat} (nodes : Fin size → Node G)
    (a : Accumulator G P) (k : Nat) (hk : k ≤ size) (budget : Budget) where
  acc : Accumulator G P
  grows : a.group.IsSubgroup acc.group
  status : ChildrenStatus C nodes k hk acc budget

/-- Process children in orbit order. An incomplete child stops the loop and
retains its lower bound; completed earlier certificates are transported along
each enlargement of the accumulator. -/
@[expose] def collect (C : Constraint G P) {size : Nat} (nodes : Fin size → Node G)
    (visit : ∀ a : Accumulator G P, Meter budget → ∀ i : Fin size, Result C (nodes i) a budget)
    (a : Accumulator G P) (m : Meter budget) (k : Nat) (hk : k ≤ size) : Children C nodes a k hk budget :=
  match k with
  | 0 => ⟨a, fun _ hp => hp, .complete #v[] (fun i => Fin.elim0 i) m⟩
  | k + 1 =>
    let previous := collect C nodes visit a m k (Nat.le_trans (Nat.le_succ k) hk)
    match previous.status with
    | .incomplete failure => ⟨previous.acc, previous.grows, .incomplete failure⟩
    | .complete certificates checked meter =>
      let next := visit previous.acc meter ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      { acc := next.acc
        grows := fun p hp => next.grows p (previous.grows p hp)
        status := match next.status with
          | .incomplete failure => .incomplete failure
          | .complete certificate hc meter =>
            .complete (certificates.push certificate) (by
              intro i
              by_cases hi : i.val < k
              · rw [Vector.getElem_push_lt hi]
                exact checkTree_mono C _ _ next.grows (checked ⟨i.val, hi⟩)
              · have he : i.val = k := by omega
                simp only [he, Vector.getElem_push_eq]
                exact hc) meter }

end Hex.PermGroup.Search.Bounded
