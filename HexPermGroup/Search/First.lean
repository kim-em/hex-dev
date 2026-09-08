/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Failure

public section

namespace Hex.PermGroup.Search

variable {G : Group n} {test : Perm n → Bool}

/-- A node either supplies a satisfying completion or a checked account of
why every completion fails. There is no exhausted-search constructor. -/
inductive Decision (C : Pruner G test) (t : Node G) where
  | found (p : Element G) (inside : t.Contains p.val) (satisfies : test p.val = true)
  | absent (certificate : Certificate C.Reason) (checked : checkFailure C t certificate = true)

namespace First

/-- The first `k` children either yielded a witness, or all have failure
certificates. A witness prevents visiting any later children. -/
inductive Children (C : Pruner G test) {m : Nat} (nodes : Fin m → Node G) (k : Nat) (hk : k ≤ m) where
  | found (i : Fin k) (p : Element G)
      (inside : (nodes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).Contains p.val) (satisfies : test p.val = true)
  | absent (certificates : Vector (Certificate C.Reason) k)
      (checked : ∀ i : Fin k,
        checkFailure C (nodes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) certificates[i.val] = true)

@[expose] def collect (C : Pruner G test) {m : Nat} (nodes : Fin m → Node G)
    (visit : ∀ i : Fin m, Decision C (nodes i)) (k : Nat) (hk : k ≤ m) : Children C nodes k hk :=
  match k with
  | 0 => .absent #v[] (fun i => Fin.elim0 i)
  | k + 1 =>
    match collect C nodes visit k (Nat.le_trans (Nat.le_succ k) hk) with
    | .found i p hp ht => .found ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩ p hp ht
    | .absent certificates checked =>
      match visit ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ with
      | .found p hp ht => .found ⟨k, Nat.lt_succ_self _⟩ p hp ht
      | .absent certificate hc =>
        .absent (certificates.push certificate) (by
          intro i
          by_cases hi : i.val < k
          · rw [Vector.getElem_push_lt hi]
            exact checked ⟨i.val, hi⟩
          · have he : i.val = k := by omega
            simp only [he, Vector.getElem_push_eq]
            exact hc)

/-- Follow the checked chain and refine assigned images before expanding a
node. A successful leaf ends the search immediately. -/
@[expose] def visit (C : Pruner G test) (t : Node G) : Decision C t :=
  match hr : C.find t with
  | some r => .absent (.rejected r) (by simpa only [checkFailure] using C.checked t r hr)
  | none =>
    match hs : t.suffix with
    | .leaf S words =>
      if hp : test t.rep.val = true then
        .found t.rep t.contains_rep hp
      else .absent .leaf (by simp [checkFailure, hs, Bool.eq_false_iff.mpr hp])
    | .cons level tail =>
      match collect C (t.child hs) (fun i => visit C (t.child hs i))
          level.orbit.points.size (Nat.le_refl _) with
      | .found i p hp ht => .found p ((t.contains_children hs p.val).mpr ⟨i, hp⟩) ht
      | .absent certificates checked =>
        .absent (.branch certificates.toArray) (by
          rw [checkFailure_branch C t hs]
          simp only [Vector.size_toArray]
          exact decide_eq_true checked)
termination_by t.suffix.length
decreasing_by
  all_goals
    change tail.length < t.suffix.length
    rw [hs]
    exact Nat.lt_succ_self _

end First

/-- The original-generator program and defining equation are independently
checkable data for a positive transporter answer. -/
structure Witness (G : Group n) (test : Perm n → Bool) where
  value : Perm n
  word : Program
  checked : checkWitness G test value word = true

@[expose] def Witness.element (w : Witness G test) : Element G :=
  ⟨w.value, (checkWitness_spec G test w.value w.word w.checked).1⟩

theorem Witness.satisfies (w : Witness G test) : test w.value = true :=
  (checkWitness_spec G test w.value w.word w.checked).2

@[expose] def Witness.ofElement (p : Element G) (hp : test p.val = true) : Witness G test where
  value := p.val
  word := (G.word? p.val).get (by rw [Group.word?_isSome]; exact (G.contains_iff _).mpr p.property)
  checked := by
    rw [checkWitness, Bool.and_eq_true]
    refine ⟨?_, hp⟩
    apply G.word?_sound
    simp

inductive Answer (C : Pruner G test) where
  | found (witness : Witness G test)
  | absent (certificate : Certificate C.Reason) (checked : checkFailure C (Node.root G) certificate = true)

@[expose] def Answer.element? (C : Pruner G test) : Answer C → Option (Element G)
  | .found w => some w.element
  | .absent _ _ => none

theorem Answer.some_spec (C : Pruner G test) (a : Answer C) (p : Element G)
    (h : a.element? C = some p) : test p.val = true := by
  cases a with
  | found w => cases h; exact w.satisfies
  | absent certificate checked => cases h

theorem Answer.none_spec (C : Pruner G test) (a : Answer C) :
    a.element? C = none ↔ ¬ ∃ p : Element G, test p.val = true := by
  cases a with
  | found w =>
    constructor
    · intro h; cases h
    · intro h
      exact False.elim (h ⟨w.element, w.satisfies⟩)
  | absent certificate checked =>
    exact ⟨fun _ => checkFailure_spec C certificate checked, fun _ => rfl⟩

/-- Exact existence search carries either a checked positive word or a
complete negative certificate. -/
@[expose] def first (C : Pruner G test) : Answer C :=
  match First.visit C (Node.root G) with
  | .found p _ hp => .found (Witness.ofElement p hp)
  | .absent certificate checked => .absent certificate checked

end Hex.PermGroup.Search
