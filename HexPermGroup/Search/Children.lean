/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Accumulator

public section

namespace Hex.PermGroup.Search

variable {G : Group n} {P : Predicate n}

/-- The first `k` children have been visited in order. Earlier certificates
are valid against the current accumulator, even after subsequent insertions. -/
structure Children (C : Constraint G P) {m : Nat} (nodes : Fin m → Node G)
    (a : Accumulator G P) (k : Nat) (hk : k ≤ m) where
  acc : Accumulator G P
  grows : a.group.IsSubgroup acc.group
  certificates : Vector (Certificate C.Reason) k
  checked : ∀ i : Fin k,
    checkTree C acc.group (nodes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) certificates[i.val] = true

namespace Children

/-- Process children in stored orbit order, carrying the subgroup forward and
appending one certificate for every child. -/
@[expose] def collect (C : Constraint G P) {m : Nat} (nodes : Fin m → Node G)
    (visit : ∀ a : Accumulator G P, ∀ i : Fin m, Result C (nodes i) a)
    (a : Accumulator G P) (k : Nat) (hk : k ≤ m) : Children C nodes a k hk :=
  match k with
  | 0 =>
    { acc := a
      grows := fun _ hp => hp
      certificates := #v[]
      checked := fun i => Fin.elim0 i }
  | k + 1 =>
    let previous := collect C nodes visit a k (by omega)
    let next := visit previous.acc ⟨k, by omega⟩
    { acc := next.acc
      grows := fun p hp => next.grows p (previous.grows p hp)
      certificates := previous.certificates.push next.certificate
      checked := by
        intro i
        by_cases hi : i.val < k
        · rw [Vector.getElem_push_lt hi]
          exact checkTree_mono C _ _ next.grows (previous.checked ⟨i.val, hi⟩)
        · have he : i.val = k := by omega
          simp only [he, Vector.getElem_push_eq]
          exact next.checked }

end Children

end Hex.PermGroup.Search
