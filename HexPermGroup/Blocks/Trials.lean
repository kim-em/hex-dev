/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks.Primitive

public section

namespace Hex.PermGroup.Primitivity

/-- The first `k` seed tests have complete forced-union traces. The diagonal
test is vacuous and uses an empty trace without running a block search. -/
structure Checks (G : Group n) (a : Fin n) (k : Nat) (hk : k ≤ n) where
  traces : Vector (List (Fin n × Fin n)) k
  checked : ∀ i : Fin k,
    let b : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    b ≠ a → Blocks.check G.chain.generators [(a, b)] (Partition.indiscrete n) traces[i.val] = true

/-- A checked invariant partition that is neither discrete nor indiscrete. -/
structure Failure (G : Group n) (a : Fin n) where
  point : Fin n
  distinct : point ≠ a
  solution : Blocks.Solution G.chain.generators [(a, point)]
  proper : solution.partition ≠ Partition.indiscrete n

namespace Failure

variable {G : Group n} {a : Fin n}

theorem invariant (f : Failure G a) : f.solution.partition.IsInvariant G := by
  intro g hg x y
  exact f.solution.admissible.invariant.generated G.chain_symmetric
    ((G.chain_generated g).mpr hg) x y

theorem nondiscrete (f : Failure G a) : f.solution.partition ≠ Partition.discrete n := by
  intro h
  have hs := f.solution.admissible.seeds (a, f.point) (by simp)
  rw [h, Partition.discrete_same] at hs
  exact f.distinct hs.symm

theorem not_primitive (f : Failure G a) : ¬G.IsPrimitive := by
  intro h
  rcases h.2.2 f.solution.partition f.invariant with hd | hi
  · exact f.nondiscrete hd
  · exact f.proper hi

end Failure

/-- Either all tests through `k` are complete, or an explicit nontrivial
invariant partition has been found. -/
inductive Result (G : Group n) (a : Fin n) (k : Nat) (hk : k ≤ n) where
  | complete (checks : Checks G a k hk)
  | imprimitive (failure : Failure G a)

namespace Checks

variable {G : Group n} {a : Fin n} {k : Nat} {hk : k ≤ n}

/-- Append one successful seed test to the already checked prefix. -/
@[expose] def push (c : Checks G a k hk) (hn : k + 1 ≤ n)
    (trace : List (Fin n × Fin n))
    (h : let b : Fin n := ⟨k, by omega⟩
      b ≠ a → Blocks.check G.chain.generators [(a, b)] (Partition.indiscrete n) trace = true) :
    Checks G a (k + 1) hn where
  traces := c.traces.push trace
  checked := by
    intro i
    dsimp only
    intro hb
    by_cases hi : i.val < k
    · rw [Vector.getElem_push_lt hi]
      exact c.checked ⟨i.val, hi⟩ hb
    · have he : i.val = k := by omega
      simp only [he, Vector.getElem_push_eq]
      exact h (by simpa only [he] using hb)

/-- Complete traces prove the seeded criterion without rerunning the producer. -/
theorem criterion (c : Checks G a n (Nat.le_refl n)) :
    ∀ b, b ≠ a → G.blocks [(a, b)] = Partition.indiscrete n := by
  intro b hb
  let s : Blocks.Solution G.chain.generators [(a, b)] :=
    ⟨Partition.indiscrete n, c.traces[b.val], c.checked b hb⟩
  exact (G.blocksCert [(a, b)]).unique s

end Checks

/-- Visit other points in natural order, retaining each completed block trace
and stopping immediately at a nontrivial invariant partition. -/
@[expose] def scan (G : Group n) (a : Fin n) (k : Nat) (hk : k ≤ n) : Result G a k hk :=
  match k with
  | 0 => .complete ⟨#v[], fun i => Fin.elim0 i⟩
  | k + 1 =>
    match scan G a k (Nat.le_trans (Nat.le_succ k) hk) with
    | .imprimitive f => .imprimitive f
    | .complete previous =>
      let b : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      if h : b = a then .complete (previous.push hk [] (fun hb => False.elim (hb h)))
      else
        let s := G.blocksCert [(a, b)]
        if hp : s.partition = Partition.indiscrete n then
          .complete (previous.push hk s.trace (fun _ => hp ▸ s.checked))
        else .imprimitive ⟨b, h, s, hp⟩

end Hex.PermGroup.Primitivity
