/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks.Trials

public section

namespace Hex.PermGroup.Primitivity

/-- Replay every off-diagonal seeded test. Omitting a test cannot certify
primitivity, even when all traces that remain are individually valid. -/
@[expose] def check (G : Group n) (a : Fin n)
    (traces : Vector (List (Fin n × Fin n)) n) : Bool :=
  decide (∀ b : Fin n, b ≠ a →
    Blocks.check G.chain.generators [(a, b)] (Partition.indiscrete n) traces[b.val] = true)

theorem check_sound {G : Group n} {a : Fin n} {traces : Vector (List (Fin n × Fin n)) n}
    (hn : 2 ≤ n) (ht : G.isTransitive = true) (h : check G a traces = true) : G.IsPrimitive := by
  apply (G.primitive_criterion hn ht a).mpr
  exact (Checks.mk traces (of_decide_eq_true h) : Checks G a n (Nat.le_refl n)).criterion

/-- Every verdict contains a complete reason: a degree obstruction, unreachable
point, nontrivial invariant partition, or all seeded block certificates. -/
inductive Verdict (G : Group n) where
  | small (degree : n < 2)
  | intransitive (source target : Fin n) (missing : target ∉ G.orbit source)
  | imprimitive (point : Fin n) (failure : Failure G point)
  | primitive (degree : 2 ≤ n) (transitive : G.isTransitive = true)
      (point : Fin n) (checks : Checks G point n (Nat.le_refl n))

namespace Verdict

/-- Extract the Boolean decision without discarding the separately available
certificate or obstruction. -/
@[expose] def accepted (v : Verdict G) : Bool :=
  match v with
  | .primitive .. => true
  | _ => false

theorem accepted_iff {G : Group n} (v : Verdict G) : v.accepted = true ↔ G.IsPrimitive := by
  cases v with
  | small hn =>
    simp only [accepted, Bool.false_eq_true, false_iff]
    intro h
    have hh := h.1
    omega
  | intransitive a b hb =>
    simp only [accepted, Bool.false_eq_true, false_iff]
    intro h
    exact hb ((G.mem_orbit a b).mpr ((G.isTransitive_iff.mp h.2.1).2 a b))
  | imprimitive a f =>
    simp only [accepted, Bool.false_eq_true, false_iff]
    exact f.not_primitive
  | primitive hn ht a c =>
    simp only [accepted, true_iff]
    exact (G.primitive_criterion hn ht a).mpr c.criterion

end Verdict

/-- Decide transitivity at point zero, then perform the complete seeded
criterion. Neither degree zero nor degree one enters the block search. -/
@[expose] def decide (G : Group n) : Verdict G :=
  if hn : 2 ≤ n then
    let a : Fin n := ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hn⟩
    let points := G.orbit a
    match hf : (List.finRange n).find? (fun b => !points.contains b) with
    | some b => .intransitive a b (by
        have h := List.find?_some hf
        simpa [points] using h)
    | none =>
      have ht : G.isTransitive = true := by
        have h := List.find?_eq_none.mp hf
        unfold Group.isTransitive
        rw [dite_eq_left (Nat.lt_of_lt_of_le (by decide : 0 < 2) hn)]
        apply decide_eq_true
        intro b
        have hb := h b (by simp)
        simpa [points, a] using hb
      match scan G a n (Nat.le_refl n) with
      | .complete checks => .primitive hn ht a checks
      | .imprimitive failure => .imprimitive a failure
  else .small (by omega)

end Hex.PermGroup.Primitivity

namespace Hex.PermGroup.Group

/-- A complete primitivity certificate or an explicit obstruction. -/
@[expose] def primitivity (G : Group n) : Primitivity.Verdict G := Primitivity.decide G

/-- Primitive means transitive of degree at least two, with no nontrivial
invariant partition. The certificate remains available through `primitivity`. -/
@[expose] def isPrimitive (G : Group n) : Bool := G.primitivity.accepted

theorem isPrimitive_iff (G : Group n) : G.isPrimitive = true ↔ G.IsPrimitive :=
  G.primitivity.accepted_iff

end Hex.PermGroup.Group
