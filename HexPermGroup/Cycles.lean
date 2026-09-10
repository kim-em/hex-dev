/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm

public section

namespace Hex.Perm

/-- The sorted points moved by a permutation. -/
@[expose] def support (p : Perm n) : Array (Fin n) :=
  ((List.finRange n).filter fun i => p.get i ≠ i).toArray

@[simp] theorem mem_support (p : Perm n) (i : Fin n) :
    i ∈ p.support ↔ p.get i ≠ i := by
  simp [support]

/-- Follow one cycle, marking each point on its first visit. The degree bounds
its length, including when the cycle contains every point. -/
@[expose] def visit (p : Perm n) : Nat → Fin n → Vector Bool n →
    Array (Fin n) → Vector Bool n × Array (Fin n)
  | 0, _, seen, cycle => (seen, cycle)
  | fuel + 1, x, seen, cycle =>
    if seen[x.val] then (seen, cycle)
    else visit p fuel (p.get x) (seen.set x.val true) (cycle.push x)

/-- Scan the starting points, retaining the marks between visits. -/
@[expose] def scanCycles (p : Perm n) : List (Fin n) → Vector Bool n →
    Array (Array (Fin n)) → Vector Bool n × Array (Array (Fin n))
  | [], seen, result => (seen, result)
  | x :: xs, seen, result =>
    if seen[x.val] then p.scanCycles xs seen result
    else
      let (next, cycle) := p.visit n x seen #[]
      p.scanCycles xs next (result.push cycle)

/-- Disjoint cycles, including singleton fixed points. Scanning starting points
in order makes each cycle begin at its least point and orders the cycles. -/
@[expose] def allCycles (p : Perm n) : Array (Array (Fin n)) :=
  (p.scanCycles (List.finRange n) (Vector.replicate n false) #[]).2

/-- Canonical disjoint cycles, omitting fixed points. -/
@[expose] def cycles (p : Perm n) : Array (Array (Fin n)) :=
  p.allCycles.filter fun cycle => cycle.size > 1

/-- Sorted cycle lengths, with a one for every fixed point. Counting lengths
in the range `1,...,n` keeps the computation linear in the declared degree. -/
@[expose] def cycleType (p : Perm n) : Array Nat :=
  let counts := p.allCycles.foldl (fun counts cycle => counts.modify cycle.size (· + 1))
    (Array.replicate (n + 1) 0)
  (List.range (n + 1)).toArray.flatMap fun k => Array.replicate counts[k]! k

/-- Permutation sign from the number of cycles, including fixed points. -/
@[expose] def sign (p : Perm n) : Int :=
  if (n - p.allCycles.size) % 2 = 0 then 1 else -1

/-- The least common multiple of the cycle lengths; the empty lcm is one. -/
@[expose] def order (p : Perm n) : Nat :=
  p.cycles.foldl (fun k cycle => Nat.lcm k cycle.size) 1

/-- Natural powers, with function-composition multiplication. -/
@[expose] def pow (p : Perm n) : Nat → Perm n
  | 0 => Perm.id n
  | k + 1 => p.comp (pow p k)

@[simp] theorem pow_zero (p : Perm n) : p.pow 0 = Perm.id n := rfl
@[simp] theorem pow_succ (p : Perm n) (k : Nat) : p.pow (k + 1) = p.comp (p.pow k) := rfl

theorem pow_add (p : Perm n) (k l : Nat) : p.pow (k + l) = (p.pow k).comp (p.pow l) := by
  induction k with
  | zero => simp
  | succ k ih => simp [Nat.succ_add, ih, comp_assoc]

instance : Mul (Perm n) := ⟨comp⟩
instance : Inv (Perm n) := ⟨inv⟩
instance : OfNat (Perm n) 1 := ⟨Perm.id n⟩
instance : Pow (Perm n) Nat := ⟨pow⟩

@[simp] theorem mul_def (p q : Perm n) : p * q = p.comp q := rfl
@[simp] theorem inv_def (p : Perm n) : p⁻¹ = p.inv := rfl
@[simp] theorem one_def : (1 : Perm n) = Perm.id n := rfl
@[simp] theorem pow_def (p : Perm n) (k : Nat) : p ^ k = p.pow k := rfl

theorem sign_eq (p : Perm n) : p.sign = 1 ∨ p.sign = -1 := by
  unfold sign
  split <;> simp

end Hex.Perm
