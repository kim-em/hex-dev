/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.Crt
public import HexModular.Euclid

public section

/-!
Bounded, vector, and maximal-quotient rational reconstruction.
-/
namespace Hex

namespace Modular

/-- Check that `x` represents `a` modulo `m` and satisfies the requested
numerator and denominator bounds. This is split from the Euclidean search so
certificate replay need not unfold that search. -/
@[expose]
def ratReconCheck (a : Int) (m : Nat) (P Q : Int) (x : Rat) : Bool :=
  decide (0 < m) &&
    decide ((Int.ofNat x.den * a - x.num) % (m : Int) = 0) &&
    decide ((x.num.natAbs : Int) ≤ P) &&
    decide ((0 : Int) < x.den) &&
    decide ((x.den : Int) ≤ Q)

/-- Reconstruct `a mod m` as a rational with numerator absolute value at most
`P` and positive denominator at most `Q`. The truncated Euclidean candidate is
normalized and all output conditions are checked before it is returned. -/
def ratRecon? (a : Int) (m : Nat) (P Q : Int) : Option Rat :=
  if m = 0 then
    none
  else
    let row := euclidUntil (Int.ofNat m) a P
    if row.t = 0 then
      none
    else
      let candidate := Rat.divInt row.r row.t
      if ratReconCheck a m P Q candidate then some candidate else none

/-- Symmetric rational reconstruction with
`P = Q = ⌊√((m-1)/2)⌋`, which guarantees `2 P Q < m`. -/
def ratReconWide? (a : Int) (m : Nat) : Option Rat :=
  let bound := Nat.sqrt ((m - 1) / 2)
  ratRecon? a m (Int.ofNat bound) (Int.ofNat bound)

/-- Every rational returned by bounded reconstruction satisfies the requested
modular congruence. -/
theorem ratRecon?_congr {a : Int} {m : Nat} {P Q : Int} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    (Int.ofNat x.den * a - x.num) % (m : Int) = 0 := by
  unfold ratRecon? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next candidate hcheck =>
    cases h
    simp only [ratReconCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨⟨⟨_, hcongr⟩, _⟩, _⟩, _⟩
    exact hcongr

/-- Every rational returned by bounded reconstruction satisfies the requested
numerator and denominator bounds. -/
theorem ratRecon?_bounds {a : Int} {m : Nat} {P Q : Int} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    (x.num.natAbs : Int) ≤ P ∧ 0 < x.den ∧ (x.den : Int) ≤ Q := by
  unfold ratRecon? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next candidate hcheck =>
    cases h
    simp only [ratReconCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨⟨⟨_, _⟩, hnum⟩, hdenpos⟩, hdenBound⟩
    exact ⟨hnum, by simpa using hdenpos, hdenBound⟩

/-- The reduced denominator of a successful reconstruction is coprime to the
modulus. -/
theorem ratRecon?_den_coprime {a : Int} {m : Nat} {P Q : Int} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    Nat.gcd x.den m = 1 := by
  sorry

/-- Rational reconstruction is unique whenever twice the product of the two
bounds is strictly smaller than the modulus. -/
theorem ratRecon_unique {a P Q : Int} {m : Nat} {y₁ y₂ : Rat}
    (hm : 2 * P * Q < (m : Int))
    (h₁ : (Int.ofNat y₁.den * a - y₁.num) % (m : Int) = 0)
    (h₂ : (Int.ofNat y₂.den * a - y₂.num) % (m : Int) = 0)
    (b₁ : (y₁.num.natAbs : Int) ≤ P ∧ (y₁.den : Int) ≤ Q)
    (b₂ : (y₂.num.natAbs : Int) ≤ P ∧ (y₂.den : Int) ≤ Q) :
    y₁ = y₂ := by
  sorry

/-- Under the uniqueness bound, bounded reconstruction finds every rational
that satisfies the congruence and bounds. -/
theorem ratRecon?_complete {a P Q : Int} {m : Nat} {y : Rat}
    (hm : 2 * P * Q < (m : Int))
    (hy : (Int.ofNat y.den * a - y.num) % (m : Int) = 0)
    (hb : (y.num.natAbs : Int) ≤ P ∧ (y.den : Int) ≤ Q) :
    ratRecon? a m P Q = some y := by
  sorry

/-- Check a vector reconstruction with common denominator. -/
private def ratReconVecCheck (a y : Vector Int k) (m : Nat) (P Q d : Int) : Bool :=
  decide (0 < m) && decide (0 < d) && decide (d ≤ Q) &&
    (Vector.zipWith
      (fun ai yi =>
        decide ((d * ai - yi) % (m : Int) = 0) &&
          decide ((yi.natAbs : Int) ≤ P))
      a y).toArray.all (fun ok => ok)

/-- Process the remaining coordinates of a common-denominator reconstruction.
The index increases until it reaches the statically known vector length. -/
private def ratReconVec.go (a : Vector Int k) (m : Nat) (P Q : Int)
    (i : Nat) (hi : i ≤ k) (nums : Vector Int k) (d : Nat) :
    Option (Vector Int k × Nat) :=
  if hik : i = k then
    some (nums, d)
  else
    have hlt : i < k := by omega
    let residue := a[i]
    let fast := symMod (Int.ofNat d * residue) m
    if (fast.natAbs : Int) ≤ P then
      ratReconVec.go a m P Q (i + 1) (by omega) (nums.set i fast) d
    else do
      let entry ← ratRecon? residue m P Q
      let newD := Nat.lcm d entry.den
      let oldScale := Int.ofNat (newD / d)
      let entryScale := Int.ofNat (newD / entry.den)
      let nums :=
        (nums.map fun value => value * oldScale).set i (entry.num * entryScale)
      ratReconVec.go a m P Q (i + 1) (by omega) nums newD
termination_by k - i
decreasing_by all_goals exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self i)

/-- Reconstruct `k` residues as rationals with a common denominator. The first
entry seeds the denominator. Later entries first try one symmetric
multiplication at that denominator, falling back to their own Euclidean run
only when necessary. Denominators are combined with `lcm`, and the final
numerator vector and denominator are reduced by their common gcd. -/
def ratReconVec? (a : Vector Int k) (m : Nat) (P Q : Int) :
    Option (Vector Int k × Int) :=
  if hk : k = 0 then
    let y := Vector.replicate k (0 : Int)
    if ratReconVecCheck a y m P Q 1 then
      some (y, 1)
    else
      none
  else
    do
      have hkpos : 0 < k := by omega
      let first ← ratRecon? a[0] m P Q
      let nums := (Vector.replicate k (0 : Int)).set 0 first.num
      let (nums, d) ← ratReconVec.go a m P Q 1 (by omega) nums first.den
      let common := nums.foldl (fun g value => Nat.gcd g value.natAbs) d
      let reducedNums := nums.map fun value => value / Int.ofNat common
      let reducedDen := d / common
      let denInt := Int.ofNat reducedDen
      if ratReconVecCheck a reducedNums m P Q denInt then
        some (reducedNums, denInt)
      else
        none

/-- A successful common-denominator vector reconstruction has a positive
bounded denominator, and every coordinate satisfies its congruence and
numerator bound. -/
theorem ratReconVec?_spec {a : Vector Int k} {m : Nat} {P Q d : Int}
    {y : Vector Int k}
    (h : ratReconVec? a m P Q = some (y, d)) :
    0 < d ∧ d ≤ Q ∧
      ∀ i : Fin k,
        (d * a[i] - y[i]) % (m : Int) = 0 ∧ (y[i].natAbs : Int) ≤ P := by
  sorry

/-- Track the row immediately preceding the largest quotient in an extended
Euclidean run. -/
private def maxQuotRow.go (oldR r : Nat) (oldT t : Int)
    (bestQuot : Nat) (best : Option Row) : Option Row :=
  if _hr : r = 0 then
    best
  else
    let quotient := oldR / r
    let (bestQuot, best) :=
      if bestQuot < quotient then
        (quotient, some { r := Int.ofNat r, t })
      else
        (bestQuot, best)
    maxQuotRow.go r (oldR % r) t (oldT - Int.ofNat quotient * t)
      bestQuot best
termination_by r
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hr)

/-- Produce the maximal-quotient rational-reconstruction candidate. This is a
heuristic: only the modular congruence is checked and promised. -/
def ratReconMaxQuot? (a : Int) (m : Nat) : Option Rat :=
  if _hm : m = 0 then
    none
  else
    let residue := (a % (m : Int)).natAbs
    if residue = 0 then
      some 0
    else
      match maxQuotRow.go m residue 0 1 0 none with
      | none => none
      | some row =>
          if row.t = 0 then
            none
          else
            let candidate := Rat.divInt row.r row.t
            if (Int.ofNat candidate.den * a - candidate.num) % (m : Int) = 0 then
              some candidate
            else
              none

/-- A maximal-quotient candidate always satisfies the modular congruence; no
claim is made that it is the intended rational. -/
theorem ratReconMaxQuot?_congr {a : Int} {m : Nat} {x : Rat}
    (h : ratReconMaxQuot? a m = some x) :
    (Int.ofNat x.den * a - x.num) % (m : Int) = 0 := by
  unfold ratReconMaxQuot? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h
  · cases h
    have hr : a % (m : Int) = 0 := Int.natAbs_eq_zero.mp (by assumption)
    simpa [hr]
  · split at h <;> try contradiction
    split at h <;> try contradiction
    try dsimp only at h
    split at h <;> try contradiction
    next candidate hcheck =>
      cases h
      exact hcheck

end Modular

end Hex
