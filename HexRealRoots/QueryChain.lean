/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PseudoGcd
public import HexBasic.OfFn
public import HexBasic.ArrayDecEq

public section

/-! Shared positive-scaled signed remainders and finite literal chain replay.
The head is retained literally. The initial product is reduced before chain
extension, and the terminal nonzero entry may be a nonconstant gcd. -/
namespace Hex

open scoped Hex

/-- Positive scales and a literal quotient for a three-term identity. -/
structure QueryStep (D : Type u) [Zero D] [DecidableEq D] where
  leftScale : D
  quotient : DensePoly D
  rightScale : D

/-- A signed remainder chain, its initial reduction, and a separate terminal
zero identity. A singleton chain has no terminal pair. -/
structure QueryChain (D : Type u) [Zero D] [DecidableEq D] where
  chain : Array (DensePoly D)
  /-- Literal degree data for serialized certificates; replay checks it against
  the stored entries as well as checking strict degree descent. -/
  degrees : Array Nat
  initial : QueryStep D
  steps : Array (QueryStep D)
  terminal : Option (D × DensePoly D)

namespace QueryChain

variable {D : Type u} [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D]

/-- No content removal; useful for small generic interpretation probes.
Unnormalized pseudo-remainder sequences can have exponential coefficient growth.
Production backends should supply a proved positive normalization. -/
@[expose] def normalizeId (p : DensePoly D) : D × DensePoly D := (1, p)

/-- Extend the chain using only positive-scaled pseudo-division. The internal
bound comes from the original head degree. Under the normalization laws,
strict degree descent reaches the terminal zero branch within that bound.
The zero-fuel value lacks terminal evidence and cannot pass replay for a pair. -/
@[expose] def buildAux [Neg D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D) :
    Nat → DensePoly D → DensePoly D → Array (DensePoly D) → Array (QueryStep D) →
      Array (DensePoly D) × Array (QueryStep D) × Option (D × DensePoly D)
  | 0, _, _, chain, steps => (chain, steps, none)
  | fuel + 1, prev, cur, chain, steps =>
    let r := DensePoly.positivePseudoDiv sign prev cur
    if r.remainder.isZero then
      (chain, steps, some (r.multiplier, r.quotient))
    else
      let (factor, reduced) := normalize r.remainder
      let next := -reduced
      buildAux sign normalize fuel cur next (chain.push next)
        (steps.push ⟨r.multiplier, r.quotient, factor⟩)

/-- The input-derived bound reaches a terminal zero identity when normalized
nonzero remainders stay nonzero and do not increase stored size. This is an
adequacy theorem for the actual recursive loop, separate from query semantics. -/
theorem buildAux_complete [Neg D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnext : ∀ r : DensePoly D, r ≠ 0 →
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size ≤ r.size)
    (fuel : Nat) (prev cur : DensePoly D) (chain : Array (DensePoly D)) (steps : Array (QueryStep D))
    (hcur : cur ≠ 0) (bound : cur.size ≤ fuel) :
    (buildAux sign normalize fuel prev cur chain steps).2.2.isSome = true := by
  induction fuel generalizing prev cur chain steps with
  | zero =>
    exact False.elim (hcur ((DensePoly.size_eq_zero_iff cur).mp (by omega)))
  | succ fuel ih =>
    simp only [buildAux]
    split
    · rfl
    · rename_i hr
      have hr' : (DensePoly.positivePseudoDiv sign prev cur).remainder ≠ 0 := by
        intro hzero
        rw [hzero] at hr
        exact hr rfl
      have hn := hnext _ hr'
      have hdrop := DensePoly.positivePseudoDiv_remainder_lt sign prev cur hcur
      apply ih _ _ _ _ hn.1
      omega

/-- Strict size descent bounds the number of appended entries, including when
an internal call is viewed at an arbitrary finite recursion depth. -/
theorem buildAux_size [Neg D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnext : ∀ r : DensePoly D, r ≠ 0 →
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size ≤ r.size)
    (fuel : Nat) (prev cur : DensePoly D) (chain : Array (DensePoly D)) (steps : Array (QueryStep D))
    (hcur : cur ≠ 0) :
    (buildAux sign normalize fuel prev cur chain steps).1.size ≤ chain.size + cur.size - 1 := by
  induction fuel generalizing prev cur chain steps with
  | zero =>
    simp only [buildAux]
    have hpos := Nat.pos_of_ne_zero (fun h => hcur ((DensePoly.size_eq_zero_iff cur).mp h))
    omega
  | succ fuel ih =>
    simp only [buildAux]
    split
    · dsimp only
      have hpos := Nat.pos_of_ne_zero (fun h => hcur ((DensePoly.size_eq_zero_iff cur).mp h))
      omega
    · rename_i hr
      have hr' : (DensePoly.positivePseudoDiv sign prev cur).remainder ≠ 0 := by
        intro hz
        rw [hz] at hr
        exact hr rfl
      have hn := hnext _ hr'
      have hd := DensePoly.positivePseudoDiv_remainder_lt sign prev cur hcur
      have hb := ih cur (-(normalize (DensePoly.positivePseudoDiv sign prev cur).remainder).2)
        (chain.push (-(normalize (DensePoly.positivePseudoDiv sign prev cur).remainder).2))
        (steps.push ⟨(DensePoly.positivePseudoDiv sign prev cur).multiplier,
          (DensePoly.positivePseudoDiv sign prev cur).quotient,
          (normalize (DensePoly.positivePseudoDiv sign prev cur).remainder).1⟩) hn.1
      simp only [Array.size_push] at hb
      omega

/-- Produce the signed chain of `(p, f*p')` after the mandatory initial
reduction. Normalization is a total polynomial backend operation: its laws
require a positive factor and preservation of the polynomial up to that factor.
It supplies no coefficient-operation certificates or arithmetic budgets. -/
@[expose] def build [Neg D] [NatCast D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D) (p f : DensePoly D) : QueryChain D :=
  let r := DensePoly.positivePseudoDiv sign (f * p.derivative) p
  if r.remainder.isZero then
    { chain := #[p], degrees := #[p.natDegree]
      initial := ⟨r.multiplier, r.quotient, 1⟩, steps := #[], terminal := none }
  else
    let (factor, second) := normalize r.remainder
    let result := buildAux sign normalize p.natDegree p second #[p, second] #[]
    { chain := result.1, degrees := Hex.Array.map' DensePoly.natDegree result.1
      initial := ⟨r.multiplier, r.quotient, factor⟩
      steps := result.2.1, terminal := result.2.2 }

/-- A nonzero initial remainder reaches terminal evidence using exactly the
head's internally computed degree bound. -/
theorem build_terminal [Neg D] [NatCast D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnormalize : ∀ r : DensePoly D, r ≠ 0 →
      (normalize r).2 ≠ 0 ∧ (normalize r).2.size ≤ r.size)
    (hnext : ∀ r : DensePoly D, r ≠ 0 →
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size ≤ r.size)
    (p f : DensePoly D) (hp : p ≠ 0)
    (hr : (DensePoly.positivePseudoDiv sign (f * p.derivative) p).remainder.isZero = false) :
    (build sign normalize p f).terminal.isSome = true := by
  simp only [build, hr, Bool.false_eq_true, ↓reduceIte]
  have hr' : (DensePoly.positivePseudoDiv sign (f * p.derivative) p).remainder ≠ 0 := by
    intro hz
    rw [hz] at hr
    contradiction
  have hn := hnormalize _ hr'
  apply buildAux_complete sign normalize hnext _ _ _ _ _ hn.1
  have hd := DensePoly.positivePseudoDiv_remainder_lt sign (f * p.derivative) p hp
  rw [DensePoly.natDegree_eq_size_sub_one]
  omega

/-- A produced chain has at most `degree p + 1` entries for nonzero `p`. -/
theorem build_size [Neg D] [NatCast D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnormalize : ∀ r : DensePoly D, r ≠ 0 →
      (normalize r).2 ≠ 0 ∧ (normalize r).2.size ≤ r.size)
    (hnext : ∀ r : DensePoly D, r ≠ 0 →
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size ≤ r.size)
    (p f : DensePoly D) (hp : p ≠ 0) : (build sign normalize p f).chain.size ≤ p.size := by
  simp only [build]
  split
  · change 1 ≤ p.size
    exact Nat.pos_of_ne_zero (fun h => hp ((DensePoly.size_eq_zero_iff p).mp h))
  · rename_i hr
    have hr' : (DensePoly.positivePseudoDiv sign (f * p.derivative) p).remainder ≠ 0 := by
      intro hz
      rw [hz] at hr
      exact hr rfl
    have hn := hnormalize _ hr'
    have hb := buildAux_size sign normalize hnext p.natDegree p
      (normalize (DensePoly.positivePseudoDiv sign (f * p.derivative) p).remainder).2
      #[p, (normalize (DensePoly.positivePseudoDiv sign (f * p.derivative) p).remainder).2] #[] hn.1
    have hd := DensePoly.positivePseudoDiv_remainder_lt sign (f * p.derivative) p hp
    have hsize : #[p, (normalize
        (DensePoly.positivePseudoDiv sign (f * p.derivative) p).remainder).2].size = 2 := rfl
    rw [hsize] at hb
    exact Nat.le_trans hb (by omega)

/-- Arithmetic identities test a zero difference. This is intentionally
separate from the literal equality used for the head and context bindings. -/
@[expose] def equal (p q : DensePoly D) : Bool := (p - q).isZero

/-- Check a positive three-term recurrence without performing division. -/
@[expose] def checkStep (sign : D → Int) (a b c : DensePoly D) (s : QueryStep D) : Bool :=
  decide (sign s.leftScale = 1) && decide (sign s.rightScale = 1) &&
    equal (DensePoly.scale s.leftScale a) (s.quotient * b - DensePoly.scale s.rightScale c)

/-- Literal finite replay of the initial reduction, degree evidence, all
recurrences and the terminal zero identity. No gcd or chain producer runs. -/
@[expose] def check [NatCast D] (sign : D → Int) (p f : DensePoly D) (cert : QueryChain D) : Bool :=
  let n := cert.chain.size
  !p.isZero && decide (0 < n) && decide (n ≤ p.size) &&
    decide (cert.chain[0]? = some p) &&
    decide (cert.degrees = Hex.Array.map' DensePoly.natDegree cert.chain) &&
    cert.chain.all (fun r => !r.isZero) &&
    (Array.range (n - 1)).all (fun i =>
      (cert.chain.getD (i + 1) 0).size < (cert.chain.getD i 0).size) &&
    decide (sign cert.initial.leftScale = 1) && decide (sign cert.initial.rightScale = 1) &&
    equal (DensePoly.scale cert.initial.leftScale (f * p.derivative))
      (cert.initial.quotient * p + DensePoly.scale cert.initial.rightScale (cert.chain.getD 1 0)) &&
    if n = 1 then cert.steps.isEmpty && cert.terminal.isNone
    else
      decide (cert.steps.size + 2 = n) &&
      (Array.range cert.steps.size).all (fun i =>
        checkStep sign (cert.chain.getD i 0) (cert.chain.getD (i + 1) 0)
          (cert.chain.getD (i + 2) 0) (cert.steps.getD i ⟨0, 0, 0⟩)) &&
      match cert.terminal with
      | none => false
      | some (factor, quotient) =>
        decide (sign factor = 1) &&
          equal (DensePoly.scale factor (cert.chain.getD (n - 2) 0))
            (quotient * cert.chain.getD (n - 1) 0)

end QueryChain
end Hex
