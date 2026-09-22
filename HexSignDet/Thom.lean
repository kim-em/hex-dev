/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.TableProducer

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

/-- Literal input for a selected squarefree root. Derivative polynomials are
reconstructed from the head; callers supply only their indices and signs. -/
structure RawDescriptor (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  context : Ctx
  head : DensePoly E
  lower : Endpoint E
  upper : Endpoint E
  indices : List Nat
  signs : List Int

variable [NatCast E] [Mul E]

/-- The next `n` formal derivatives, without normalization or sign-changing
scaling. Each derivative is computed once from its predecessor. -/
@[expose] def derivativesFrom (p : DensePoly E) : Nat → List (DensePoly E)
  | 0 => []
  | n + 1 => let q := p.derivative; q :: derivativesFrom q n

@[expose] def derivatives (p : DensePoly E) : List (DensePoly E) :=
  derivativesFrom p p.natDegree

theorem derivativesFrom_length (p : DensePoly E) (n : Nat) :
    (derivativesFrom p n).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [derivativesFrom, List.length_cons, ih]

/-- Shape checks for derivative indices and their corresponding signs.
Index zero is not a derivative slot, and the highest derivative is retained. -/
@[expose] def RawDescriptor.wellFormed (d : RawDescriptor E Ctx) : Bool :=
  decide (0 < d.head.natDegree) && decide (d.indices.length = d.signs.length) &&
  decide d.indices.Nodup && d.indices.all (fun i => decide (1 ≤ i ∧ i ≤ d.head.natDegree)) &&
  d.signs.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1))

/-- Ordered derivative queries. This internal extraction is used only after
`wellFormed` has excluded zero and out-of-range indices. -/
@[expose] def RawDescriptor.queries (d : RawDescriptor E Ctx) : List (DensePoly E) :=
  let ds := derivatives d.head
  d.indices.map fun i => ds[i - 1]?.getD 0

namespace Thom

/-- Inspect the highest differing position first. A difference in the last
slot, or with zero common next sign, cannot be ordered by the Thom rule. -/
@[expose] def compareFrom : List Int → List Int → Option Ordering
  | [], [] => some .eq
  | a :: as, b :: bs => do
    let order ← compareFrom as bs
    if order != .eq then return order
    if a = b then return .eq
    let next ← as.head?
    if next = 1 then return compare a b
    if next = -1 then return compare b a
    none
  | _, _ => none

/-- Finite largest-differing-index rule on sign vectors. This checks vector
shape, not realization or polynomial/context identity. Only validated full
descriptors of the same head may use it for root comparison. -/
@[expose] def compareSigns (as bs : List Int) : Option Ordering :=
  if as.isEmpty || bs.isEmpty ||
      !as.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) ||
      !bs.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) then none
  else compareFrom as bs

theorem compareFrom_self (as : List Int) : compareFrom as as = some .eq := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [compareFrom, ih]

/-- Equality returned by the finite rule is exact vector equality. This
does not identify roots belonging to different polynomials or contexts. -/
theorem compareFrom_eq {as bs : List Int} (h : compareFrom as bs = some .eq) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [compareFrom]
  | cons a as ih =>
    cases bs with
    | nil => simp [compareFrom] at h
    | cons b bs =>
      cases ht : compareFrom as bs with
      | none => simp [compareFrom, ht] at h
      | some order =>
        cases order with
        | lt => simp [compareFrom, ht] at h
        | gt => simp [compareFrom, ht] at h
        | eq =>
          have he := ih ht
          subst bs
          by_cases hab : a = b
          · simp [hab]
          · simp only [compareFrom, ht, ↓reduceIte, hab] at h
            cases hh : as.head? with
            | none => simp [hh] at h
            | some next =>
              by_cases hp : next = 1
              · simp [hh, hp, Std.LawfulEqCmp.compare_eq_iff_eq] at h
                exact False.elim (hab h)
              · by_cases hn : next = -1
                · simp [hh, hn, Std.LawfulEqCmp.compare_eq_iff_eq] at h
                  exact False.elim (hab h.symm)
                · simp [hh, hp, hn] at h

theorem compareSigns_eq {as bs : List Int} (h : compareSigns as bs = some .eq) : as = bs := by
  unfold compareSigns at h
  split at h
  · contradiction
  · exact compareFrom_eq h

end Thom

end Hex.SignDet
