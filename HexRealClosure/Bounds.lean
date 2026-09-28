/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Basic

public section

/-!
# Finite Cauchy bound search

The strict coefficient test needs no coefficient division. The search tries
exactly the prescribed finite dyadic candidates and may return no bound.
Root isolation must then complete on the whole line by sign determination.
-/

namespace Hex.RealClosure.Bounds

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Neg E]
variable [Sub E] [Mul E] [NatCast E]

/-- Absolute value using the predecessor's total sign operation. -/
@[expose] def abs (sign : E → Int) (a : E) : E :=
  if sign a < 0 then -a else a

/-- The strict Cauchy test `B > 1` and
`|aᵢ| < (B - 1) * |aₙ|` for every coefficient below the leading term. -/
@[expose] def check (sign : E → Int) (p : DensePoly E) (bound : E) : Bool :=
  !p.isZero && (0 < sign (bound - 1)) &&
    (let limit := (bound - 1) * abs sign p.leadingCoeff
     (List.range p.natDegree).all fun i => 0 < sign (limit - abs sign (p.coeff i)))

/-- A finite bound accepted for this exact stored polynomial and sign operation.
Its mathematical root bound is established in the companion. -/
structure Bound (sign : E → Int) (p : DensePoly E) where
  private mk ::
  value : E
  accepted : check sign p value = true

namespace Bound

/-- Test one dyadic candidate without discarding its checked provenance. -/
def candidate? (sign : E → Int) (p : DensePoly E) (exponent : Nat) :
    Option (Bound sign p) :=
  let bound : E := (2 ^ exponent : Nat)
  if h : check sign p bound = true then some ⟨bound, h⟩ else none

end Bound

/-- Finite policy: exponents `1, …, 2 * (degree p + 1)`, in that order.
Failure requests whole-line BKR completion; it does not mean there are no roots. -/
@[expose] def find? (sign : E → Int) (p : DensePoly E) : Option (Bound sign p) :=
  (List.range (2 * (p.natDegree + 1))).findSome? fun i => Bound.candidate? sign p (i + 1)

omit [NatCast E] in
/-- The coefficient test never accepts a zero polynomial. -/
theorem check_nonzero {sign : E → Int} {p : DensePoly E} {bound : E}
    (checked : check sign p bound = true) : p ≠ 0 := by
  intro h
  subst p
  have hz : (0 : DensePoly E).isZero = true :=
    (DensePoly.isZero_eq_true_iff _).mpr DensePoly.size_zero
  simp only [check, hz, Bool.not_true, Bool.false_and, Bool.false_eq_true] at checked

/-- The successful candidate retains the literal tested value. -/
theorem Bound.candidate?_value {sign : E → Int} {p : DensePoly E} {exponent : Nat}
    {bound : Bound sign p} (h : candidate? sign p exponent = some bound) :
    bound.value = ((2 ^ exponent : Nat) : E) := by
  unfold candidate? at h
  dsimp only at h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

/-- Every successful search result comes from the prescribed finite range. -/
theorem find?_exponent {sign : E → Int} {p : DensePoly E} {bound : Bound sign p}
    (h : find? sign p = some bound) :
    ∃ exponent, 1 ≤ exponent ∧ exponent ≤ 2 * (p.natDegree + 1) ∧
      bound.value = ((2 ^ exponent : Nat) : E) := by
  obtain ⟨i, hi, hc⟩ := List.exists_of_findSome?_eq_some h
  have hi' := List.mem_range.mp hi
  exact ⟨i + 1, by omega, by omega, Bound.candidate?_value hc⟩

/-- Candidate failure means that exact coefficient test failed. -/
theorem Bound.candidate?_none (sign : E → Int) (p : DensePoly E) (exponent : Nat) :
    candidate? sign p exponent = none ↔
      check sign p ((2 ^ exponent : Nat) : E) = false := by
  unfold candidate?
  dsimp only
  split <;> simp_all

/-- Search failure rejects all the finite candidates, without claiming that
the polynomial has no roots or that no larger bound could work. -/
theorem find?_none (sign : E → Int) (p : DensePoly E) :
    find? sign p = none ↔ ∀ i < 2 * (p.natDegree + 1),
      check sign p ((2 ^ (i + 1) : Nat) : E) = false := by
  simp only [find?, List.findSome?_eq_none_iff, List.mem_range, Bound.candidate?_none]

end Hex.RealClosure.Bounds
