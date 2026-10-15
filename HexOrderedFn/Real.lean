/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Search
public import HexOrderedFn.Oracle
public import HexRationalFn

/-!
Horner bounds, finite trials and total refinement searches on canonical fractions.
Formal zero is algebraic; nonzero signs require separated numerator and denominator bounds.
-/

@[expose] public section

namespace Hex.OrderedFn.Real

open Oracle
universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]

/-- Positive requested width at refinement index `n`. -/
def precision (n : Nat) : Rat := 1 / (2 : Rat) ^ n

/-- Exact Horner bounds, refining every coefficient and the argument together. -/
noncomputable def enclose (a : Approximation K) (p : DensePoly K) (δ : Rat) : Bounds :=
  let x := a.constant δ
  p.coeffs.foldr (fun c acc => (a.coeff c δ).add (x.mul acc)) (.singleton 0)

/-- The empty coefficient array encloses exact zero without provider hypotheses. -/
private theorem enclose_empty (a : Approximation K) (p : DensePoly K) (δ : Rat)
    (h : p.coeffs = #[]) : enclose a p δ = .singleton 0 := by
  simp [enclose, h]

/-- A single coefficient needs no extension-constant enclosure. -/
private theorem enclose_singleton (a : Approximation K) (p : DensePoly K) (δ : Rat)
    (c : K) (h : p.coeffs = #[c]) : enclose a p δ = a.coeff c δ := by
  apply Bounds.ext <;>
    simp [enclose, h, Bounds.mul, Bounds.hull4, Bounds.singleton, Bounds.add, min, max, Rat.add_zero]

/-- Constant enclosures preserve the coefficient provider, except that the
canonical zero polynomial has its exact zero enclosure. -/
@[simp] theorem enclose_C (a : Approximation K) (c : K) (δ : Rat) :
    enclose a (DensePoly.C c) δ = if c = 0 then .singleton 0 else a.coeff c δ := by
  split
  · rename_i hc
    subst c
    exact enclose_empty a _ δ DensePoly.coeffs_C_zero
  · rename_i hc
    exact enclose_singleton a _ δ c (DensePoly.coeffs_C_of_ne_zero hc)

/-- Skip zero and singleton Horner initializations; larger arrays retain the
reference fold and joint coefficient/argument precision. -/
def encloseImpl (a : Approximation K) (p : DensePoly K) (δ : Rat) : Bounds :=
  if h : p.coeffs.size = 0 then .singleton 0
  else if h1 : p.coeffs.size = 1 then
    a.coeff p.coeffs[0] δ
  else
    let x := a.constant δ
    p.coeffs.foldr (fun c acc => (a.coeff c δ).add (x.mul acc)) (.singleton 0)

/-- The native constant fast path returns exactly the reference enclosure. -/
@[csimp] theorem enclose_eq_impl : @enclose = @encloseImpl := by
  funext K _ _ a p δ
  unfold encloseImpl
  split
  · rename_i h
    exact enclose_empty a p δ (Array.eq_empty_of_size_eq_zero h)
  · rename_i h
    split
    · rename_i h1
      obtain ⟨c, hc⟩ := Array.size_eq_one_iff.mp h1
      simpa [hc] using enclose_singleton a p δ c hc
    · rfl

/-- One total-sign trial. Formal zero does not invoke either provider. -/
def attempt (a : Approximation K) (f : RationalFn K) (n : Nat) : Option Int :=
  if f.num = 0 then some 0 else do
    let s ← (enclose a f.num (precision n)).sign?
    let t ← (enclose a f.den (precision n)).sign?
    pure (s * t)

/-- Total sign for one query, given an erased proof that its refinement terminates.
Semantic correctness additionally needs containment for these exact providers. -/
def sign (a : Approximation K) (f : RationalFn K)
    (h : Acc (Next (attempt a f)) 0) : Int := firstSome (attempt a f) 0 h

/-- One trial for a requested rational-function enclosure. -/
def approxAttempt (a : Approximation K) (f : RationalFn K) (δ : Rat) (n : Nat) :
    Option Bounds :=
  if f.num = 0 then
    if 0 ≤ δ then some (.singleton 0) else none
  else do
    let b ← (enclose a f.num (precision n)).div? (enclose a f.den (precision n))
    if b.width ≤ δ then some b else none

/-- Nonpositive requests ask for a coarse width-one enclosure. -/
def requestWidth (δ : Rat) : Rat := if 0 < δ then δ else 1

/-- Positive requests retain their original width. -/
@[simp] theorem requestWidth_of_pos {δ : Rat} (h : 0 < δ) : requestWidth δ = δ :=
  ite_eq_left h

/-- Nonpositive requests use width one instead. -/
@[simp] theorem requestWidth_of_nonpos {δ : Rat} (h : δ ≤ 0) : requestWidth δ = 1 := by
  have hn : ¬0 < δ := by have := h; grind
  exact ite_eq_right hn

/-- Every normalized request is strictly positive, so refinement can progress. -/
theorem requestWidth_pos (δ : Rat) : 0 < requestWidth δ := by
  unfold requestWidth
  split
  · assumption
  · decide +kernel

/-- Derived approximation for one query. Nonpositive requests run the same
refinement at width one, so every result still encloses the queried value. -/
def approx (a : Approximation K) (f : RationalFn K) (δ : Rat)
    (h : Acc (Next (approxAttempt a f (requestWidth δ))) 0) : Bounds :=
  firstSome (approxAttempt a f (requestWidth δ)) 0 h

/-- Finite evaluation requires a separated denominator even without transcendence.
An exact singleton numerator may certify zero; a zero-containing bound cannot. -/
def finiteAttempt (a : Approximation K) (f : RationalFn K) (n : Nat) : Option Int := do
  let t ← (enclose a f.den (precision n)).sign?
  let s ← (enclose a f.num (precision n)).exactSign?
  pure (s * t)

/-- Optional finite evaluation. Fuel counts trials, beginning at precision zero;
this function is never a coefficient field operation. -/
def sign? (a : Approximation K) (f : RationalFn K) (fuel : Nat) : Option Int :=
  go fuel 0
where
  /-- Try consecutive precisions until the fuel is exhausted or a trial succeeds. -/
  go : Nat → Nat → Option Int
    | 0, _ => none
    | fuel + 1, n =>
      match finiteAttempt a f n with
      | some s => some s
      | none => go fuel (n + 1)

/-- Formal zero succeeds at every precision without querying the provider. -/
theorem attempt_zero (a : Approximation K) (n : Nat) : attempt a 0 n = some 0 := by
  simp [attempt, show (0 : RationalFn K).num = 0 from rfl]

/-- A total sign search returns zero for the zero fraction. -/
theorem sign_zero (a : Approximation K) (h : Acc (Next (attempt a 0)) 0) :
    sign a 0 h = 0 := firstSome_some _ _ _ (attempt_zero a 0)

/-- Every successful approximation trial meets its supplied width bound. -/
theorem approxAttempt_width (a : Approximation K) (f : RationalFn K)
    (δ : Rat) (n : Nat) {b : Bounds} (hb : approxAttempt a f δ n = some b) :
    b.width ≤ δ := by
  unfold approxAttempt at hb
  split at hb
  · split at hb
    · cases hb
      simpa using ‹0 ≤ δ›
    · contradiction
  · cases hd : (enclose a f.num (precision n)).div? (enclose a f.den (precision n)) with
    | none => simp [hd] at hb
    | some c =>
      simp [hd] at hb
      exact hb.2 ▸ hb.1

/-- Width is a rational property of the actual search, separate from containment. -/
theorem approx_width_le (a : Approximation K) (f : RationalFn K) (δ : Rat)
    (h : Acc (Next (approxAttempt a f (requestWidth δ))) 0) :
    (approx a f δ h).width ≤ requestWidth δ := by
  obtain ⟨n, _, hn⟩ := firstSome_spec (approxAttempt a f (requestWidth δ)) 0 h
  exact approxAttempt_width a f (requestWidth δ) n hn

/-- Positive requests retain their specified width. -/
theorem approx_width (a : Approximation K) (f : RationalFn K) (δ : Rat)
    (h : Acc (Next (approxAttempt a f (requestWidth δ))) 0) (hδ : 0 < δ) :
    (approx a f δ h).width ≤ δ := by
  calc
    (approx a f δ h).width ≤ requestWidth δ := approx_width_le a f δ h
    _ = δ := requestWidth_of_pos hδ

end Hex.OrderedFn.Real
