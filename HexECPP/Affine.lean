/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Data

public section

/-!
# Affine arithmetic over a candidate modulus

Every division in this partial addition is justified by the next supplied
inverse witness. The checker never computes an inverse. Coordinates returned
by a successful finite addition are reduced modulo the candidate.
-/

namespace Hex.ECPP

/-- A point used by the certificate replay. -/
inductive Point where
  | infinity
  | affine (x y : Nat)
deriving Repr, BEq, DecidableEq

/-- Natural subtraction interpreted modulo `n`, for canonical operands. -/
@[expose]
def modSub (n a b : Nat) : Nat := (a % n + n - b % n) % n

/-- The equation of the short Weierstrass curve. -/
@[expose]
def onCurve (n a b x y : Nat) : Bool :=
  (y * y) % n == (x * x * x + a * x + b) % n

/-- A canonical point has both coordinates below the modulus. -/
@[expose]
def Point.canonical (n : Nat) : Point → Bool
  | .infinity => true
  | .affine x y => x < n && y < n

/-- Infinity belongs to every short curve; finite points satisfy its equation. -/
@[expose]
def Point.onCurve (n a b : Nat) : Point → Bool
  | .infinity => true
  | .affine x y => Hex.ECPP.onCurve n a b x y

/-- Complete one division branch, consuming exactly one inverse witness. -/
@[expose]
def addWithInverse (n x₁ y₁ x₂ d v : Nat)
    (inverses : List Nat) : Option (Point × List Nat) := do
  let u :: rest := inverses | none
  if !(u < n && d * u % n == 1) then none
  else
    let slope := v * u % n
    let x₃ := modSub n (modSub n (slope * slope % n) x₁) x₂
    let y₃ := modSub n (slope * (modSub n x₁ x₃) % n) y₁
    some (.affine x₃ y₃, rest)

/-- Partial affine addition with explicit inverse witnesses. -/
@[expose]
def add? (n a : Nat) (P Q : Point) (inverses : List Nat) :
    Option (Point × List Nat) :=
  match P, Q with
  | .infinity, Q => some (Q, inverses)
  | P, .infinity => some (P, inverses)
  | .affine x₁ y₁, .affine x₂ y₂ =>
    if x₁ == x₂ then
      if (y₁ + y₂) % n == 0 then some (.infinity, inverses)
      else if y₁ == y₂ then
        addWithInverse n x₁ y₁ x₂ (2 * y₁ % n)
          ((3 * x₁ * x₁ + a) % n) inverses
      else none
    else
      addWithInverse n x₁ y₁ x₂ (modSub n x₂ x₁)
        (modSub n y₂ y₁) inverses

/-- Replay accepts only canonical points on the supplied curve after each
addition. This makes both arithmetic invariants local, executable checks. -/
@[expose]
def checkedAdd? (n a b : Nat) (P Q : Point) (inverses : List Nat) :
    Option (Point × List Nat) := do
  let (R, rest) ← add? n a P Q inverses
  if R.canonical n && R.onCurve n a b then some (R, rest) else none

/-- Accepted checked additions satisfy the raw branch and both local arithmetic invariants. -/
theorem checkedAdd_facts {n a b : Nat} {P Q R : Point}
    {ws rest : List Nat}
    (h : checkedAdd? n a b P Q ws = some (R, rest)) :
    add? n a P Q ws = some (R, rest) ∧
      R.canonical n = true ∧ R.onCurve n a b = true := by
  unfold checkedAdd? at h
  cases hadd : add? n a P Q ws with
  | none => simp [hadd] at h
  | some pair =>
      rcases pair with ⟨S, tail⟩
      simp [hadd] at h
      rcases h with ⟨⟨hcan, hcurve⟩, rfl, rfl⟩
      exact ⟨rfl, hcan, hcurve⟩

/-- Modular subtraction returns a canonical residue for a positive modulus. -/
theorem modSub_lt {n a b : Nat} (hn : 0 < n) : modSub n a b < n := by
  exact Nat.mod_lt _ hn

/-- A successful division branch returns canonical coordinates. -/
theorem addWithInverse_canonical {n x₁ y₁ x₂ d v : Nat}
    {ws rest : List Nat} {R : Point} (hn : 0 < n)
    (h : addWithInverse n x₁ y₁ x₂ d v ws = some (R, rest)) :
    R.canonical n = true := by
  unfold addWithInverse at h
  cases ws with
  | nil => simp at h
  | cons u tail =>
    simp only at h
    split at h
    · simp at h
    · cases h
      simp [Point.canonical, modSub_lt hn]

/-- A successful division branch used exactly the next checked witness. -/
theorem addWithInverse_spec {n x₁ y₁ x₂ d v : Nat}
    {ws rest : List Nat} {R : Point}
    (h : addWithInverse n x₁ y₁ x₂ d v ws = some (R, rest)) :
    ∃ u, ws = u :: rest ∧ u < n ∧ d * u % n = 1 ∧
      R = .affine
        (modSub n (modSub n ((v * u % n) * (v * u % n) % n) x₁) x₂)
        (modSub n ((v * u % n) *
          (modSub n x₁ (modSub n (modSub n ((v * u % n) * (v * u % n) % n) x₁) x₂)) % n) y₁) := by
  cases ws with
  | nil => simp [addWithInverse] at h
  | cons u tail =>
    by_cases hu : u < n ∧ d * u % n = 1
    · have hbool : (u < n && d * u % n == 1) = true := by
        simp [hu.1, hu.2]
      simp only [addWithInverse, hbool, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨u, rfl, hu.1, hu.2, rfl⟩
    · have hbool : (u < n && d * u % n == 1) = false := by
        apply Bool.eq_false_of_ne_true
        intro htrue
        simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at htrue
        exact hu htrue
      simp [addWithInverse, hbool] at h

end Hex.ECPP
