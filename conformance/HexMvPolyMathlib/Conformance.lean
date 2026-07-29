/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPolyMathlib

/-!
Deterministic randomized cross-checks between `Hex.MvPoly` and Mathlib's
`MvPolynomial`.

The generator deliberately includes duplicate monomials, zero coefficients,
and mixed signs. Each seeded case constructs the two representations
independently from the same term streams, then compares arithmetic,
evaluation, differentiation, homogeneous projection, and renaming under lex,
grlex, and grevlex storage orders.
-/

namespace HexMvPolyMathlib.Conformance

open scoped HexMvPolyMathlib

open Hex
open Hex.MvPoly

private def word (seed i : Nat) : Nat :=
  (1664525 * (seed + 1013904223) + 22695477 * (i + 1)) % 4294967291

private def randomMono (seed i : Nat) : Mono 3 :=
  let source := if i % 5 = 0 then 0 else i
  Hex.Vector.ofFn' fun j => word (seed + 17 * source) j.val % 6

private def randomCoeff (seed i : Nat) : Int :=
  (Int.ofNat (word (seed + 31) i % 13)) - 6

private def randomTerms (seed count : Nat) : List (Mono 3 × Int) :=
  (List.range count).map fun i =>
    (randomMono seed i, randomCoeff seed i)

private noncomputable def mathOfTerms
    (terms : List (Mono 3 × Int)) : MvPolynomial (Fin 3) Int :=
  terms.foldl
    (fun p term =>
      p + MvPolynomial.monomial (monoEquiv term.1) term.2)
    0

private def hexLeft
    (cmp : Mono 3 → Mono 3 → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (seed : Nat) : MvPoly 3 Int cmp :=
  ofTerms (randomTerms (7 * seed + 3) 9)

private def hexRight
    (cmp : Mono 3 → Mono 3 → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (seed : Nat) : MvPoly 3 Int cmp :=
  ofTerms (randomTerms (11 * seed + 5) 8)

private noncomputable def mathLeft (seed : Nat) :
    MvPolynomial (Fin 3) Int :=
  mathOfTerms (randomTerms (7 * seed + 3) 9)

private noncomputable def mathRight (seed : Nat) :
    MvPolynomial (Fin 3) Int :=
  mathOfTerms (randomTerms (11 * seed + 5) 8)

private def point : Fin 3 → Int := fun i => #[2, -1, 3][i]

private def renameTarget : Fin 3 → Fin 2 := fun i =>
  if i = 1 then 1 else 0

private noncomputable def Agrees
    (cmp : Mono 3 → Mono 3 → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (seed : Nat) : Prop :=
  let p := hexLeft cmp seed
  let q := hexRight cmp seed
  let pMath := mathLeft seed
  let qMath := mathRight seed
  toMvPolynomial p = pMath ∧
  toMvPolynomial q = qMath ∧
  toMvPolynomial (p + q) = pMath + qMath ∧
  toMvPolynomial (p * q) = pMath * qMath ∧
  toMvPolynomial (p - q) = pMath - qMath ∧
  toMvPolynomial (p ^ 3) = pMath ^ 3 ∧
  eval point p = MvPolynomial.aeval point pMath ∧
  toMvPolynomial (derivative 1 p) = MvPolynomial.pderiv 1 pMath ∧
  toMvPolynomial (homogeneousComponent 5 p) =
    MvPolynomial.homogeneousComponent 5 pMath ∧
  toMvPolynomial (rename (cmp := cmp) Mono.grevlex renameTarget p) =
    MvPolynomial.rename renameTarget pMath

private theorem checkCase
    (cmp : Mono 3 → Mono 3 → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (seed : Nat) : Agrees cmp seed := by
  let p := hexLeft cmp seed
  let q := hexRight cmp seed
  let pMath := mathLeft seed
  let qMath := mathRight seed
  have hp : toMvPolynomial p = pMath := by
    simpa [p, pMath, hexLeft, mathLeft, mathOfTerms] using
      (toMvPolynomial_ofTerms (cmp := cmp)
        (randomTerms (7 * seed + 3) 9))
  have hq : toMvPolynomial q = qMath := by
    simpa [q, qMath, hexRight, mathRight, mathOfTerms] using
      (toMvPolynomial_ofTerms (cmp := cmp)
        (randomTerms (11 * seed + 5) 8))
  unfold Agrees
  change
    toMvPolynomial p = pMath ∧
    toMvPolynomial q = qMath ∧
    toMvPolynomial (p + q) = pMath + qMath ∧
    toMvPolynomial (p * q) = pMath * qMath ∧
    toMvPolynomial (p - q) = pMath - qMath ∧
    toMvPolynomial (p ^ 3) = pMath ^ 3 ∧
    eval point p = MvPolynomial.aeval point pMath ∧
    toMvPolynomial (derivative 1 p) = MvPolynomial.pderiv 1 pMath ∧
    toMvPolynomial (homogeneousComponent 5 p) =
      MvPolynomial.homogeneousComponent 5 pMath ∧
    toMvPolynomial (rename (cmp := cmp) Mono.grevlex renameTarget p) =
      MvPolynomial.rename renameTarget pMath
  refine ⟨hp, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toMvPolynomial_add, hp, hq]
  · rw [toMvPolynomial_mul, hp, hq]
  · rw [toMvPolynomial_sub, hp, hq]
  · rw [toMvPolynomial_pow, hp]
  · rw [← aeval_eq_eval, aeval_apply, hp]
  · rw [toMvPolynomial_derivative, hp]
  · rw [toMvPolynomial_homogeneousComponent, hp]
  · rw [toMvPolynomial_rename, hp]

private theorem checkSeeds
    (cmp : Mono 3 → Mono 3 → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    (List.range 24).Forall (Agrees cmp) := by
  rw [List.forall_iff_forall_mem]
  intro seed _
  exact checkCase cmp seed

private theorem lex_agrees : (List.range 24).Forall (Agrees Mono.lex) :=
  checkSeeds Mono.lex

private theorem grlex_agrees : (List.range 24).Forall (Agrees Mono.grlex) :=
  checkSeeds Mono.grlex

private theorem grevlex_agrees :
    (List.range 24).Forall (Agrees Mono.grevlex) :=
  checkSeeds Mono.grevlex

end HexMvPolyMathlib.Conformance
