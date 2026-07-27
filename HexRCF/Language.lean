/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.Separation

public section

/-!
# Reflected univariate real-closed-field sentences

This module defines the object language consumed by the `rcf` decision
procedure. A formula is a Boolean combination of comparisons between an
integer polynomial evaluated at one real variable and zero. A sentence places
exactly one universal or existential quantifier around a formula, either over
all real numbers or over a half-open interval with dyadic endpoints.

Nested quantifiers and additional variables are unrepresentable by
construction. Rational coefficients are handled by the tactic's reifier,
which clears denominators before constructing an `Atom`.

Reification transports atom evaluation and dyadic endpoints propositionally,
through the `aeval` and `Dyadic.toReal` bridge lemmas. Normalisation and
denominator clearing are not expected to make the reflected semantics
definitionally equal to the source goal.
-/

namespace Hex.RCF

/-- The six comparisons supported by reflected polynomial atoms. -/
inductive Cmp where
  | lt
  | le
  | eq
  | ge
  | gt
  | ne
  deriving DecidableEq

/-- Interpret a reflected comparison between two real numbers. -/
@[expose]
def Cmp.toProp : Cmp → ℝ → ℝ → Prop
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .eq, a, b => a = b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b
  | .ne, a, b => a ≠ b

/-- An atomic predicate asserting that an integer polynomial at `x` compares
with zero according to `cmp`. -/
structure Atom where
  /-- The integer polynomial on the left of the comparison. -/
  p : ZPoly
  /-- The comparison with zero. -/
  cmp : Cmp
  deriving DecidableEq

/-- Interpret an atomic polynomial comparison at a real point. -/
@[expose]
def Atom.toProp (a : Atom) (x : ℝ) : Prop :=
  a.cmp.toProp (Polynomial.aeval x (HexPolyZMathlib.toPolynomial a.p)) 0

/-- Boolean combinations of univariate polynomial atoms. -/
inductive Formula where
  /-- A polynomial comparison. -/
  | atom (a : Atom)
  /-- Truth. -/
  | tt
  /-- Falsity. -/
  | ff
  /-- Boolean negation. -/
  | not (φ : Formula)
  /-- Boolean conjunction. -/
  | and (φ ψ : Formula)
  /-- Boolean disjunction. -/
  | or (φ ψ : Formula)
  /-- Boolean implication. -/
  | imp (φ ψ : Formula)
  deriving DecidableEq

/-- Interpret a reflected formula at a real point. -/
@[expose]
def Formula.toProp : Formula → ℝ → Prop
  | .atom a, x => a.toProp x
  | .tt, _ => True
  | .ff, _ => False
  | .not φ, x => ¬φ.toProp x
  | .and φ ψ, x => φ.toProp x ∧ ψ.toProp x
  | .or φ ψ, x => φ.toProp x ∨ ψ.toProp x
  | .imp φ ψ, x => φ.toProp x → ψ.toProp x

/-- A quantifier-free formula under exactly one real or bounded-real
quantifier. Bounded quantifiers use the half-open convention `(a, b]` inherited
from real-root isolations. -/
inductive Sentence where
  /-- Universal quantification over all real numbers. -/
  | forallReal (φ : Formula)
  /-- Existential quantification over all real numbers. -/
  | existsReal (φ : Formula)
  /-- Universal quantification over the half-open dyadic interval `(a, b]`. -/
  | forallIoc (a b : Dyadic) (φ : Formula)
  /-- Existential quantification over the half-open dyadic interval `(a, b]`. -/
  | existsIoc (a b : Dyadic) (φ : Formula)
  deriving DecidableEq

/-- Interpret a reflected sentence as a Lean proposition. -/
@[expose]
def Sentence.toProp : Sentence → Prop
  | .forallReal φ => ∀ x : ℝ, φ.toProp x
  | .existsReal φ => ∃ x : ℝ, φ.toProp x
  | .forallIoc a b φ =>
      ∀ x : ℝ, x ∈ Set.Ioc (HexRealRootsMathlib.Dyadic.toReal a)
        (HexRealRootsMathlib.Dyadic.toReal b) → φ.toProp x
  | .existsIoc a b φ =>
      ∃ x : ℝ, x ∈ Set.Ioc (HexRealRootsMathlib.Dyadic.toReal a)
        (HexRealRootsMathlib.Dyadic.toReal b) ∧ φ.toProp x

end Hex.RCF
