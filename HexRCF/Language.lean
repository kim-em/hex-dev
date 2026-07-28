/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Syntax
public import HexRealRootsMathlib.Separation

public section

/-!
# Reflected univariate real-closed-field sentences

This module defines the real-valued semantics of the Mathlib-free object
language in `HexRCF.Syntax`.

Nested quantifiers and additional variables are unrepresentable by
construction. Rational coefficients are handled by the tactic's reifier,
which clears denominators before constructing an `Atom`.

Reification relates atom evaluation and dyadic endpoints propositionally
using the `aeval` and `Dyadic.toReal` lemmas. Normalisation and
denominator clearing are not expected to make the reflected semantics
definitionally equal to the source goal.
-/

namespace Hex.RCF

/-- Interpret a reflected comparison between two real numbers. -/
@[expose]
def Cmp.toProp : Cmp → ℝ → ℝ → Prop
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .eq, a, b => a = b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b
  | .ne, a, b => a ≠ b

/-- Interpret an atomic polynomial comparison at a real point. -/
@[expose]
def Atom.toProp (a : Atom) (x : ℝ) : Prop :=
  a.cmp.toProp (Polynomial.aeval x (HexPolyZMathlib.toPolynomial a.p)) 0

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
