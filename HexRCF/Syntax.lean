/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Basic

public section

/-!
# Reflected syntax for univariate real-closed-field sentences

This module contains the Mathlib-free data consumed by the compiled `rcf`
decision pipeline. A formula is a Boolean combination of comparisons between
an integer polynomial and zero. A sentence places exactly one universal or
existential quantifier around a formula, either over the whole domain or over
a half-open interval with dyadic endpoints.

Real-valued semantics live separately in `HexRCF.Language`. Keeping the
syntax and its structural polynomial traversals here allows compiled consumers
to depend on the reflected input without importing those semantics.
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

/-- An atomic comparison between an integer polynomial and zero. -/
structure Atom where
  /-- The integer polynomial on the left of the comparison. -/
  p : ZPoly
  /-- The comparison with zero. -/
  cmp : Cmp
  deriving DecidableEq

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

/-- A quantifier-free formula under exactly one real or bounded-real
quantifier. Bounded quantifiers use the half-open convention `(a, b]` inherited
from real-root isolations. -/
inductive Sentence where
  /-- Universal quantification over the whole domain. -/
  | forallReal (φ : Formula)
  /-- Existential quantification over the whole domain. -/
  | existsReal (φ : Formula)
  /-- Universal quantification over the half-open dyadic interval `(a, b]`. -/
  | forallIoc (a b : Dyadic) (φ : Formula)
  /-- Existential quantification over the half-open dyadic interval `(a, b]`. -/
  | existsIoc (a b : Dyadic) (φ : Formula)
  deriving DecidableEq

/-- All atom polynomials in a formula, in deterministic left-to-right order. -/
@[expose]
def Formula.polys : Formula → List ZPoly
  | .atom a => [a.p]
  | .tt | .ff => []
  | .not φ => φ.polys
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.polys ++ ψ.polys

/-- The body of a one-quantifier sentence. -/
@[expose]
def Sentence.formula : Sentence → Formula
  | .forallReal φ | .existsReal φ | .forallIoc _ _ φ | .existsIoc _ _ φ => φ

/-- The positive-degree atom polynomials used by the carrier decomposition.
Constant atoms remain in the reflected formula but, after their truth values
are evaluated, do not contribute carrier boundaries. -/
@[expose]
def Sentence.polys (s : Sentence) : List ZPoly :=
  s.formula.polys.filter fun p => decide (0 < p.degree?.getD 0)

/-- The product of all nonconstant atom polynomials. -/
@[expose]
def Sentence.product (s : Sentence) : ZPoly := s.polys.prod

end Hex.RCF
