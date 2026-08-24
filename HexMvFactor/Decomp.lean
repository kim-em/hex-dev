/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Squarefree

@[expose] public section
set_option backward.proofsInPublic true

/-!
Checked product decompositions for multivariate integer polynomials.

This layer deliberately says nothing about irreducibility.  Its checker
replays the product identity and the canonical-form side conditions which
make multiplicities meaningful.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- One nonconstant entry in a product decomposition. -/
structure Factor (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  /-- Primitive normalized nonconstant polynomial. -/
  factor : MvPoly n Int cmp
  /-- Positive exponent of the factor in the decomposition. -/
  multiplicity : Nat

/-- An integer scalar and a list of polynomial powers. -/
structure Decomp (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  /-- Integer scalar separated from the polynomial factors. -/
  content : Int
  /-- Pairwise-distinct polynomial factors with their multiplicities. -/
  factors : List (Factor n cmp)

namespace Decomp

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Reconstruct the polynomial represented by a decomposition. -/
@[reducible] def product (D : Decomp n cmp) : MvPoly n Int cmp :=
  D.factors.foldl
    (fun acc entry => acc * entry.factor ^ entry.multiplicity)
    (C D.content)

end Decomp

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]

/-- The local canonical-form conditions for one decomposition entry. -/
@[reducible] def checkFactor (entry : Factor n cmp) : Bool :=
  decide (0 < entry.multiplicity) &&
    decide (entry.factor.vars ≠ []) &&
    (polyNormalize entry.factor == entry.factor) &&
    decide (MvPoly.content entry.factor = 1)

/-- Boolean pairwise distinctness, kept structural for kernel replay. -/
@[reducible] def distinctFactors : List (Factor n cmp) → Bool
  | [] => true
  | entry :: entries =>
      entries.all (fun other => decide (entry.factor ≠ other.factor)) &&
        distinctFactors entries

/-- Replay all five decomposition conditions from the SPEC. -/
@[reducible] def checkDecomp (f : MvPoly n Int cmp)
    (D : Decomp n cmp) : Bool :=
  (D.product == f) &&
    D.factors.all checkFactor &&
    distinctFactors D.factors

/-- The semantic product and nonconstant-positive-multiplicity payload of a
checked decomposition.  Normalization and distinctness are checker-side
canonicity conditions rather than part of this minimal witness. -/
def IsDecompOf (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop :=
  D.product = f ∧
    ∀ entry ∈ D.factors,
      0 < entry.multiplicity ∧ ¬ MvPoly.IsConst entry.factor

/-- Accepted decomposition data tied to the subject checked by its caller. -/
structure CheckedDecomp (f : MvPoly n Int cmp) where
  /-- Raw decomposition data accepted by the checker. -/
  raw : Decomp n cmp
  /-- Evidence that replay accepts the decomposition for `f`. -/
  valid : checkDecomp f raw = true

/-- Executable replay implies the semantic decomposition payload. -/
theorem checkDecomp_sound {f : MvPoly n Int cmp} {D : Decomp n cmp}
    (h : checkDecomp f D = true) : IsDecompOf f D := by
  simp only [checkDecomp, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  refine ⟨h.1.1, ?_⟩
  intro entry hentry
  have hfactor := h.1.2 entry hentry
  simp only [decide_eq_true_eq] at hfactor
  exact ⟨hfactor.1.1.1, hfactor.1.1.2⟩

/-! # Structural answers

These are the complete no-search cases used before the EEZ driver: zero,
constants, and a single monomial.  A general polynomial with scalar or
monomial content still needs a residual factorization and is handled by the
driver rather than hidden behind a partial division here.
-/

/-- The variable factors of a monomial, in increasing variable order. -/
def monomialFactors (m : Mono n) : List (Factor n cmp) :=
  (List.finRange n).filterMap fun i =>
    let exponent := Mono.degreeOf i m
    if exponent = 0 then none else some ⟨X i, exponent⟩

/-- Canonical decomposition of one coefficient-monomial pair. -/
def monomialDecomp (coefficient : Int) (m : Mono n) : Decomp n cmp :=
  ⟨coefficient, monomialFactors m⟩

/-- Recognize the no-search structural cases. -/
def structural? (f : MvPoly n Int cmp) : Option (Decomp n cmp) :=
  match f.termsList with
  | [] => some ⟨0, []⟩
  | [(m, coefficient)] => some (monomialDecomp coefficient m)
  | _ => none

/-- Every structural answer passes the decomposition checker. -/
theorem structural_checks {f : MvPoly n Int cmp} {D : Decomp n cmp}
    (h : structural? f = some D) : checkDecomp f D = true := by
  sorry

end Hex.MvFactor
