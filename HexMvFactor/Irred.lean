/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvFactor.Kronecker
public import HexMvHensel.Complete

@[expose] public section
set_option backward.proofsInPublic true

/-!
Irreducibility certificate replay independent of the factor search.

The four constructors reduce multivariate irreducibility either to a
primitive degree-one argument, to an explicitly reported univariate
obligation, or to a certificate one arity lower.  The Kronecker constructor
checks a carried univariate factorization and exhaustively refutes every
proper exponent-vector product by exact division.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- Replay a primitive-content certificate against the coefficients in one
named-variable view. -/
@[reducible] def checkPrimitive {n : Nat}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (g : MvPoly (n + 1) Int cmp)
    (prim : ContentCert n Int cmp') : Bool :=
  checkContent (toUnivariate i cmp' g).toArray.toList prim &&
    decide (prim.value = 1)

/-- Replay an irreducibility certificate.  Successful `image` certificates
leave the primitive univariate image as an explicit obligation. -/
@[reducible] def checkIrred : {n : Nat} →
    {cmp : Mono n → Mono n → Ordering} →
    [IsMonomialOrder cmp] → MvPoly n Int cmp → IrredCert n cmp → Bool
  | _, _, _, g,
      @IrredCert.degreeOne _ _ _ _ i cmp' order prim =>
      letI : IsMonomialOrder cmp' := order
      decide (MvPoly.degreeOf i g = 1) &&
        checkPrimitive i cmp' g prim
  | _, _, _, g,
      @IrredCert.image _ _ _ _ i cmp' order point prim =>
      letI : IsMonomialOrder cmp' := order
      decide (0 < MvPoly.degreeOf i g) &&
        decide (MvPoly.eval point (MvHensel.lcIn i cmp' g) ≠ 0) &&
        checkPrimitive i cmp' g prim
  | _, _, _, g,
      @IrredCert.embed _ _ _ _ i cmp' order sub cert =>
      letI : IsMonomialOrder cmp' := order
      (g == constIn i cmp' sub) && checkIrred sub cert
  | _, _, _, g, @IrredCert.kronecker _ _ _ _ scalar uni =>
      checkKronecker g scalar uni

/-- The univariate facts still trusted by a successful certificate replay. -/
@[reducible] def obligations {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (g : MvPoly n Int cmp) (cert : IrredCert n cmp) : List ZPoly :=
  match cert with
  | @IrredCert.degreeOne _ _ _ _ _ _ _ _ => []
  | @IrredCert.image _ _ _ _ i cmp' order point _ =>
      letI : IsMonomialOrder cmp' := order
      [ZPoly.primitivePart (MvHensel.imageAt i cmp' point g)]
  | @IrredCert.embed _ _ _ _ _ _ order sub cert =>
      @obligations _ _ order sub cert
  | @IrredCert.kronecker _ _ _ _ _ uni => uni.map Prod.fst

/-- Checked certificate replay, together with its declared univariate
obligations, implies Mathlib-free irreducibility. -/
theorem checkIrred_sound {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {g : MvPoly n Int cmp} {cert : IrredCert n cmp}
    (h : checkIrred g cert = true)
    (ho : ∀ F ∈ obligations g cert, MvHensel.Irred F) :
    MvHensel.Irred g := by
  sorry

/-! # Reducibility witnesses -/

/-- Replay a factorization and reject a unit on either side. -/
@[reducible] def checkSplit {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (g : MvPoly n Int cmp) (split : Split n cmp) : Bool :=
  checkSplitCore g split

/-- Semantic payload of a checked split. -/
def IsSplitOf {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (g : MvPoly n Int cmp) (split : Split n cmp) : Prop :=
  split.left * split.right = g ∧
    ¬ (∃ u, split.left * u = 1) ∧
    ¬ (∃ u, split.right * u = 1)

/-- Cheap split replay directly refutes irreducibility. -/
theorem checkSplit_sound {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {g : MvPoly n Int cmp} {split : Split n cmp}
    (h : checkSplit g split = true) : ¬ MvHensel.Irred g := by
  simp only [checkSplit, checkSplitCore, Bool.and_eq_true, beq_iff_eq] at h
  intro hirred
  rcases hirred.2 split.left split.right h.1.1.symm with hleft | hright
  · have hnot := h.1.2
    rw [(MvPoly.polyIsUnit_iff split.left).2 hleft] at hnot
    contradiction
  · have hnot := h.2
    rw [(MvPoly.polyIsUnit_iff split.right).2 hright] at hnot
    contradiction

/-! # Complete decompositions -/

@[reducible] def checkCerts {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp] :
    List (Factor n cmp) → List (IrredCert n cmp) → Bool
  | [], [] => true
  | entry :: entries, cert :: certs =>
      checkIrred entry.factor cert && checkCerts entries certs
  | _, _ => false

/-- Reject zero, replay the decomposition, and pair every factor with exactly
one irreducibility certificate. -/
@[reducible] def checkComplete {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f : MvPoly n Int cmp) (complete : Complete n cmp) : Bool :=
  decide (f ≠ 0) &&
    checkDecomp f complete.decomp &&
    decide (complete.certs.length = complete.decomp.factors.length) &&
    checkCerts complete.decomp.factors complete.certs

/-- Detect the expensive constructor through embedded certificates as well as
at the outermost arity. -/
@[reducible] def IrredCert.noKronecker : {n : Nat} →
    {cmp : Mono n → Mono n → Ordering} →
    [IsMonomialOrder cmp] → IrredCert n cmp → Bool
  | _, _, _, @IrredCert.degreeOne _ _ _ _ _ _ _ _ => true
  | _, _, _, @IrredCert.image _ _ _ _ _ _ _ _ _ => true
  | _, _, _, @IrredCert.embed lowerN _ _ _ _ lowerCmp lowerOrder _ cert =>
      @IrredCert.noKronecker lowerN lowerCmp lowerOrder cert
  | _, _, _, @IrredCert.kronecker _ _ _ _ _ _ => false

/-- True exactly when all certificates use only the cheap replay routes. -/
@[reducible] def NoKronecker {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (complete : Complete n cmp) : Bool :=
  complete.certs.all IrredCert.noKronecker

/-- A product decomposition into normalized, pairwise nonassociated
irreducible factors, up to the retained integer content. -/
def IsFactorizationOf {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop :=
  f ≠ 0 ∧
    IsDecompOf f D ∧
    (∀ entry ∈ D.factors, MvHensel.Irred entry.factor) ∧
    D.factors.Pairwise fun left right =>
      ∀ u : Int, u * u = 1 → left.factor ≠ right.factor * C u

/-- Accepted complete data tied to its checked subject. -/
structure CheckedComplete {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f : MvPoly n Int cmp) where
  raw : Complete n cmp
  valid : checkComplete f raw = true

/-- Complete checker replay plus the declared univariate obligations gives a
factorization into irreducibles. -/
theorem checkComplete_sound {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {f : MvPoly n Int cmp} {complete : Complete n cmp}
    (h : checkComplete f complete = true)
    (ho : ∀ pair ∈ complete.decomp.factors.zip complete.certs,
      ∀ F ∈ obligations pair.1.factor pair.2, MvHensel.Irred F) :
    IsFactorizationOf f complete.decomp := by
  sorry

/-! # Kronecker decision contracts -/

/-- On its intended primitive, nonconstant domain, an irreducible verdict
replays and reduces the conclusion to the carried univariate obligations. -/
theorem kronDecide_irreducible {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {g : MvPoly n Int cmp} {cert : IrredCert n cmp}
    (hprim : MvPoly.content g = 1) (hnonconst : ¬ MvPoly.IsConst g)
    (h : kronDecide g = .irreducible cert)
    (ho : ∀ F ∈ obligations g cert, MvHensel.Irred F) :
    MvHensel.Irred g := by
  sorry

/-- Reducible verdicts retain the exact divisor found by the sweep. -/
theorem kronDecide_reducible {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {g : MvPoly n Int cmp} {split : Split n cmp}
    (h : kronDecide g = .reducible split) : checkSplit g split = true := by
  exact kronDecide_split h

end Hex.MvFactor
