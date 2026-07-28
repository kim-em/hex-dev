/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Separation
public import HexRCF.SturmBuilder
public meta import HexRCF.Separation
public meta import HexRCF.SturmBuilder
public meta import HexRCF.Isolations
public meta import HexRCF.SturmReplay
public meta import HexRealRoots.Basic
public meta import HexRealRoots.Chain
public meta import HexRealRoots.Var
public meta import HexRealRoots.Prec
public meta import HexPolyZ.Mignotte
import all HexRCF.Separation
import all HexRCF.SeparationCheck
import all HexRCF.SturmBuilder
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

public section

/-! Regression tests for strict separation and exact endpoint comparison. -/

namespace Hex.RCF.SeparationTests

open HexRealRootsMathlib

private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]

private def replay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def left : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 0) (by decide)

private def right : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide)

private def touching : IsolationCert := ⟨#[left, right]⟩

/-- A touching pair is a valid generalized isolation, but not yet strict. -/
example : touching.check replay = true := by decide
example : touching.checkStrict replay = false := by decide

/-- Midpoint roots belong to the left half of each bisection. -/
example : (match Separation.refinePairWith? replay 8 left right with
  | some (a, b) =>
      a.lower == Dyadic.ofInt (-2) &&
      a.upper == Dyadic.ofInt (-1) &&
      b.lower == Dyadic.ofInt 0 &&
      b.upper == Dyadic.ofInt 1
  | none => false) = true := by decide

/- The production wrapper computes its own separation fuel and traverses the
touching branch.  This is a compiled guard because `sepPrec` intentionally
contains opaque square-root helpers across the module boundary. -/
#guard
  match Separation.separate? quad replay touching with
  | some out => out.checkStrict replay
  | none => false

private def negHalf : Dyadic := Dyadic.ofInt (-1) >>> (1 : Int)
private def half : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)

private def strict : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) negHalf (by decide),
  DyadicInterval.mk half (Dyadic.ofInt 2) (by decide)]⟩

/-- An already-strict pair is returned endpoint-for-endpoint unchanged. -/
example : (match Separation.separate? quad replay strict with
  | some out => match out.intervals.toList, strict.intervals.toList with
      | [a, b], [a', b'] =>
          a.lower == a'.lower && a.upper == a'.upper &&
          b.lower == b'.lower && b.upper == b'.upper
      | _, _ => false
  | none => false) = true := by decide

/-- The raw list walk handles empty and singleton inputs without refinement. -/
example : (match Separation.separateList? quad replay [] with
  | some [] => true
  | _ => false) = true := by decide
example : (match Separation.separateList? quad replay [left] with
  | some [out] => out.lower == left.lower && out.upper == left.upper
  | _ => false) = true := by decide

/-- Genuine overlap is rejected before refinement. -/
private def overlapping : DyadicInterval :=
  DyadicInterval.mk negHalf (Dyadic.ofInt 2) (by decide)

example : (match Separation.refinePairWith? replay 8 left overlapping with
  | none => true
  | some _ => false) = true := by decide

#guard
  match Separation.separate? quad replay ⟨#[left, overlapping]⟩ with
  | none => true
  | some _ => false

/-- A touching interval with no count-one child is rejected. -/
private def outside : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt 0) half (by decide)

example : (match Separation.refinePairWith? replay 8 left outside with
  | none => true
  | some _ => false) = true := by decide

/-- Several bisections separate the close roots of `64x² - 1`. -/
private def close : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 64]

private def unitLeft : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 0) (by decide)

private def unitRight : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 1) (by decide)

example : (match buildSturmReplay? close with
  | some closeReplay =>
      match Separation.refinePairWith? closeReplay 12 unitLeft unitRight with
      | some (a, b) =>
          a.lower == (Dyadic.ofInt (-1) >>> (2 : Int)) &&
          a.upper == (Dyadic.ofInt (-1) >>> (3 : Int)) &&
          b.lower == Dyadic.ofInt 0 &&
          b.upper == (Dyadic.ofInt 1 >>> (3 : Int)) &&
          IsolationCert.checkStrict closeReplay ⟨#[a, b]⟩
      | none => false
  | none => false) = true := by decide

/-- Refining a middle interval against its successor preserves the strict gap
created against its predecessor. -/
private def cubic : ZPoly := DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]

private def cubicIntervals : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt (-1)) (by decide),
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 0) (by decide),
  DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide)]⟩

example : (match buildSturmReplay? cubic with
  | some cubicReplay =>
      match cubicIntervals.intervals.toList with
      | [a, b, c] =>
        match Separation.refinePairWith? cubicReplay 12 a b with
        | some (a', b') =>
          match Separation.refinePairWith? cubicReplay 12 b' c with
          | some (b'', c') => IsolationCert.checkStrict cubicReplay ⟨#[a', b'', c']⟩
          | none => false
        | none => false
      | _ => false
  | none => false) = true := by decide

/- The production scan refines a middle interval a second time without
destroying the gap established against its predecessor. -/
#guard
  match buildSturmReplay? cubic with
  | some cubicReplay =>
      match Separation.separate? cubic cubicReplay cubicIntervals with
      | some out => out.checkStrict cubicReplay
      | none => false
  | none => false

/-! Endpoint classification, including the half-open boundary cases. -/

example : Separation.classify? quad replay left (Dyadic.ofInt (-2)) =
    some .gt := by decide
example : Separation.classify? quad replay left
    (Dyadic.ofInt (-3) >>> (1 : Int)) = some .gt := by decide
example : Separation.classify? quad replay left (Dyadic.ofInt (-1)) =
    some .eq := by decide
example : Separation.classify? quad replay left negHalf = some .lt := by decide
example : Separation.classify? quad replay left (Dyadic.ofInt 1) =
    some .lt := by decide

example : Separation.classify? quad replay right (Dyadic.ofInt 0) =
    some .gt := by decide
example : Separation.classify? quad replay right (Dyadic.ofInt 1) =
    some .eq := by decide
example : Separation.classify? quad replay right (Dyadic.ofInt 3) =
    some .lt := by decide

/-- Equality at the included upper endpoint takes the interior count-one and
exact-evaluation branch. -/
private def leftAtRoot : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt (-1)) (by decide)

example : Separation.classify? quad replay leftAtRoot (Dyadic.ofInt (-1)) =
    some .eq := by decide

/-- Invalid intervals may expose the defensive `none` branch. -/
private def wide : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide)

example : Separation.classify? quad replay wide (Dyadic.ofInt 2) = none := by
  decide

example : IsolationCert.checkGaps ⟨#[]⟩ = true := by decide
example : IsolationCert.checkGaps ⟨#[left]⟩ = true := by decide

/-- A root at the shared endpoint belongs only to the left half-open
isolation, and the production pass separates the pair in one round. -/
private def sharedRoot : IsolationCert := ⟨#[leftAtRoot,
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 2) (by decide)]⟩

example : sharedRoot.check replay = true := by decide

#guard
  match Separation.separate? quad replay sharedRoot with
  | some out => out.checkStrict replay
  | none => false

example : Separation.checkCmp quad replay left (Dyadic.ofInt (-1)) .eq = true := by
  decide
example : Separation.checkCmp quad replay left (Dyadic.ofInt (-1)) .lt = false := by
  decide

/-- Checked endpoint claims expose their semantic order in the kernel. -/
example : ∃! root : ℝ, (HexRealRootsMathlib.toPolyℝ quad).IsRoot root ∧
    HexRealRootsMathlib.Literal.InInterval touching.intervals[0] root ∧
    Separation.RootCmp.eq.Holds root (Dyadic.toReal (Dyadic.ofInt (-1))) :=
  Separation.checkCmp_sound (f := quad) (replay := replay) (cert := touching)
    (by decide) (by decide) ⟨0, by decide⟩ (Dyadic.ofInt (-1)) .eq (by decide)

end Hex.RCF.SeparationTests
