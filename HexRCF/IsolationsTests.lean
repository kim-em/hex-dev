/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Isolations
public import HexRCF.SturmBuilder
import all HexRCF.Isolations
import all HexRCF.SturmBuilder

public section

/-! Regression tests for raw generalized literal isolation certificates. -/

namespace Hex.RCF.IsolationsTests

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

private def wide : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide)

private def outside : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt 2) (Dyadic.ofInt 3) (by decide)

private def overlap : DyadicInterval :=
  DyadicInterval.mk ((Dyadic.ofInt (-1)) >>> (1 : Int))
    (Dyadic.ofInt 2) (by decide)

private def valid : IsolationCert := ⟨#[left, right]⟩
private def wrongCount : IsolationCert := ⟨#[left, outside]⟩
private def doubleCount : IsolationCert := ⟨#[wide, right]⟩
private def wrongOrder : IsolationCert := ⟨#[left, overlap]⟩
private def incomplete : IsolationCert := ⟨#[left]⟩
private def duplicate : IsolationCert := ⟨#[left, left]⟩
private def reversed : IsolationCert := ⟨#[right, left]⟩
private def empty : IsolationCert := ⟨#[]⟩

/-- Touching endpoints are valid for ordered half-open isolations. -/
example : valid.check replay = true := by decide
example : wrongCount.check replay = false := by decide
example : doubleCount.check replay = false := by decide
example : wrongOrder.check replay = false := by decide
example : incomplete.check replay = false := by decide
example : duplicate.check replay = false := by decide
example : reversed.check replay = false := by decide
example : empty.check replay = false := by decide

example : ∃! r : ℝ, (HexRealRootsMathlib.toPolyℝ quad).IsRoot r ∧
    HexRealRootsMathlib.Literal.InInterval (valid.intervals[0]'(by decide)) r :=
  IsolationCert.existsUnique_root
    (f := quad) (replay := replay) (cert := valid) (by decide) (by decide)
      ⟨0, by decide⟩

example : ∀ r : ℝ, (HexRealRootsMathlib.toPolyℝ quad).IsRoot r →
    ∃! i : Fin valid.intervals.size,
      HexRealRootsMathlib.Literal.InInterval valid.intervals[i] r :=
  IsolationCert.isolates_of_check (f := quad) (replay := replay) (cert := valid)
    (by decide) (by decide)

/-- An empty isolation array is valid for a squarefree polynomial with no real
roots, while replay validity remains an independent outer obligation. -/
private def noRoots : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 0, 1]

example : (buildSturmReplay? noRoots).map
    (fun r => r.check noRoots && empty.check r) = some true := by
  decide

example : replay.check noRoots = false := by decide

end Hex.RCF.IsolationsTests
