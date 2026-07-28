/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Cells

public section

/-! Regression tests for semantic cells and bounded-domain relevance. -/

namespace Hex.RCF.CellsTests

open HexRealRootsMathlib

private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]

private def replay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def negHalf : Dyadic := Dyadic.ofInt (-1) >>> (1 : Int)
private def half : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)

private def strict : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) negHalf (by decide),
  DyadicInterval.mk half (Dyadic.ofInt 2) (by decide)]⟩

private theorem replay_ok : replay.check quad = true := by decide
private theorem strict_ok : strict.checkStrict replay = true := by decide

example : replay.check quad = true := replay_ok
example : strict.checkStrict replay = true := strict_ok

/-- Enumeration contains `2n+1` cells, including both tails. -/
example : (Cell.all 0).size = 1 := by decide
example : (Cell.all 2).size = 5 := by decide
example : (Cell.all 3).size = 7 := by decide
example : Cell.all 2 =
    #[Cell.open ⟨0, by decide⟩, Cell.root ⟨0, by decide⟩,
      Cell.open ⟨1, by decide⟩, Cell.root ⟨1, by decide⟩,
      Cell.open ⟨2, by decide⟩] := by
  rfl

/-- The three open samples are respectively left of both roots, between them,
and right of both roots. -/
example : strict.openPoint ⟨0, by decide⟩ = Dyadic.ofInt (-3) := by decide
example : strict.openPoint ⟨1, by decide⟩ = 0 := by decide
example : strict.openPoint ⟨2, by decide⟩ = Dyadic.ofInt 3 := by decide

/-- The proof-facing sample and partition APIs consume the same checked data. -/
example : Cell.Sem (strict.rootModel (f := quad) (replay := replay)
      replay_ok strict_ok)
    (Cell.open ⟨1, by decide⟩) (Dyadic.toReal (strict.openPoint ⟨1, by decide⟩)) :=
  Cell.openPoint_mem (f := quad) (replay := replay) strict
    replay_ok strict_ok ⟨1, by decide⟩

example (z : ℝ) : ∃! c : Cell strict.intervals.size,
    Cell.Sem (strict.rootModel (f := quad) (replay := replay)
      replay_ok strict_ok) c z :=
  Cell.existsUnique_mem (strict.rootModel (f := quad) (replay := replay)
    replay_ok strict_ok) z

private def lower : Vector Separation.RootCmp 2 :=
  ⟨#[.eq, .gt], by decide⟩

private def upper : Vector Separation.RootCmp 2 :=
  ⟨#[.lt, .eq], by decide⟩

private def cmps : IocCmps 2 := ⟨lower, upper⟩

private theorem cmps_ok : IocCmps.check quad replay strict
    (Dyadic.ofInt (-1)) (Dyadic.ofInt 1) cmps = true := by decide

/-- For `(-1, 1]`, equality excludes the left root and includes the right one. -/
example : IocCmps.check quad replay strict (Dyadic.ofInt (-1))
    (Dyadic.ofInt 1) cmps = true := cmps_ok

example : Cell.meetsIoc cmps (Cell.open ⟨0, by decide⟩) = false := by decide
example : Cell.meetsIoc cmps (Cell.root ⟨0, by decide⟩) = false := by decide
example : Cell.meetsIoc cmps (Cell.open ⟨1, by decide⟩) = true := by decide
example : Cell.meetsIoc cmps (Cell.root ⟨1, by decide⟩) = true := by decide
example : Cell.meetsIoc cmps (Cell.open ⟨2, by decide⟩) = false := by decide
example : Cell.meetsIocOn (Dyadic.ofInt (-1)) (Dyadic.ofInt 1) cmps
    (Cell.root ⟨1, by decide⟩) = true := by decide

/-- The checked theorem identifies the Boolean table with actual intersection
against the half-open domain. -/
example (c : Cell strict.intervals.size) :
    Cell.meetsIoc cmps c = true ↔
      ∃ z : ℝ, Cell.Sem (strict.rootModel (f := quad) (replay := replay)
          replay_ok strict_ok) c z ∧
        z ∈ Set.Ioc (Dyadic.toReal (Dyadic.ofInt (-1)))
          (Dyadic.toReal (Dyadic.ofInt 1)) :=
  Cell.meetsIoc_iff_of_check (f := quad) (replay := replay) (cert := strict)
    cmps (Dyadic.ofInt (-1)) (Dyadic.ofInt 1)
    replay_ok strict_ok cmps_ok
    (HexRealRootsMathlib.toReal_lt_toReal (by decide)) c

/-- A mismatched comparison claim is rejected by replay. -/
private def badLower : Vector Separation.RootCmp 2 :=
  ⟨#[.gt, .gt], by decide⟩

example : IocCmps.check quad replay strict (Dyadic.ofInt (-1))
    (Dyadic.ofInt 1) ⟨badLower, upper⟩ = false := by decide

private def badUpper : Vector Separation.RootCmp 2 :=
  ⟨#[.lt, .lt], by decide⟩

example : IocCmps.check quad replay strict (Dyadic.ofInt (-1))
    (Dyadic.ofInt 1) ⟨lower, badUpper⟩ = false := by decide

/-! The zero-root branches reduce on an honest checked empty isolation. -/

private def posQuad : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 0, 1]
private def minusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int)]

private def posReplay : SturmReplay where
  chain := #[posQuad, x, minusOne]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def noRoots : IsolationCert := ⟨#[]⟩
private theorem posReplay_ok : posReplay.check posQuad = true := by decide
private theorem noRoots_ok : noRoots.checkStrict posReplay = true := by decide

private def emptyVec : Vector Separation.RootCmp 0 := ⟨#[], rfl⟩
private def noRootCmps : IocCmps 0 := ⟨emptyVec, emptyVec⟩

example : noRoots.openPoint ⟨0, by decide⟩ = 0 := by decide
example : Cell.meetsIoc noRootCmps (Cell.open ⟨0, by decide⟩) = true := by decide
example : IocCmps.check posQuad posReplay noRoots 0 (Dyadic.ofInt 1)
    noRootCmps = true := by decide

example (z : ℝ) : Cell.Sem
    (noRoots.rootModel (f := posQuad) (replay := posReplay)
      posReplay_ok noRoots_ok) (Cell.open ⟨0, by decide⟩) z := by
  have hzero : noRoots.intervals.size = 0 := rfl
  simp only [Cell.Sem, hzero, dite_true]

/-! A singleton isolation exercises the distinct left/right-tail branches. -/

private def linearReplay : SturmReplay where
  chain := #[x, one]
  derivScale := 1
  steps := #[]

private def singleton : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 1) (by decide)]⟩

private theorem linearReplay_ok : linearReplay.check x = true := by decide
private theorem singleton_ok : singleton.checkStrict linearReplay = true := by decide

private def oneLower : Vector Separation.RootCmp 1 := ⟨#[.gt], by decide⟩
private def oneUpper : Vector Separation.RootCmp 1 := ⟨#[.lt], by decide⟩
private def oneCmps : IocCmps 1 := ⟨oneLower, oneUpper⟩

example : singleton.openPoint ⟨0, by decide⟩ = Dyadic.ofInt (-2) := by decide
example : singleton.openPoint ⟨1, by decide⟩ = Dyadic.ofInt 2 := by decide
example : IocCmps.check x linearReplay singleton (Dyadic.ofInt (-1))
    (Dyadic.ofInt 1) oneCmps = true := by decide
example : Cell.meetsIoc oneCmps (Cell.open ⟨0, by decide⟩) = true := by decide
example : Cell.meetsIoc oneCmps (Cell.root ⟨0, by decide⟩) = true := by decide
example : Cell.meetsIoc oneCmps (Cell.open ⟨1, by decide⟩) = true := by decide

/-! Equal and reversed endpoints are rejected before the core relevance table. -/

example (c : Cell 2) : Cell.meetsIocOn (Dyadic.ofInt (-1))
    (Dyadic.ofInt (-1)) cmps c = false := by
  simp [Cell.meetsIocOn]

example (c : Cell 2) : Cell.meetsIocOn (Dyadic.ofInt 1)
    (Dyadic.ofInt (-1)) cmps c = false := by
  have h : ¬Dyadic.ofInt 1 < Dyadic.ofInt (-1) := by decide
  simp [Cell.meetsIocOn, h]

end Hex.RCF.CellsTests
