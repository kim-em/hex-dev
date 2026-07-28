/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import Init.Data.List.Lemmas
import Init.Data.List.Nat.Sum
public import HexRCF.SeparationCheck

public section

/-!
# Executable cells and bounded-domain checks

An array of `n` strictly ordered carrier roots cuts the real line into `n`
root cells and `n + 1` open cells. This module stores only indices, exact
dyadic sample points, claimed endpoint comparisons, and Boolean relevance
checks. The semantic roots and real-cell interpretation live in `HexRCF.Cells`.
-/

namespace Hex.RCF

/-- A root cell or one of the open cuts around `n` ordered roots. -/
inductive Cell (n : Nat) where
  /-- Open cell at a cut between roots, including both tails. -/
  | open (cut : Fin (n + 1))
  /-- Singleton cell at an isolated root. -/
  | root (i : Fin n)
  deriving DecidableEq, Repr

namespace Cell

/-- Alternating position of a cell in the left-to-right decomposition. -/
@[expose]
def rank : Cell n → Nat
  | .open cut => 2 * cut.val
  | .root i => 2 * i.val + 1

/-- Every rank is a valid index into a `2 * n + 1` cell vector. -/
theorem rank_lt (c : Cell n) : c.rank < 2 * n + 1 := by
  cases c with
  | «open» cut => simp [rank]; omega
  | root i => simp [rank]

/-- Deterministic left-to-right enumeration of all `2 * n + 1` cells. -/
@[expose]
def all (n : Nat) : Array (Cell n) :=
  (((List.finRange n).flatMap fun i =>
      [Cell.open i.castSucc, Cell.root i]) ++
    [Cell.open (Fin.last n)]).toArray

/-- The enumeration for `n` roots contains `2 * n + 1` cells. -/
@[simp] theorem size_all (n : Nat) : (all n).size = 2 * n + 1 := by
  simp [all, List.map_const']
  omega

/-- Every size-correct cell occurs in the executable enumeration. -/
theorem mem_all (c : Cell n) : c ∈ all n := by
  cases c with
  | root i =>
      simp [all]
  | «open» cut =>
      by_cases hlast : cut.val = n
      · have hcut : cut = Fin.last n := Fin.ext (by simpa [Fin.last] using hlast)
        subst cut
        simp [all]
      · let i : Fin n := ⟨cut.val, by omega⟩
        have hcut : i.castSucc = cut := Fin.ext rfl
        simp [all]
        exact Or.inl ⟨i, hcut.symm⟩

end Cell

namespace IsolationCert

/-- Exact dyadic sample for an open cut. -/
@[expose]
def openPoint (cert : IsolationCert) :
    Fin (cert.intervals.size + 1) → Dyadic
  | cut =>
      if hzero : cert.intervals.size = 0 then 0
      else if hleft : cut.val = 0 then
        (cert.intervals[0]'(by omega)).lower + Dyadic.ofInt (-1)
      else if hright : cut.val = cert.intervals.size then
        (cert.intervals[cert.intervals.size - 1]'(by omega)).upper + Dyadic.ofInt 1
      else
        ((cert.intervals[cut.val - 1]'(by omega)).upper +
          (cert.intervals[cut.val]'(by omega)).lower) >>> (1 : Int)

/-- Open cells carry exact dyadic samples. Root cells are represented by their
certified isolation instead. -/
@[expose]
def sample? (cert : IsolationCert) : Cell cert.intervals.size → Option Dyadic
  | .open cut => some (cert.openPoint cut)
  | .root _ => none

/-- Sampling an open cell returns its exact dyadic sample point. -/
@[simp] theorem sample?_open (cert : IsolationCert)
    (cut : Fin (cert.intervals.size + 1)) :
    cert.sample? (.open cut) = some (cert.openPoint cut) := rfl

end IsolationCert

/-- Claimed carrier-root comparisons against the lower and upper endpoints of
a bounded domain. -/
structure IocCmps (n : Nat) where
  /-- Each root's order relative to the excluded lower endpoint. -/
  lower : Vector Separation.RootCmp n
  /-- Each root's order relative to the included upper endpoint. -/
  upper : Vector Separation.RootCmp n
  deriving Repr

namespace IocCmps

/-- Recompute every claimed endpoint comparison. This validates comparison
data only. The bounded-domain layer separately checks `a < b`. -/
@[expose]
def check (f : ZPoly) (replay : SturmReplay) (cert : IsolationCert)
    (a b : Dyadic) (cmps : IocCmps cert.intervals.size) : Bool :=
  (List.range cert.intervals.size).all fun i =>
    if hi : i < cert.intervals.size then
      Separation.checkCmp f replay cert.intervals[i] a cmps.lower[i] &&
        Separation.checkCmp f replay cert.intervals[i] b cmps.upper[i]
    else false

end IocCmps

namespace Cell

/-- Executable bounded-domain relevance test for a cell. The surrounding
certificate first checks `a < b`. This definition assumes that the domain is
nonempty. -/
@[expose]
def meetsIoc (cmps : IocCmps n) : Cell n → Bool
  | .root i => cmps.lower[i] == .gt && cmps.upper[i] != .gt
  | .open cut =>
      if hzero : n = 0 then true
      else if hleft : cut.val = 0 then
        cmps.lower[0] == .gt
      else if hright : cut.val = n then
        cmps.upper[n - 1] == .lt
      else
        cmps.upper[cut.val - 1] == .lt && cmps.lower[cut.val] == .gt

/-- Guard the nonempty-domain relevance table against equal or reversed
endpoints. -/
@[expose]
def meetsIocOn (a b : Dyadic) (cmps : IocCmps n) (c : Cell n) : Bool :=
  decide (a < b) && meetsIoc cmps c

end Cell

end Hex.RCF
