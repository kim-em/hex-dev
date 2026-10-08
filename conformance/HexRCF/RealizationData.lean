/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealCoefficients.Realization

public section

/-! Literal recursive BKR data for the root of `X − (1 + ε)` and the entire
shared `(1, 2]` guard conjunction. Count, moment and remainder identities are
stored directly; no root/sign producer is invoked. -/

open Hex Hex.RealFormula Hex.SignDet Hex.RCF.RealCoefficients
open scoped Hex
attribute [local instance 2500] Field.toGrindField
namespace Hex.RCF.RealizationTests
abbrev E := RationalFn Rat
def sign : E → Int := OrderedFn.Infinitesimal.sign OrderedFn.orderSign
def epsilon : E := RationalFn.X
def x : DensePoly E := DensePoly.ofList [0, 1]
def p : DensePoly E := x - DensePoly.C (1 + epsilon)
def first : DensePoly E := x - 1
def second : DensePoly E := x - 2
def values : Fin 1 → Rat := fun _ => 1
def formula : QF 2 := .and (.atom ⟨MvPoly.X 1 - MvPoly.X 0, .gt⟩)
  (.atom ⟨MvPoly.X 1 - 2, .le⟩)
def chain (c : E) (quotient : DensePoly E) : SignedRemainderChain E where
  chain := #[p, DensePoly.C c]
  degrees := #[1, 0]
  initial := ⟨1, quotient, 1⟩
  steps := #[]
  terminal := some (c * c, DensePoly.C c * p)
def count : TarskiCertificate E E Nat where
  context := 7
  head := p
  queryPoly := 1
  lower := .finite 1
  upper := .finite 2
  squarefree := chain 1 0
  remainders := chain 1 0
  lowerSigns := #[-1, 1]
  upperSigns := #[1, 1]
  lowerVariations := 1
  upperVariations := 0
  value := 1
def moment (query : DensePoly E) (c : E) (quotient : DensePoly E) (s : Int) :
    TarskiCertificate E E Nat :=
  { count with
    queryPoly := query
    remainders := chain c quotient
    lowerSigns := #[-1, s]
    upperSigns := #[1, s]
    lowerVariations := if s = 1 then 1 else 0
    upperVariations := if s = 1 then 0 else 1
    value := s }
def inverse3 : Matrix Int 3 3 :=
  Matrix.ofRows #v[#v[0, -1, 1], #v[2, 0, -2], #v[0, 1, 1]]
def child (q : DensePoly E) (c : E) (quotient : DensePoly E) (s : Int) : Node E Nat where
  context := 7
  head := p
  lower := .finite 1
  upper := .finite 2
  queries := [q]
  size := 3
  system := {
    rows := #v[[0], [1], [2]]
    columns := #v[[-1], [0], [1]]
    counts := if s = 1 then #v[0, 0, 1] else #v[1, 0, 0]
    values := #v[1, s, 1]
    denominator := 2
    inverse := inverse3 }
  moments := #v[count, moment q c quotient s,
    moment (q * q) (c * c) (quotient * (q + DensePoly.C c)) 1]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by
      by_cases h : s = 1
      · simp [System.positive, h]
        exact ⟨(2 : Fin 3), by norm_num⟩
      · simp [System.positive, h]
        exact ⟨(0 : Fin 3), by norm_num⟩⟩]
    denom := 1
    adj := Matrix.identity 1}
def node : Node E Nat where
  context := 7
  head := p
  lower := .finite 1
  upper := .finite 2
  queries := [first, second]
  size := 1
  system := {
    rows := #v[[0, 0]]
    columns := #v[[1, -1]]
    counts := #v[1]
    values := #v[1]
    denominator := 1
    inverse := Matrix.identity 1 }
  moments := #v[count]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide +kernel⟩]
    denom := 1
    adj := Matrix.identity 1}
def replay : Replay E Nat :=
  .split node (.leaf (child first epsilon 1 1))
    (.leaf (child second (epsilon - 1) 1 (-1)))

end Hex.RCF.RealizationTests
