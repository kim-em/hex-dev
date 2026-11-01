/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Elimination
import HexGroebner.Fixtures

open Hex.Groebner

namespace Hex.Groebner.MatrixNativeConformance

private def rowEq (a b : SparseRow) : Bool :=
  a.columns.data == b.columns.data && a.coefficients.data == b.coefficients.data

private def equal (a b : MatrixResult) : Bool :=
  a.stats == b.stats && match a.result,b.result with
  | .error e,.error f => e == f
  | .ok a,.ok b => a.reducerRank == b.reducerRank && a.trace == b.trace &&
    a.rows.size == b.rows.size && (a.rows.zip b.rows).all fun (a,b) =>
      rowEq a.row b.row && a.fromTarget == b.fromTarget && a.derivation == b.derivation &&
        a.multiplier == b.multiplier && a.sugar == b.sugar
  | _,_ => false

private def equalR (a b : RemainderResult) : Bool :=
  a.stats == b.stats && match a.result,b.result with
  | .error e,.error f => e == f
  | .ok a,.ok b => a.trace == b.trace && a.rows.size == b.rows.size &&
    (a.rows.zip b.rows).all fun (a,b) => rowEq a.row b.row &&
      a.derivation == b.derivation && a.sugar == b.sugar
  | _,_ => false

private def checked : Bool := Id.run do
  for field in Fixtures.fields do
    for c in Fixtures.cases field do
      let .ok reducers := Fixtures.sparse field c.columns c.reducers | return false
      let .ok targets := Fixtures.sparse field c.columns c.targets | return false
      let sugars := (Array.range (reducers.size+targets.size)).map fun i => 2^90+i*17
      for provenance in [false,true] do
        let expected := eliminateWith field {} c.columns reducers targets provenance sugars false
        if !equal expected (eliminateWith field {} c.columns reducers targets provenance sugars) then return false
        if !equalR (reduceRowsWith field {} c.columns reducers targets provenance sugars false)
            (reduceRowsWith field {} c.columns reducers targets provenance sugars) then return false
        for work in [0,1,64,expected.stats.work/2,expected.stats.work-1,expected.stats.work] do
          if !equal (eliminateWith field { work } c.columns reducers targets provenance sugars false)
              (eliminateWith field { work } c.columns reducers targets provenance sugars) then return false
        for traceNodes in [0,1,expected.stats.traceNodes-1,expected.stats.traceNodes] do
          if !equal (eliminateWith field { traceNodes } c.columns reducers targets provenance sugars false)
              (eliminateWith field { traceNodes } c.columns reducers targets provenance sugars) then return false
        for packedBytes in [0,1,expected.stats.packedBytes/2,expected.stats.packedBytes-1,expected.stats.packedBytes] do
          if !equal (eliminateWith field { packedBytes } c.columns reducers targets provenance sugars false)
              (eliminateWith field { packedBytes } c.columns reducers targets provenance sugars) then return false
        for outputEntries in [0,expected.stats.outputEntries-1,expected.stats.outputEntries] do
          if !equal (eliminateWith field { outputEntries } c.columns reducers targets provenance sugars false)
              (eliminateWith field { outputEntries } c.columns reducers targets provenance sugars) then return false
        let independent := reduceRowsWith field {} c.columns reducers targets provenance sugars
        for packedBytes in [0,independent.stats.packedBytes/2,independent.stats.packedBytes-1,independent.stats.packedBytes] do
          if !equalR (reduceRowsWith field { packedBytes } c.columns reducers targets provenance sugars false)
              (reduceRowsWith field { packedBytes } c.columns reducers targets provenance sugars) then return false
  return true

#guard checked

private def large : Bool := Id.run do
  let field : PrimeField := ⟨65537,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let n := 5000
  let .some reducer := SparseRow.ofEntries field n ((Array.range n).map fun i => (i,1)) | return false
  let .some target := SparseRow.ofEntries field n ((Array.range n).map fun i => (i,2)) | return false
  for provenance in [false,true] do
    let expected := eliminateWith field {} n #[reducer] #[target] provenance #[100,7] false
    if !equal expected (eliminateWith field {} n #[reducer] #[target] provenance #[100,7]) then return false
    for work in [expected.stats.work/2,expected.stats.work-1,expected.stats.work] do
      if !equal (eliminateWith field { work } n #[reducer] #[target] provenance #[100,7] false)
          (eliminateWith field { work } n #[reducer] #[target] provenance #[100,7]) then return false
  return true

#guard large

def engineRuntimeChecks : Bool := checked && large

end Hex.Groebner.MatrixNativeConformance
