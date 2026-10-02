/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Algebraic
import Nested
import Lean.Data.Json
open Hex Algebraic Lean

def polyJson (p : QPoly) : Json := toJson (p.toArray.map toString)
def fieldPolyJson {d : Descriptor} (p : DensePoly (Element d)) : Json :=
  Json.arr (p.toArray.map (polyJson ∘ raw))
def emit (xs : List (String × Json)) : IO Unit := IO.println (Json.mkObj xs).compress

def checkPair (a b : DensePoly (Element reducible)) : IO Unit := do
  let (q,r) := DensePoly.divMod a b
  let g := DensePoly.monicize (DensePoly.gcd a b)
  let xg := DensePoly.xgcd a b
  emit [("kind",toJson "poly"),("a",fieldPolyJson a),("b",fieldPolyJson b),
    ("quot",fieldPolyJson q),("rem",fieldPolyJson r),("gcd",fieldPolyJson g),
    ("xgcd",fieldPolyJson xg.gcd),("left",fieldPolyJson xg.left),
    ("right",fieldPolyJson xg.right),("mul",fieldPolyJson (a*b)),
    ("batch",fieldPolyJson (batchMul reducible a b))]

def main : IO Unit := do
  unless Nested.checks do throw (IO.userError "nested algebraic checks failed")
  -- Full coefficient vectors, not just hashes, are checked independently in Python.
  for seed in [:48] do
    let q := DensePoly.ofCoeffs ((List.range (seed%6+1)).toArray.map fun i =>
      (((seed*17+i*13)%11 : Nat) : Rat)-5)
    let q := if seed%3 == 0 then q*sqrt2 else if seed%3 == 1 then q*sqrt3 else q
    let inv := invert reducible q
    emit [("kind",toJson "scalar"),("q",polyJson q),("zero",toJson (isZero reducible q)),
      ("inverse",polyJson inv.value),("factor",polyJson inv.polynomial),
      ("discarded",polyJson inv.discarded),("split",toJson inv.split),
      ("sign",toJson (signSqrt2 q))]
  for n in [2,3,4] do
    for salt in [:4] do
      let a := input reducible n salt
      let b := input reducible (n-1) (salt+1)
      checkPair a b
  let a := input reducible 3
  let b := input reducible 2 1
  let factor := input reducible 2 2
  checkPair (a*factor) (b*factor)
  checkPair 0 a
  checkPair a 0
  checkPair 0 0
  checkPair a a
  for n in [4,8,16] do
    for shared in [false,true] do
      let p := input reducible n
      let q := input reducible n 1
      let p := if shared then DensePoly.ofCoeffs (p.toArray.map fun a => pack reducible (raw a*sqrt3)) else p
      let q := if shared then DensePoly.ofCoeffs (q.toArray.map fun a => pack reducible (raw a*sqrt3)) else q
      let (a,ca) := tracedMul reducible false p q
      let (b,cb) := tracedMul reducible true p q
      unless observePoly a == observePoly (p*q) && observePoly b == observePoly (batchMul reducible p q) && observePoly a == observePoly b do
        throw (IO.userError "instrumentation disagrees with kernel")
      emit [("kind",toJson "cost"),("n",toJson n),("shared",toJson shared),
        ("each",toJson #[ca.zeroTests,ca.gcds,ca.sturmCounts]),
        ("batch",toJson #[cb.zeroTests,cb.gcds,cb.sturmCounts])]
  let live := (input reducible 8).toArray
  let inv := invert reducible sqrt3
  let d := refine reducible inv
  unless valid d && live.map observe == (live.map (transport reducible d)).map observe do
    throw (IO.userError "split transport changed a live value")
  -- A cancellation-heavy product has semantic zero coefficients with nonzero raw representatives.
  let a := pack reducible (DensePoly.monomial 1 1)
  let p := DensePoly.ofCoeffs #[a,1]
  let q := DensePoly.ofCoeffs #[-((2 : Nat) : Element reducible),a]
  unless !sqrt2.isZero && (zeroWithCost reducible sqrt2).2.sturmCounts == 1 do
    throw (IO.userError "cancellation fixture does not need root selection")
  unless observePoly (p*q) == observePoly (batchMul reducible p q) && (p*q).coeff 1 == 0 do
    throw (IO.userError "cancellation failed")
