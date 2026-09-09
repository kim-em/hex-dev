/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealAlgebraic

/-! Additional compiled conformance cases, shared by the executable and fixture emitter. -/

open Hex
open Hex.RealAlgebraicNumber (ofRat ofAlgebraic? sqrt?)

namespace Hex.RealAlgebraicChecks

private def sqrtApprox (_ : Unit) : Bool :=
  match ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2)) with
  | none => false
  | some s =>
    let lo := ofRat (7071 / 5000)
    let hi := ofRat (14143 / 10000)
    compare lo s == .lt && compare hi s == .gt &&
      compare (-s) lo == .lt && compare lo (-s) == .gt &&
      compare (-s) hi == .lt && compare hi (-s) == .gt &&
      (#[0, ofRat (-3 / 2), s, -s]).all (fun a => sqrt? (a * a) == some a.abs) &&
      (#[(-8 : Int), 0, 16]).all (fun prec =>
        let c := ofRat (s.approx prec).toRat
        let e := ofRat (Dyadic.ofIntWithPrec 1 prec).toRat
        decide (c - e ≤ s) && decide (s ≤ c + e))

private def mignotte (_ : Unit) : Bool :=
  let p : ZPoly := #p[-2, 1024, -131072, 0, 0, 0, 0, 0, 1]
  let roots := p.realAlgebraicRoots
  roots.size == 4 &&
    (roots.toList.zip roots.toList.tail).all (fun (a, b) => decide (a < b)) &&
    match roots[1]?, roots[2]? with
    | some a, some b =>
      decide (a < ofRat (1 / 256)) && decide (ofRat (1 / 256) < b) &&
        decide (ofRat (1 / 256 - 1 / (2 ^ (35 : Nat) : Rat)) < a) &&
        decide (b < ofRat (1 / 256 + 1 / (2 ^ (35 : Nat) : Rat)))
    | _, _ => false

private def crossFactor (_ : Unit) : Bool :=
  let q : Rat := 1 / (2 ^ (12 : Nat) : Rat)
  let roots := ZPoly.realAlgebraicRoots #p[-2, 0, 1]
  match roots[1]? with
  | none => false
  | some s =>
    let t := s + ofRat q
    !(s.toAlgebraic.p == t.toAlgebraic.p) && compare s t == .lt && compare t s == .gt &&
      t - s == ofRat q

private def degreeEight (_ : Unit) : Bool :=
  let p : ZPoly := #p[-2, 0, 1] * #p[-3, 0, 1] * #p[-5, 0, 1] * #p[-7, 0, 1]
  let roots := p.realAlgebraicRoots
  let permuted := roots.toList.reverse
  let sorted := permuted.mergeSort (fun a b => decide (a ≤ b))
  roots.size == 8 && sorted.toArray == roots &&
    (roots.toList.zip roots.toList.tail).all (fun (a, b) => decide (a < b)) &&
    roots.map (fun a => (a * a).toRat?) ==
      #[some 7, some 5, some 3, some 2, some 2, some 3, some 5, some 7]

private def irrationalCoefficient (_ : Unit) : Bool :=
  match ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2)) with
  | none => false
  | some s =>
    let roots := (RealAlgebraicPoly.ofArray #[-s, 0, 1]).roots.toArray
    roots.size == 2 && roots.all (fun r => r.root * r.root == s && r.multiplicity == 1) &&
      match roots[0]?, roots[1]? with
      | some a, some b => compare a.root b.root == .lt && a.root == (-b.root : RealAlgebraicNumber)
      | _, _ => false

private def repeatedRoots (_ : Unit) : Bool :=
  let roots := (RealAlgebraicPoly.ofArray #[1, -2, 1]).roots.toArray
  roots.size == 1 && roots.all (fun r => r.root == 1 && r.multiplicity == 2) &&
    (RealAlgebraicPoly.ofArray #[]).roots.contains (ofRat (123 / 7)) &&
    (ZPoly.realAlgebraicRoots #p[]).isEmpty && (ZPoly.realAlgebraicRoots #p[7]).isEmpty

private def integerRounding (_ : Unit) : Bool :=
  (#[(-2 : Int), 0, 3]).all (fun n =>
    let a : RealAlgebraicNumber := n
    a.floor == n && a.ceil == n && a.toRat? == some (n : Rat))

/-- Run the larger root fixtures as compiled executable checks. -/
def run (verbose : Bool := false) : IO Unit := do
  if verbose then IO.eprintln "checking sqrtApprox"
  if !sqrtApprox () then throw (IO.userError "real algebraic conformance: sqrtApprox")
  if verbose then IO.eprintln "checking mignotte"
  if !mignotte () then throw (IO.userError "real algebraic conformance: mignotte")
  if verbose then IO.eprintln "checking crossFactor"
  if !crossFactor () then throw (IO.userError "real algebraic conformance: crossFactor")
  if verbose then IO.eprintln "checking degreeEight"
  if !degreeEight () then throw (IO.userError "real algebraic conformance: degreeEight")
  if verbose then IO.eprintln "checking irrationalCoefficient"
  if !irrationalCoefficient () then throw (IO.userError "real algebraic conformance: irrationalCoefficient")
  if verbose then IO.eprintln "checking repeatedRoots"
  if !repeatedRoots () then throw (IO.userError "real algebraic conformance: repeatedRoots")
  if verbose then IO.eprintln "checking integerRounding"
  if !integerRounding () then throw (IO.userError "real algebraic conformance: integerRounding")

end Hex.RealAlgebraicChecks
