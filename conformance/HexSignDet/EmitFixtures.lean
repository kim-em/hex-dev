/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSignDet
import Hex.Conformance.Emit
import HexRealAlgebraic.Roots
import HexPolyZ.IntegerPolynomial
import Lean.Data.Json

/-! Rational BKR fixtures with independent real-algebraic root evaluation.
This consumer-only import of `HexRealAlgebraic` creates no library dependency
from sign determination back to the rational real-algebraic implementation. -/
namespace Hex.SignDet.Emit

open Lean

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]

private def poly (p : DensePoly Rat) : Json := Json.arr (p.toArray.map rat)

private def endpoint : Endpoint Rat → Json
  | .negInf => toJson "-inf"
  | .posInf => toJson "+inf"
  | .finite q => rat q

private def row (signs : List Int) (count : Nat) : Json :=
  Json.mkObj [("signs", toJson signs), ("count", toJson count)]

private def table {r : Nat} (s : System r) : Json :=
  toJson (s.positive.map fun i => row s.columns[i] s.counts[i].toNat)

private def result (t : Json) (replay : Bool) : Json :=
  Json.mkObj [("status", toJson "ok"), ("table", t), ("replay", toJson replay)]

private def failure (error : BuildError) : Json :=
  Json.mkObj [("status", toJson "error"), ("error", toJson (reprStr error))]

private def produced (domain : Sturm.PreparedDomain Rat) (qs : List (DensePoly Rat))
    (reduced : Bool) : Json :=
  match buildPrepared (10377 : Nat) domain qs reduced with
  | .error error => failure error
  | .ok t => result (table t.val.node.system)
    (t.val.check Sturm.orderSign 10377 domain.head domain.lower domain.upper qs)

private def reference (domain : Sturm.PreparedDomain Rat) (qs : List (DensePoly Rat)) : Json :=
  match referencePrepared (10377 : Nat) domain qs with
  | .error error => failure error
  | .ok n => result (table n.system)
    (n.check Sturm.orderSign 10377 domain.head domain.lower domain.upper qs)

private def inside (lower upper : Endpoint Rat) (root : RealAlgebraicNumber) : Bool :=
  (match lower with
   | .negInf => true
   | .posInf => false
   | .finite q => decide (RealAlgebraicNumber.ofRat q < root)) &&
  (match upper with
   | .posInf => true
   | .negInf => false
   | .finite q => decide (root < RealAlgebraicNumber.ofRat q))

/-- Independent existing real-algebraic root enumeration and Horner evaluation;
no BKR rows, moments, counts or proposed support enter this computation. -/
private def algebraicTable (p : DensePoly Rat) (qs : List (DensePoly Rat))
    (lower upper : Endpoint Rat) : Json :=
  let roots := (ZPoly.clearDenominators p).2.realAlgebraicRoots
  let words := (roots.filter (inside lower upper)).toList.map fun root =>
    qs.map fun q =>
      let value := q.toArray.toList.reverse.foldl
        (fun acc c => acc * root + RealAlgebraicNumber.ofRat c) 0
      value.sign
  let support := words.eraseDups.mergeSort (fun a b => compare a b != .gt)
  toJson (support.map fun signs => row signs (words.count signs))

private def emit (case : String) (p : DensePoly Rat) (qs : List (DensePoly Rat))
    (lower : Endpoint Rat := .negInf) (upper : Endpoint Rat := .posInf) : IO Unit := do
  let input := [("schema", toJson (1 : Nat)), ("seed", toJson (10377 : Nat)),
    ("head", poly p), ("queries", toJson (qs.map poly)),
    ("lower", endpoint lower), ("upper", endpoint upper)]
  let fields := match Sturm.prepare Sturm.orderSign p lower upper with
    | none =>
      let invalid := Json.mkObj [("status", toJson "invalid-domain")]
      [("reduced", invalid), ("direct", invalid), ("reference", invalid), ("algebraic", Json.null)]
    | some domain =>
      [("reduced", produced domain qs true), ("direct", produced domain qs false),
        ("algebraic", algebraicTable p qs lower upper)] ++
        (if qs.length ≤ 4 then [("reference", reference domain qs)] else [])
  Hex.Conformance.Emit.emitResult "HexSignDet" case "table" (Json.mkObj (input ++ fields)).compress

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]

def run : IO Unit := do
  let p := x * x - 1
  emit "two-roots" p [x, x - 1]
  emit "negative-head" (-p) [x, x - 1]
  emit "empty-queries" p []
  emit "zero-root" x [x, 0]
  emit "duplicate-zero-constant" p [0, 1, x, x]
  emit "irrational-common-factor" (x * x - 2) [x, x * x - 2, x * x - 3, x - 1]
  emit "cubic-derivatives" (x.natPow 3 - x) [3 * x * x - 1, 6 * x, 6]
  emit "negative-cubic-derivatives" (x - x.natPow 3) [1 - 3 * x * x, -6 * x, -6]
  emit "high-degree-queries" p [x.natPow 7 + 1, x.natPow 6 - 1]
  emit "rational-scaling" (DensePoly.scale (1 / 6) p) [DensePoly.scale (-1 / 10) x]
  emit "finite-interval" (x.natPow 3 - x) [x] (.finite (-1 / 2)) (.finite (1 / 2))
  emit "left-half-line" p [x] .negInf (.finite 0)
  emit "right-half-line" p [x] (.finite 0) .posInf
  emit "many-queries" (x.natPow 3 - x) (List.replicate 12 x)
  for (name, head) in [("constant", (3 : DensePoly Rat)), ("negative-constant", -2),
      ("root-free", x * x + 1)] do
    emit (name ++ "/empty") head []
    emit (name ++ "/queries") head [x, 0]
  for (name, head) in [("zero-head", (0 : DensePoly Rat)), ("repeated-head", p * p),
      ("cancelled-head", p - p)] do
    emit (name ++ "/empty") head []
    emit (name ++ "/queries") head [x]
  for (i, (lower, upper)) in ([(.negInf, .negInf), (.posInf, .posInf), (.posInf, .negInf),
      (.finite 0, .negInf), (.posInf, .finite 0), (.finite 0, .finite 0),
      (.finite 2, .finite (-2)), (.finite (-1), .posInf), (.negInf, .finite 1)] :
      List (Endpoint Rat × Endpoint Rat)).zipIdx.map (fun (pair, i) => (i, pair)) do
    emit s!"invalid-interval/{i}" p [] lower upper
  -- Fixed seed and generator; all generated inputs are emitted in full.
  let mut state := 10377
  for i in List.range 24 do
    state := (1664525 * state + 1013904223) % 4294967296
    let a : Rat := (state % 17 : Nat) - 8
    state := (1664525 * state + 1013904223) % 4294967296
    let b : Rat := (state % 19 : Nat) - 9
    let head := (x * x - 2) * (x - DensePoly.C ((i + 2 : Nat) : Rat))
    emit s!"seed-10377/{i}" head [x + DensePoly.C a, x * x + DensePoly.C b, head]

end Hex.SignDet.Emit

def main : IO Unit := Hex.SignDet.Emit.run
