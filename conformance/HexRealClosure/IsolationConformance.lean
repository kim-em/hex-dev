/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.IsolationRoots
public import HexSignDet.Codec
public import HexOrderedFn.Infinitesimal
public import Lean.Data.Json.Printer
public import Lean.Data.Json.FromToJson.Basic

public section

open Hex Hex.RealClosure Hex.RealClosure.Isolation Lean

private def rational (a : Rat) : Json := toJson (a.num, a.den)

private def fraction (a : RationalFn Rat) : Json := Json.mkObj [
  ("num", .arr (a.num.toArray.map rational)), ("den", .arr (a.den.toArray.map rational))]

private def emit {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Neg E] [Inv E]
    (name : String) (depth : Nat) (sign : E → Int) (encode : E → Json)
    (p : DensePoly E) : IO Unit := do
  let result := complete? sign (10378 : Nat) p
  let output := match result with
    | .error error => Json.mkObj [("error", .str (reprStr error))]
    | .ok none => .null
    | .ok (some completion) =>
      let route := match completion.search.route with
        | .whole stored => Json.mkObj [("kind", .str "whole"),
            ("head", .arr (stored.domain.head.toArray.map encode))]
        | .bounded bound frontier => Json.mkObj [("kind", .str "bounded"),
            ("bound", encode bound.value), ("nodes", toJson frontier.nodes),
            ("head", .arr (frontier.head.toArray.map encode)),
            ("cells", .arr (frontier.cells.toArray.map fun cell => Json.mkObj [
              ("lower", encode cell.lower), ("upper", encode cell.upper),
              ("count", toJson cell.count)]))]
      Json.mkObj [("route", route), ("points", .arr (completion.roots.points.toArray.map encode)),
        ("descriptors", .arr (completion.roots.descriptors.toArray.map fun d => Json.mkObj [
          ("head", .arr (d.raw.head.toArray.map encode)),
          ("lower", SignDet.Codec.endpoint ⟨encode, fun _ => .error "encode only"⟩ d.raw.lower),
          ("upper", SignDet.Codec.endpoint ⟨encode, fun _ => .error "encode only"⟩ d.raw.upper),
          ("indices", toJson d.raw.indices), ("signs", toJson d.raw.signs)]))]
  IO.println (Json.mkObj [("case", .str name), ("depth", toJson depth),
    ("head", .arr (p.toArray.map encode)), ("output", output)]).compress

private def emitRat := emit (depth := 0) (sign := Sturm.orderSign) (encode := rational)

def main : IO Unit := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  emitRat "zero" 0
  emitRat "constant" (DensePoly.C 5)
  emitRat "repeated" ((x - 1) * (x - 1))
  emitRat "nonmonic linear" (DensePoly.ofCoeffs #[-3, 2])
  emitRat "quadratic" (x * x - 2)
  emitRat "negative cubic with removed zero" (DensePoly.scale (-3) (x * (x * x - 2)))
  emitRat "nonquadratic" (x * x * x - 2)
  emitRat "four roots" ((x * x - 2) * (x * x - 3))
  let epsilon : RationalFn Rat := RationalFn.X
  let sign := OrderedFn.Infinitesimal.sign Sturm.orderSign
  emit "whole-line inverse infinitesimal" 1 sign fraction (DensePoly.ofCoeffs #[-epsilon⁻¹, 1])
  emit "inseparable by rational bisection" 1 sign fraction
    (DensePoly.ofCoeffs #[-epsilon, 1] * DensePoly.ofCoeffs #[-(2 * epsilon), 1])
