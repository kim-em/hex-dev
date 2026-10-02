/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFactors
public import HexRealClosure.AlgebraicContext
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
    (p : DensePoly E) (context : Nat := 10378) (base : Option Json := none) : IO Unit := do
  let result := complete? sign context p
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
          ("context", toJson d.raw.context),
          ("head", .arr (d.raw.head.toArray.map encode)),
          ("lower", SignDet.Codec.endpoint ⟨encode, fun _ => .error "encode only"⟩ d.raw.lower),
          ("upper", SignDet.Codec.endpoint ⟨encode, fun _ => .error "encode only"⟩ d.raw.upper),
          ("indices", toJson d.raw.indices), ("signs", toJson d.raw.signs)]))]
  let fields := [("case", .str name), ("depth", toJson depth),
    ("head", .arr (p.toArray.map encode)), ("output", output)]
  let fields := match base with
    | none => fields
    | some descriptor => ("base", descriptor) :: fields
  IO.println (Json.mkObj fields).compress

private def emitRat := emit (depth := 0) (sign := Sturm.orderSign) (encode := rational)

private def emitAssembly {E : Type} [Zero E] [DecidableEq E] [One E] [Add E]
    [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
    (name : String) (sign : E → Int) (encode : E → Json) (p : DensePoly E)
    (context : Nat := 10378) (base : Option Json := none) : IO Unit := do
  let output := match Roots.assemble sign context p with
    | .error error => Json.mkObj [("error", .str (reprStr error))]
    | .ok .all => Json.mkObj [("kind", .str "all")]
    | .ok (.finite entries) => Json.mkObj [("kind", .str "finite"),
        ("entries", .arr (entries.toArray.map fun entry =>
          let root := match entry.root with
            | .point value => Json.mkObj [("kind", .str "point"), ("value", encode value)]
            | .selected d => Json.mkObj [("kind", .str "selected"),
                ("context", toJson d.raw.context),
                ("head", .arr (d.raw.head.toArray.map encode)),
                ("lower", SignDet.Codec.endpoint
                  ⟨encode, fun _ => .error "encode only"⟩ d.raw.lower),
                ("upper", SignDet.Codec.endpoint
                  ⟨encode, fun _ => .error "encode only"⟩ d.raw.upper),
                ("indices", toJson d.raw.indices), ("signs", toJson d.raw.signs)]
          Json.mkObj [("root", root), ("multiplicity", toJson entry.multiplicity)]))]
  let fields := [("case", .str name), ("mode", .str "assembly"),
    ("head", .arr (p.toArray.map encode)), ("output", output)]
  let fields := match base with
    | none => fields
    | some descriptor => ("base", descriptor) :: fields
  IO.println (Json.mkObj fields).compress

private def emitAssemblyRat (name : String) (p : DensePoly Rat) : IO Unit :=
  emitAssembly name Sturm.orderSign rational p

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
  emitAssemblyRat "assembly zero" 0
  emitAssemblyRat "assembly constant" (DensePoly.C 5)
  emitAssemblyRat "assembly pure power" (DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, -5])
  let quadratic := x * x - 2
  let repeated := DensePoly.scale (-3) (x * x * quadratic * quadratic * quadratic *
    (x - 3) * (x - 3) * (x - 3) * (x - 3) * (x - 3))
  emitAssemblyRat "assembly repeated factors" repeated
  emitAssemblyRat "assembly root-free factor" ((x * x + 1) * (x * x + 1) * (x - 1))
  emitAssemblyRat "assembly simple zero" (x * (x - 1) * (x - 1))
  let firstHead := (x * x - 2) * (x - 3)
  let some firstRoot := SignDet.Descriptor.validate Sturm.orderSign (10378 : Nat)
      { context := 10378, head := firstHead, lower := .finite 1,
        upper := .finite 2, indices := [], signs := [] }
    | throw (IO.userError "nested isolation: first descriptor failed")
  let first := Algebraic.Context.adjoin firstRoot (fun q : Rat => q.den == 1)
  let alpha := Algebraic.Element.ofPoly (context := first) x
  let baseDescriptor := Json.mkObj [
    ("context", toJson firstRoot.raw.context),
    ("head", .arr (firstRoot.raw.head.toArray.map rational)),
    ("lower", SignDet.Codec.endpoint
      ⟨rational, fun _ => .error "encode only"⟩ firstRoot.raw.lower),
    ("upper", SignDet.Codec.endpoint
      ⟨rational, fun _ => .error "encode only"⟩ firstRoot.raw.upper),
    ("indices", toJson firstRoot.raw.indices), ("signs", toJson firstRoot.raw.signs)]
  let nested : DensePoly (Algebraic.Element first) := DensePoly.ofCoeffs #[-alpha, 0, 1]
  emit "nested algebraic coefficients" 1 Algebraic.Element.sign
    (fun a => .arr (a.polynomial.toArray.map rational)) nested 10379 (some baseDescriptor)
  let y : DensePoly (Algebraic.Element first) := DensePoly.ofCoeffs #[0, 1]
  emitAssembly "nested algebraic multiplicities" Algebraic.Element.sign
    (fun a => .arr (a.polynomial.toArray.map rational))
    (nested * nested * (y - 1)) 10379 (some baseDescriptor)
  let cutFactor : DensePoly Rat := DensePoly.ofCoeffs #[3, -5, 2]
  emitAssemblyRat "assembly nonzero cut point" (cutFactor * cutFactor)
