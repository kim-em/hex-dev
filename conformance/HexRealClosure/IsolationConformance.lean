/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.CompleteRoots
public import HexRealClosure.AlgebraicContext
public import HexRealClosure.RootCollection
public import HexSignDet.Codec
public import HexOrderedFn.Infinitesimal

public section

open Hex Hex.RealClosure Hex.RealClosure.Isolation
open Hex.SignDet.Codec (Json)

private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

private def printJson (value : Json) : IO Unit := do
  let some text := String.fromUTF8? value.writeBytes
    | throw (IO.userError "JSON printer emitted invalid UTF-8")
  IO.println text.trimAsciiEnd.toString

private def rational (a : Rat) : Json := .arr #[Json.of a.num, Json.of a.den]

private def fraction (a : RationalFn Rat) : Json := object [
  ("num", .arr (a.num.toArray.map rational)), ("den", .arr (a.den.toArray.map rational))]

private def emit {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Neg E] [Inv E]
    (name : String) (depth : Nat) (sign : E → Int) (encode : E → Json)
    (p : DensePoly E) (context : Nat := 10378) (base : Option Json := none) : IO Unit := do
  let result := complete? sign context p
  let output := match result with
    | .error error => object [("error", .string (reprStr error))]
    | .ok none => .null
    | .ok (some completion) =>
      let route := match completion.search.route with
        | .whole stored => object [("kind", .string "whole"),
            ("head", .arr (stored.domain.head.toArray.map encode))]
        | .bounded bound frontier => object [("kind", .string "bounded"),
            ("bound", encode bound.value), ("nodes", Json.of frontier.nodes),
            ("head", .arr (frontier.head.toArray.map encode)),
            ("cells", .arr (frontier.cells.toArray.map fun cell => object [
              ("lower", encode cell.lower), ("upper", encode cell.upper),
              ("count", Json.of cell.count)]))]
      object [("route", route), ("points", .arr (completion.roots.points.toArray.map encode)),
        ("descriptors", .arr (completion.roots.descriptors.toArray.map fun d => object [
          ("context", Json.of d.raw.context),
          ("head", .arr (d.raw.head.toArray.map encode)),
          ("lower", SignDet.Codec.endpoint ⟨encode, fun _ => .error "encode only"⟩ d.raw.lower),
          ("upper", SignDet.Codec.endpoint ⟨encode, fun _ => .error "encode only"⟩ d.raw.upper),
          ("indices", Json.of d.raw.indices), ("signs", Json.of d.raw.signs)]))]
  let fields := [("case", .string name), ("depth", Json.of depth),
    ("head", .arr (p.toArray.map encode)), ("output", output)]
  let fields := match base with
    | none => fields
    | some descriptor => ("base", descriptor) :: fields
  printJson (object fields)

private def emitRat := emit (depth := 0) (sign := Sturm.orderSign) (encode := rational)

private def emitAssembly {E : Type} [Zero E] [DecidableEq E] [One E] [Add E]
    [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
    (name : String) (sign : E → Int) (encode : E → Json) (p : DensePoly E)
    (context : Nat := 10378) (base : Option Json := none) : IO Unit := do
  let output := match Roots.roots? sign context p with
    | .error error => object [("error", .string (reprStr error))]
    | .ok .all => object [("kind", .string "all")]
    | .ok (.finite entries) => object [("kind", .string "finite"),
        ("entries", .arr (entries.toArray.map fun entry =>
          let root := match entry.root with
            | .point value => object [("kind", .string "point"), ("value", encode value)]
            | .selected d => object [("kind", .string "selected"),
                ("context", Json.of d.raw.context),
                ("head", .arr (d.raw.head.toArray.map encode)),
                ("lower", SignDet.Codec.endpoint
                  ⟨encode, fun _ => .error "encode only"⟩ d.raw.lower),
                ("upper", SignDet.Codec.endpoint
                  ⟨encode, fun _ => .error "encode only"⟩ d.raw.upper),
                ("indices", Json.of d.raw.indices), ("signs", Json.of d.raw.signs)]
          object [("root", root), ("multiplicity", Json.of entry.multiplicity)]))]
  let fields := [("case", .string name), ("mode", .string "assembly"),
    ("head", .arr (p.toArray.map encode)), ("output", output)]
  let fields := match base with
    | none => fields
    | some descriptor => ("base", descriptor) :: fields
  printJson (object fields)

private def emitAssemblyRat (name : String) (p : DensePoly Rat) : IO Unit :=
  emitAssembly name Sturm.orderSign rational p

private def emitCollection : IO Unit := do
  let registry : BaseContext.Registry := fun _ => none
  let base := Tower.Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let some first := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C two,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "collection first descriptor failed")
  let some last := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := DensePoly.scale three (x * x - DensePoly.C three),
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "collection nonmonic descriptor failed")
  let sources : List (Tower.Root base) :=
    [Tower.Root.ofSelection base (.selected first), .point 0,
      Tower.Root.ofSelection base (.selected last)]
  let some collection := base.collect? sources
    | throw (IO.userError "native shared-context collection failed")
  let [alpha, zero, beta] := collection.entries
    | throw (IO.userError "native collection source count changed")
  let shared := collection.input.context
  let sum := alpha.value + beta.value
  let inputs := collection.entries.toArray.map fun entry => object [
    ("context", entry.source.context.signature.literal.toJson),
    ("value", entry.source.context.codec.encode entry.source.value),
    ("mapped", shared.codec.encode entry.value),
    ("oldInverse", entry.source.context.codec.encode ((entry.source.value - 1)⁻¹)),
    ("mappedInverse", shared.codec.encode (entry.apply ((entry.source.value - 1)⁻¹)))]
  printJson (object [("case", .string "native common root contexts"),
    ("mode", .string "collection"), ("context", shared.signature.literal.toJson),
    ("inputs", .arr inputs), ("sum", shared.codec.encode sum),
    ("inverse", shared.codec.encode sum⁻¹),
    ("zero", shared.codec.encode zero.value),
    ("two", shared.codec.encode (collection.input.value two)),
    ("three", shared.codec.encode (collection.input.value three))])

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
  let baseDescriptor := object [
    ("context", Json.of firstRoot.raw.context),
    ("head", .arr (firstRoot.raw.head.toArray.map rational)),
    ("lower", SignDet.Codec.endpoint
      ⟨rational, fun _ => .error "encode only"⟩ firstRoot.raw.lower),
    ("upper", SignDet.Codec.endpoint
      ⟨rational, fun _ => .error "encode only"⟩ firstRoot.raw.upper),
    ("indices", Json.of firstRoot.raw.indices), ("signs", Json.of firstRoot.raw.signs)]
  let nested : DensePoly (Algebraic.Element first) := DensePoly.ofCoeffs #[-alpha, 0, 1]
  emit "nested algebraic coefficients" 1 Algebraic.Element.sign
    (fun a => .arr (a.polynomial.toArray.map rational)) nested 10379 (some baseDescriptor)
  let y : DensePoly (Algebraic.Element first) := DensePoly.ofCoeffs #[0, 1]
  emitAssembly "nested algebraic multiplicities" Algebraic.Element.sign
    (fun a => .arr (a.polynomial.toArray.map rational))
    (nested * nested * (y - 1)) 10379 (some baseDescriptor)
  let cutFactor : DensePoly Rat := DensePoly.ofCoeffs #[3, -5, 2]
  emitAssemblyRat "assembly nonzero cut point" (cutFactor * cutFactor)
  emitCollection
