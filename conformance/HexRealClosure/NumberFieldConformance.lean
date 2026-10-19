/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexNumberField.CommonField
public import HexNumberField.Nearest
public import HexRealClosure.NumberField
public import HexRealClosure.QAdjoin
public import HexRealClosure.Algebraic
public import HexSignDet.Codec

public section

open Hex Hex.RealClosure
open Hex.SignDet.Codec (Json)

private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

private def rational (a : Rat) : Json := .arr #[Json.of a.num, Json.of a.den]

private def coordinate {generator : AlgebraicNumber} (a : QAdjoin generator) : Json :=
  .arr (a.coeffs.toArray.map rational)

private def printJson (value : Json) : IO Unit := do
  let some text := String.fromUTF8? value.writeBytes
    | throw (IO.userError "JSON printer emitted invalid UTF-8")
  IO.println text.trimAsciiEnd.toString

private def entryJson (generator : RealAlgebraicNumber) (context : Nat)
    (queries : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (entry : Roots.Entry generator.signField context) : IO Json := do
  let result : Json × List Int ← match entry.root with
    | .point value => do
      pure (object [("kind", .string "point"), ("value", coordinate value)],
          queries.map fun p => generator.signField (p.eval value))
    | .selected d => do
      let .ok signs := d.buildSigns queries
        | throw (IO.userError "number-field selected query failed")
      let extension := Algebraic.Context.adjoin d (fun _ => false)
      let beta : Algebraic.Element extension := Algebraic.Element.ofPoly (DensePoly.ofList [0, 1])
      let shifted := beta - 3
      unless Algebraic.Element.sign (shifted * shifted⁻¹ - 1) == 0 do
        throw (IO.userError "number-field selected inverse lost its value")
      pure (object [
        ("kind", .string "selected"), ("context", Json.of d.raw.context),
        ("head", .arr (d.raw.head.toArray.map coordinate)),
        ("lower", SignDet.Codec.endpoint ⟨coordinate, fun _ => .error "encode only"⟩ d.raw.lower),
        ("upper", SignDet.Codec.endpoint ⟨coordinate, fun _ => .error "encode only"⟩ d.raw.upper),
        ("indices", Json.of d.raw.indices), ("signs", Json.of d.raw.signs),
        ("generator_sign", Json.of (Algebraic.Element.sign beta)),
        ("inverse_sign", Json.of (Algebraic.Element.sign shifted⁻¹)),
        ("inverse_shift_sign", Json.of (Algebraic.Element.sign (shifted⁻¹ + Algebraic.Element.ofPoly
          (DensePoly.C (1 / 2 : QAdjoin generator.toAlgebraic))))),
        ("inverse_identity_sign", Json.of (Algebraic.Element.sign (shifted * shifted⁻¹ - 1)))],
        signs.values.toList)
  let (root, signs) := result
  return object [("root", root), ("multiplicity", Json.of entry.multiplicity),
    ("query_signs", Json.of signs)]

private def emit (generator : RealAlgebraicNumber) (name : String)
    (p : DensePoly (QAdjoin generator.toAlgebraic))
    (queries : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (inputs : Array AlgebraicNumber := #[])
    (coordinates : Array (QAdjoin generator.toAlgebraic) := #[]) : IO Unit := do
  let context := 10378
  let output := NumberField.roots generator context p
  let output ← match output with
    | .all => pure (object [("kind", .string "all")])
    | .finite entries => do
      for (left, right) in entries.zip entries.tail do
        unless left.root.compare right.root matches .ok .lt do
          throw (IO.userError "number-field roots are not strictly ordered")
      let entries ← entries.mapM (entryJson generator context queries)
      pure (object [("kind", .string "finite"), ("entries", .arr entries.toArray)])
  let square := generator.toAlgebraic.rep.1.square
  printJson (object [("case", .string name), ("context", Json.of context),
    ("generator_head", .arr (generator.toAlgebraic.p.toArray.map Json.of)),
    ("generator_sign", Json.of generator.sign),
    ("generator_lower", rational (square.re - square.radiusHi).toRat),
    ("generator_upper", rational (square.re + square.radiusHi).toRat),
    ("inputs", .arr (inputs.map fun a =>
      let square := a.rep.1.square
      object [("head", .arr (a.p.toArray.map Json.of)),
        ("lower", rational (square.re - square.radiusHi).toRat),
        ("upper", rational (square.re + square.radiusHi).toRat)])),
    ("coordinates", .arr (coordinates.map coordinate)),
    ("head", .arr (p.toArray.map coordinate)),
    ("queries", .arr (queries.toArray.map fun p => .arr (p.toArray.map coordinate))),
    ("output", output)])

def main : IO Unit := do
  let raw : SignDet.RawDescriptor Rat Nat :=
    { context := 12, head := DensePoly.ofList [-2, 0, 0, 1],
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let some descriptor := Root.validate 12 raw
    | throw (IO.userError "cubic generator validation failed")
  let generator := descriptor.handle.canonical
  let alpha := generator.toAlgebraic.toQAdjoin
  let x : DensePoly (QAdjoin generator.toAlgebraic) := DensePoly.ofList [0, 1]
  let quadratic := x*x - DensePoly.C alpha
  let queries := [x, x - 1, quadratic, x - DensePoly.C alpha]
  emit generator "cubic-field zero" 0 queries
  emit generator "cubic-field repeated roots" (quadratic*quadratic*(x-1)) queries
  emit generator "cubic-field nonmonic roots" (DensePoly.scale (-2) (quadratic*quadratic*(x-1))) queries

  let middleRaw : SignDet.RawDescriptor Rat Nat :=
    { context := 13, head := DensePoly.ofList [1, -3, 0, 1],
      lower := .finite 0, upper := .finite 1, indices := [], signs := [] }
  let some middleDescriptor := Root.validate 13 middleRaw
    | throw (IO.userError "middle cubic generator validation failed")
  let middle := middleDescriptor.handle.canonical
  let gamma := middle.toAlgebraic.toQAdjoin
  let y : DensePoly (QAdjoin middle.toAlgebraic) := DensePoly.ofList [0, 1]
  let q := y*y - DensePoly.C gamma
  emit middle "middle cubic embedding" (q*q*(y-1)) [y, y-1, q, y-DensePoly.C gamma]

  let inputs := #[ZPoly.rootNear #p[-2, 0, 1] 1.4, ZPoly.rootNear #p[-3, 0, 1] 1.7]
  let common := QAdjoin.common inputs
  if real : common.generator.isReal = true then
    let generator := RealAlgebraicNumber.ofAlgebraic common.generator real
    let coordinates : Array (QAdjoin generator.toAlgebraic) := common.entries
    let some a := coordinates[0]? | throw (IO.userError "missing quadratic coordinate")
    let some b := coordinates[1]? | throw (IO.userError "missing second coordinate")
    let y : DensePoly (QAdjoin generator.toAlgebraic) := DensePoly.ofList [0, 1]
    let quadratic := y*y - DensePoly.C b
    emit generator "common quadratic fields with zero root"
      (y*y*y * quadratic*quadratic*(y-DensePoly.C a))
      [y, y-1, quadratic, y-DensePoly.C a] inputs coordinates
  else throw (IO.userError "common generator is not real")
