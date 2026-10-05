/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.NumberFieldTower
public import HexRealClosure.RootFrame
public import HexNumberField.CommonField
public import HexNumberField.Nearest
public import HexSignDet.Codec

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)
private def rational (q : Rat) : Json := .arr #[Json.of q.num, Json.of q.den]
private def coordinates {a : AlgebraicNumber} (q : QAdjoin a) : Json :=
  .arr (q.coeffs.toArray.map rational)

private def encodeCell (context : Context registry) : Cell context → Json
  | .section root => object [("kind", .string "section"), ("root", context.codec.encode root)]
  | .sector lower upper => object [("kind", .string "sector"),
      ("lower", SignDet.Codec.endpoint context.codec lower),
      ("upper", SignDet.Codec.endpoint context.codec upper)]

private def encodeSample {parent : Context registry} (polynomials : List parent.Poly)
    (sample : Tower.Sample parent) : Json :=
  object [("context", sample.input.context.signature.literal.toJson),
    ("value", sample.input.context.codec.encode sample.value),
    ("cell", encodeCell sample.input.context sample.cell),
    ("polynomials", .arr (polynomials.toArray.map fun p =>
      .arr (p.toArray.map fun a => sample.input.context.codec.encode (sample.input.value a)))),
    ("signs", Json.of (sample.signs polynomials)),
    ("member", .bool (sample.cell.contains sample.value))]

private def emit (name : String) (generator : RealAlgebraicNumber)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic)))
    (inputs : Array (QAdjoin generator.toAlgebraic)) (boundaries : Nat) : IO Unit := do
  let some source := NumberField.present? generator registry
    | throw (IO.userError "number-field native presentation failed")
  let parent := source.context
  let packed := polynomials.map source.polynomial
  for a in inputs do
    let value := source.pack a
    unless parent.sign (source.pack (a+a) - (value+value)) == 0 &&
        parent.sign (source.pack (a*a) - value*value) == 0 &&
        parent.sign (source.pack a⁻¹ - value⁻¹) == 0 do
      throw (IO.userError "number-field packing lost arithmetic")
  unless source.roots 0 matches .all do
    throw (IO.userError "number-field zero lost universal roots")
  let family := source.family polynomials
  unless family.sections.length == boundaries && family.sectors.length == boundaries+1 do
    throw (IO.userError "number-field family lost a boundary or sector")
  for sample in family.sections ++ family.sectors do
    unless sample.cell.contains sample.value do
      throw (IO.userError "number-field sample membership failed")
    let .ok restored := (Catalog.empty registry).reconstruct sample.input.context.signature
      | throw (IO.userError "number-field sample context reconstruction failed")
    let packet := sample.input.context.write sample.value
    let .ok value := restored.val.read packet
      | throw (IO.userError "number-field sample value reconstruction failed")
    unless restored.val.sign value == sample.input.context.sign sample.value &&
        (restored.val.write value).value == packet.value do
      throw (IO.userError "number-field sample roundtrip changed its value")
  let some first := polynomials[0]? | throw (IO.userError "missing first sample polynomial")
  let some second := polynomials[1]? | throw (IO.userError "missing second sample polynomial")
  let repeated := first * first * second
  let .finite entries := source.roots repeated
    | throw (IO.userError "number-field repeated polynomial lost finite roots")
  let square := generator.toAlgebraic.rep.1.square
  let payload := object [("case", .string name),
    ("generator_head", .arr (generator.toAlgebraic.p.toArray.map Json.of)),
    ("generator_lower", rational (square.re-square.radiusHi).toRat),
    ("generator_upper", rational (square.re+square.radiusHi).toRat),
    ("inputs", .arr (inputs.map coordinates)),
    ("packed_inputs", .arr (inputs.map fun a => parent.codec.encode (source.pack a))),
    ("context", parent.signature.literal.toJson),
    ("original_polynomials", .arr (polynomials.toArray.map fun p => .arr (p.toArray.map coordinates))),
    ("polynomials", .arr (packed.toArray.map fun p => .arr (p.toArray.map parent.codec.encode))),
    ("sections", .arr (family.sections.toArray.map (encodeSample packed))),
    ("sectors", .arr (family.sectors.toArray.map (encodeSample packed))),
    ("repeated_roots", .arr (entries.toArray.map fun entry => object [
      ("multiplicity", Json.of entry.multiplicity),
      ("sample", encodeSample packed (Tower.Sample.ofRoot entry.root))]))]
  let some text := String.fromUTF8? payload.writeBytes
    | throw (IO.userError "number-field samples printer failed")
  IO.println text.trimAsciiEnd.toString

/-- Exercise original coordinates, native packing, shared samples and checked readers. -/
def main : IO Unit := do
  unless (RealAlgebraicNumber.ofAlgebraic? (ZPoly.rootNear #p[1,0,1] 0 0.9)).isNone do
    throw (IO.userError "nonreal generator entered a real presentation")
  let cubic : SignDet.RawDescriptor Rat Nat :=
    { context := 12, head := DensePoly.ofList [-2,0,0,1],
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let middle : SignDet.RawDescriptor Rat Nat :=
    { context := 13, head := DensePoly.ofList [1,-3,0,1],
      lower := .finite 0, upper := .finite 1, indices := [], signs := [] }
  for (name, raw) in [("cubic field", cubic), ("middle cubic field", middle)] do
    let some descriptor := Root.validate raw.context raw
      | throw (IO.userError "cubic field generator validation failed")
    let generator := descriptor.handle.canonical
    let a := generator.toAlgebraic.toQAdjoin
    let y : DensePoly (QAdjoin generator.toAlgebraic) := DensePoly.ofList [0,1]
    emit name generator [y*y-DensePoly.C a,y-1] #[a] 3
  let inputs := #[ZPoly.rootNear #p[-2,0,1] 1.4,ZPoly.rootNear #p[-3,0,1] 1.7]
  let common := QAdjoin.common inputs
  if real : common.generator.isReal = true then
    let generator := RealAlgebraicNumber.ofAlgebraic common.generator real
    let coordinates : Array (QAdjoin generator.toAlgebraic) := common.entries
    let some a := coordinates[0]? | throw (IO.userError "missing first common coordinate")
    let some b := coordinates[1]? | throw (IO.userError "missing second common coordinate")
    let y : DensePoly (QAdjoin generator.toAlgebraic) := DensePoly.ofList [0,1]
    emit "common quadratic fields" generator [y*y-DensePoly.C b,y-DensePoly.C a] coordinates 3
  else throw (IO.userError "common field generator is not real")
  let generator := RealAlgebraicNumber.ofRat 2
  emit "rational field" generator [DensePoly.C 1,DensePoly.C 2,0] #[1,2] 0
