/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Sample
public import HexRealClosure.RootFrame
public import HexSignDet.Codec

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

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

private def emit (name : String) (parent : Context registry) (polynomials : List parent.Poly) : IO Unit := do
  let family := Tower.Sample.family parent polynomials
  let sections := family.sections
  let sectors := family.sectors
  for sample in sections ++ sectors do
    unless sample.cell.contains sample.value do throw (IO.userError "sample conformance: membership failed")
    unless sample.input.context.signature.roots.length ≤ parent.signature.roots.length + 2 do
      throw (IO.userError "sample conformance: unrelated roots collected")
    let .ok restored := (Catalog.empty registry).reconstruct sample.input.context.signature
      | throw (IO.userError "sample conformance: context reconstruction failed")
    let packet := sample.input.context.write sample.value
    let .ok value := restored.val.read packet
      | throw (IO.userError "sample conformance: value reconstruction failed")
    unless restored.val.sign value == sample.input.context.sign sample.value &&
        (restored.val.write value).value == packet.value do
      throw (IO.userError "sample conformance: restored value changed")
  let payload := object [("case", .string name), ("context", parent.signature.literal.toJson),
    ("polynomials", .arr (polynomials.toArray.map fun p => .arr (p.toArray.map parent.codec.encode))),
    ("sections", .arr (sections.toArray.map (encodeSample polynomials))),
    ("sectors", .arr (sectors.toArray.map (encodeSample polynomials)))]
  let some text := String.fromUTF8? payload.writeBytes
    | throw (IO.userError "sample conformance: invalid JSON printer output")
  IO.println text.trimAsciiEnd.toString

/-- Export actual local sections and sectors, including their converted
coefficients, native values, complete contexts and computed sign vectors. -/
def main : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let q := x * x - DensePoly.C (1 + 1)
  emit "irrational duplicate roots" base [q, q * q]
  emit "irreducible cubic roots" base [x * x * x - DensePoly.C (1 + 1 + 1) * x + DensePoly.C 1]
  emit "mixed irrational roots" base [q, q * (x * x - DensePoly.C (1 + 1 + 1))]
  emit "root-free whole line" base [DensePoly.C (1 + 1), 0]
  let staged := (BaseContext.rational registry).infinitesimal
  let inf := Context.base staged
  let epsilon : inf.Value := BaseContext.Element.infinitesimal (BaseContext.rational registry)
  let y : inf.Poly := DensePoly.ofCoeffs #[0, 1]
  emit "infinitesimal gap" inf [(y - DensePoly.C epsilon) * (y - DensePoly.C (epsilon + epsilon))]
  let some descriptor := SignDet.Descriptor.validate inf.sign inf.signature
      { context := inf.signature, head := y * y - DensePoly.C (1 + epsilon),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "sample conformance: selected parent failed")
  let parent := inf.adjoin descriptor
  let z : parent.context.Poly := DensePoly.ofCoeffs #[0, 1]
  emit "selected parent infinitesimal gap" parent.context
    [(z - DensePoly.C (1 : parent.context.Value)) * (z - DensePoly.C parent.generator)]
