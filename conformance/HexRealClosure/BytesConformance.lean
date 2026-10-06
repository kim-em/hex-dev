/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerBytes
public import HexRealClosure.FrameFormat

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)
private def text (bytes : ByteArray) : IO String := do
  let some value := String.fromUTF8? bytes | throw (IO.userError "invalid printed UTF-8")
  return value.trimAsciiEnd.toString

private def emit (name : String) (context : Context registry) (a : context.Value)
    (p : context.Poly) : IO Unit := do
  let bytes := context.writeBytes a
  let polyBytes := context.writePolyBytes p
  let .ok value := context.readBytes bytes | throw (IO.userError "printed value failed to read")
  let .ok polynomial := context.readPolyBytes polyBytes
    | throw (IO.userError "printed polynomial failed to read")
  let .ok textValue := context.readText (context.writeText a)
    | throw (IO.userError "printed text value failed to read")
  let .ok textPoly := context.readPolyText (context.writePolyText p)
    | throw (IO.userError "printed text polynomial failed to read")
  unless context.writeBytes value == bytes && context.sign value == context.sign a &&
      context.writePolyBytes polynomial == polyBytes && context.writeBytes textValue == bytes &&
      context.writePolyBytes textPoly == polyBytes do
    throw (IO.userError "printed data changed")
  let printedValue : PackedElement registry := ⟨context,a⟩
  let printedPoly : PackedPolynomial registry := ⟨context,p⟩
  let .ok restored := (Catalog.empty registry).restoreElementText printedValue.writeText
    | throw (IO.userError "printed context failed reconstruction")
  let .ok restoredPoly := (Catalog.empty registry).restorePolynomialText printedPoly.writeText
    | throw (IO.userError "printed polynomial context failed reconstruction")
  unless restored.context.writeBytes restored.value == bytes && restored.sign == context.sign a &&
      restoredPoly.context.writePolyBytes restoredPoly.value == polyBytes do
    throw (IO.userError "printed reconstruction changed data")
  let staleBase := { context.signature.base with
    infinitesimals := context.signature.base.infinitesimals+1 }
  let stale : Serialized := ⟨⟨staleBase,context.signature.roots⟩,(context.write a).value⟩
  unless context.readBytes stale.writeBytes matches .error "context binding mismatch" do
    throw (IO.userError "stale printed binding accepted")
  let forged : Serialized := ⟨context.signature,.string "not a coefficient"⟩
  unless context.readBytes forged.writeBytes matches .error _ do
    throw (IO.userError "malformed coefficient accepted")
  let trailing : Serialized := ⟨context.signature,
    .arr ((p.toArray.map context.codec.encode).push (context.codec.encode 0))⟩
  unless context.readPolyBytes trailing.writeBytes matches .error "noncanonical polynomial vector" do
    throw (IO.userError "trailing polynomial zero accepted")
  unless context.readBytes (ByteArray.mk #[255]) matches .error "invalid certificate JSON or UTF-8" do
    throw (IO.userError "invalid UTF-8 accepted")
  unless context.readBytes "[".toUTF8 matches .error "truncated certificate syntax" do
    throw (IO.userError "truncated syntax accepted")
  unless context.readBytes bytes { bytes := 0 } matches .error "certificate byte limit exceeded" do
    throw (IO.userError "byte policy ignored")
  unless context.readBytes bytes { depth := 0 } matches .error "certificate nesting limit exceeded" do
    throw (IO.userError "depth policy ignored")
  unless context.readBytes bytes { digits := 0 } matches .error "integer token limit exceeded" do
    throw (IO.userError "digit policy ignored")
  let payload := object [("case", .string name),
    ("value_text", .string (context.writeText a)), ("value_json", Serialized.codec.encode (context.write a)),
    ("polynomial_text", .string (context.writePolyText p)),
    ("polynomial_json", Serialized.codec.encode (context.writePoly p)),
    ("sign", Json.of (context.sign a)), ("roundtrip", .bool true),
    ("reconstructed", .bool true), ("rejections", Json.of (8 : Nat))]
  IO.println (← text payload.writeBytes)

/-- Actual printed arithmetic, recursive contexts, replay graphs and rejection paths. -/
def main : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofList [0,1]
  let point : Tower.Root base := .point (1/(1+1+1))
  let .ok pointValue := point.context.readText (point.writeValueText)
    | throw (IO.userError "printed point root failed")
  unless point.context.writeBytes pointValue == point.writeValueBytes do
    throw (IO.userError "printed point root changed")
  emit "rational bytes" base (1/(1+1+1)) (x*x-DensePoly.C (1+1))
  let head := (x*x-DensePoly.C (1+1))*(x-DensePoly.C (1+1+1))
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := head, lower := .finite 1, upper := .finite (1+1),
        indices := [], signs := [] }
    | throw (IO.userError "selected reducible root failed")
  let extension := base.adjoin descriptor
  let selected : Tower.Root base := .selected descriptor extension rfl
  let .ok selectedValue := selected.context.readText (selected.writeValueText)
    | throw (IO.userError "printed selected root failed")
  unless selected.context.writeBytes selectedValue == selected.writeValueBytes do
    throw (IO.userError "printed selected root changed")
  let parent := extension.context
  let y : parent.Poly := DensePoly.ofList [0,1]
  emit "reducible inverse bytes" parent (extension.generator-(1+1+1))⁻¹
    (y*y-DensePoly.C extension.generator)
  let some nested := SignDet.Descriptor.validate parent.sign parent.signature
      { context := parent.signature, head := y*y-DensePoly.C extension.generator,
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "nested selected root failed")
  let child := parent.adjoin nested
  let z : child.context.Poly := DensePoly.ofList [0,1]
  emit "nested root bytes" child.context (child.generator+child.embed extension.generator)
    (z*z-DensePoly.C (child.embed extension.generator))
  let ordered := (BaseContext.rational registry).infinitesimal.infinitesimal
  let inf := Context.base ordered
  let epsilon : inf.Value := BaseContext.Element.infinitesimal
    (BaseContext.rational registry).infinitesimal
  let u : inf.Poly := DensePoly.ofList [0,1]
  emit "successive infinitesimal bytes" inf epsilon⁻¹ (u-DensePoly.C epsilon)
  let unicodeBase : BaseContext.Signature :=
    ⟨[{ name := "α\n\"\\λ", version := 17 }],2⟩
  let unicode : Serialized := ⟨⟨unicodeBase,[]⟩,.string "\u0000\nλ𐐷\"\\"⟩
  let .ok reread := Serialized.readBytes unicode.writeBytes
    | throw (IO.userError "Unicode binding failed to parse")
  unless reread.writeBytes == unicode.writeBytes do
    throw (IO.userError "Unicode binding changed")
  unless (Catalog.empty registry).restoreElementBytes unicode.writeBytes matches .error _ do
    throw (IO.userError "unknown Unicode provider accepted")
  IO.println (← text (object [("case",.string "Unicode provider binding"),
    ("value_text",.string unicode.writeText),
    ("value_json",Serialized.codec.encode unicode), ("unknown_rejected",.bool true)]).writeBytes)
