/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRepr

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private def catalog : Catalog registry := Catalog.empty registry
private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)
private def emit (name reader representation wire : String) : IO Unit := do
  let .ok argument := ReprFormat.read reader representation
    | throw (IO.userError "canonical reconstruction expression failed")
  unless argument == wire do throw (IO.userError "quoted argument changed")
  let data := object [("case", .string name), ("reader", .string reader),
    ("representation", .string representation), ("packet_text", .string wire)]
  let some output := String.fromUTF8? data.writeBytes | throw (IO.userError "invalid output UTF-8")
  IO.println output.trimAsciiEnd.toString

private def element (name : String) (context : Context registry) (value : context.Value) : IO Unit := do
  let packed : PackedElement registry := ⟨context, value⟩
  unless reprStr packed == packed.reprText do throw (IO.userError "element formatter changed code")
  let .ok restored := catalog.readElementRepr (reprStr packed)
    | throw (IO.userError "printed element failed reconstruction")
  unless restored.writeText == packed.writeText do throw (IO.userError "printed element changed")
  emit name "restoreElementText" (reprStr packed) packed.writeText

private def polynomial (name : String) (context : Context registry) (value : context.Poly) : IO Unit := do
  let packed : PackedPolynomial registry := ⟨context, value⟩
  unless reprStr packed == packed.reprText do throw (IO.userError "polynomial formatter changed code")
  let .ok restored := catalog.readPolynomialRepr (reprStr packed)
    | throw (IO.userError "printed polynomial failed reconstruction")
  unless restored.writeText == packed.writeText do throw (IO.userError "printed polynomial changed")
  emit name "restorePolynomialText" (reprStr packed) packed.writeText

private def root (name : String) {parent : Context registry} (value : Tower.Root parent) : IO Unit := do
  unless reprStr value == value.reprText do throw (IO.userError "root formatter changed code")
  let .ok restored := catalog.readRootRepr (reprStr value)
    | throw (IO.userError "printed root failed reconstruction")
  unless restored.writeText == value.writeText do throw (IO.userError "printed root changed")
  emit name "restoreRootText" (reprStr value) value.writeText

private def roots (name : String) {parent : Context registry} (value : Tower.RootSet parent) : IO Unit := do
  unless reprStr value == value.reprText do throw (IO.userError "root-set formatter changed code")
  let .ok restored := catalog.readRootSetRepr (reprStr value)
    | throw (IO.userError "printed root set failed reconstruction")
  unless restored.writeText == value.writeText do throw (IO.userError "printed root set changed")
  emit name "restoreRootSetText" (reprStr value) value.writeText

private def rejection {α : Type u} (name expression : String) (result : Except String α) : IO Json := do
  let .error message := result | throw (IO.userError (name ++ " was accepted"))
  return object [("case", .string name), ("expression", .string expression), ("message", .string message)]

private def readerCode (name source : String) (policy : String := "limits") : String :=
  "(Hex.RealClosure.Tower.Catalog." ++ name ++ " catalog " ++ ReprFormat.quote source ++ " " ++ policy ++ ")"
private def parserCode (source : String) : String :=
  "(Hex.RealClosure.Tower.ReprFormat.read \"restoreRootText\" " ++ ReprFormat.quote source ++ " limits)"

private def failures : IO Unit := do
  let text := "[ [ [ ] , 0 , [ ] ] , [ 0 , [ 0 , 1 , 3 ] ] ]"
  let expression := ReprFormat.write "restoreRootText" text
  let missing := ReprFormat.header "restoreRootText" ++ ReprFormat.quote text
  let truncated := ReprFormat.header "restoreRootText" ++ "\"truncated" ++ ReprFormat.suffix
  let number := ReprFormat.header "restoreRootText" ++ "0" ++ ReprFormat.suffix
  let unknown := ReprFormat.write "restoreRootText"
    "[ [ [ [ \"missing\", 0 ] ] , 0 , [] ] , [0, [0,1,1]] ]"
  let invalid := ReprFormat.write "restoreRootText" "[ [ [] , 0 , [] ] , [0, [0,1,0]] ]"
  let unicodeBase : BaseContext.Signature := ⟨[{ name := "α\n\"\\λ𐐷", version := 17 }],0⟩
  let unicode : Serialized := ⟨⟨unicodeBase,[]⟩,
    .arr #[Json.of (0 : Int), .arr #[Json.of (0 : Int), Json.of (1 : Int), Json.of (1 : Int)]]⟩
  let escaped := ReprFormat.write "restoreRootText" unicode.writeText
  let noncanonical := ReprFormat.header "restoreRootText" ++ " " ++ ReprFormat.quote text ++ ReprFormat.suffix
  let checks ← [
    rejection "changed reader" (readerCode "readElementRepr" expression)
      (catalog.readElementRepr expression),
    rejection "missing policy" (parserCode missing) (ReprFormat.read "restoreRootText" missing),
    rejection "source byte limit" (readerCode "readRootRepr" expression "{ bytes := 1 }")
      (catalog.readRootRepr expression { bytes := 1 }),
    rejection "packet integer limit" (readerCode "readRootRepr" expression "{ digits := 0 }")
      (catalog.readRootRepr expression { digits := 0 }),
    rejection "truncated literal" (parserCode truncated) (ReprFormat.read "restoreRootText" truncated),
    rejection "wrong literal type" (parserCode number) (ReprFormat.read "restoreRootText" number),
    rejection "unknown provider" unknown (catalog.restoreRootText
      "[ [ [ [ \"missing\", 0 ] ] , 0 , [] ] , [0, [0,1,1]] ]"),
    rejection "invalid stored point" invalid
      (catalog.restoreRootText "[ [ [] , 0 , [] ] , [0, [0,1,0]] ]"),
    rejection "escaped unknown provider" escaped (catalog.restoreRootText unicode.writeText),
    rejection "noncanonical expression" (parserCode noncanonical)
      (ReprFormat.read "restoreRootText" noncanonical)].mapM id
  let some output := String.fromUTF8? (object [("case", .string "checked reconstruction failures"),
    ("rejections", .array (checks.foldr Json.Values.cons .nil))]).writeBytes
    | throw (IO.userError "invalid failure UTF-8")
  IO.println output.trimAsciiEnd.toString

private def literals : IO Unit := do
  let values := ["\"", "\\", "\u0001", "λ𐐷", "\\u0001"]
  let entries := values.map fun value => object [("quoted", .string (ReprFormat.quote value)),
    ("codepoints", Json.of (value.toList.map Char.toNat))]
  let some output := String.fromUTF8? (object [("case", .string "escaped Lean literals"),
    ("literals", .array (entries.foldr Json.Values.cons .nil))]).writeBytes
    | throw (IO.userError "invalid literal UTF-8")
  IO.println output.trimAsciiEnd.toString

/-- Standard Repr rendering and checked reconstruction of actual native objects. -/
def main : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofList [0,1]
  element "rational value" base (1/(1+1+1))
  polynomial "rational polynomial" base (x*x-DensePoly.C (1+1))
  root "point root" (Tower.Root.point (parent := base) (1/(1+1+1)))
  roots "universal roots" (base.roots 0)
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := (x*x-DensePoly.C (1+1))*(x-DensePoly.C (1+1+1)),
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "reducible root failed")
  let extension := base.adjoin descriptor
  let selected : Tower.Root base := .selected descriptor extension rfl
  root "selected reducible root" selected
  element "split inverse" extension.context (extension.generator-(1+1+1))⁻¹
  let y : extension.context.Poly := DensePoly.ofList [0,1]
  polynomial "algebraic polynomial" extension.context (y*y-DensePoly.C extension.generator)
  let some nested := SignDet.Descriptor.validate extension.context.sign extension.context.signature
      { context := extension.context.signature, head := y*y-DensePoly.C extension.generator,
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "nested root failed")
  let child := extension.context.adjoin nested
  root "nested root" (Tower.Root.selected nested child rfl)
  roots "nested root multiplicity" (Tower.RootSet.finite (parent := extension.context)
    [⟨.selected nested child rfl, 3, by decide⟩])
  let inf := Context.base (BaseContext.rational registry).infinitesimal.infinitesimal
  let epsilon : inf.Value := BaseContext.Element.infinitesimal
    (BaseContext.rational registry).infinitesimal
  element "successive infinitesimal" inf epsilon⁻¹
  root "infinitesimal point" (Tower.Root.point (parent := inf) epsilon)
  failures
  literals
