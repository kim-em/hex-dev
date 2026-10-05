/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootBytes
public import HexSignDet.Codec.Bytes

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)
private def packet (data : Serialized) : Json := .arr #[data.binding.literal.toJson, data.value]
private def printJson (data : Json) : IO Unit := do
  let some text := String.fromUTF8? data.writeBytes | throw (IO.userError "invalid printed UTF-8")
  IO.println text.trimAsciiEnd.toString

private def rejection {α : Type u} (name : String) (result : Except String α)
    (expected : Option String := none) : IO Json := do
  match result with
  | .ok _ => throw (IO.userError s!"{name}: invalid root data accepted")
  | .error message =>
    if let some exact := expected then
      unless message == exact do
        throw (IO.userError s!"{name}: unexpected rejection {message}")
    return object [("case", .string name), ("message", .string message)]

private def checkRoot (parent : Context registry) (root : Tower.Root parent) : IO Unit := do
  let .ok original := parent.readRootBytes root.writeBytes
    | throw (IO.userError "root failed in its original predecessor")
  let .ok fresh := (Catalog.empty registry).restoreRootText root.writeText
    | throw (IO.userError "root failed with a fresh catalog")
  unless original.data == root.data && fresh.parent.signature == parent.signature &&
      fresh.root.data == root.data && fresh.root.context.signature == root.context.signature &&
      fresh.root.context.codec.encode fresh.root.value == root.context.codec.encode root.value &&
      fresh.root.context.sign fresh.root.value == root.context.sign root.value do
    throw (IO.userError "root kind, owner or selected value changed")

private def emit (name : String) (parent : Context registry) (roots : Tower.RootSet parent)
    (checks : Array Json := #[]) : IO Unit := do
  let .ok original := parent.readRootSetText roots.writeText
    | throw (IO.userError "root set failed in its original predecessor")
  let .ok fresh := (Catalog.empty registry).restoreRootSetBytes roots.writeBytes
    | throw (IO.userError "root set failed with a fresh catalog")
  unless original.data == roots.data && fresh.parent.signature == parent.signature &&
      fresh.roots.data == roots.data do
    throw (IO.userError "root-set kind, multiplicities or literal order changed")
  match roots with
  | .all => pure ()
  | .finite entries => for entry in entries do checkRoot parent entry.root
  printJson (object [("case", .string name), ("packet", packet roots.write),
    ("packet_text", .string roots.writeText),
    ("root_texts", match roots with
      | .all => .arr #[]
      | .finite entries => .arr (entries.toArray.map fun entry => .string entry.root.writeText)),
    ("reconstructed", packet fresh.roots.write), ("rejections", .arr checks)])

/-- Full root kinds, fresh parent reconstruction and complete finite/universal results. -/
def main : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofList [0,1]
  let point : Tower.Root base := .point (1/(1+1+1))
  checkRoot base point
  let mut bad := #[]
  bad := bad.push (← rejection "unknown root kind" (base.readRoot (.arr #[Json.of (2 : Nat), .arr #[]]))
    (some "unknown root kind"))
  bad := bad.push (← rejection "unknown root-set kind"
    (base.readRootSet (.arr #[Json.of (2 : Nat), .arr #[]])) (some "unknown root-set kind"))
  bad := bad.push (← rejection "nonempty universal roots"
    (base.readRootSet (.arr #[Json.of (0 : Nat), .arr #[Json.of (0 : Nat)]]))
    (some "nonempty universal root payload"))
  bad := bad.push (← rejection "zero multiplicity"
    (base.readRootEntry (.arr #[point.data, Json.of (0 : Nat)]))
    (some "nonpositive root multiplicity"))
  bad := bad.push (← rejection "malformed point"
    (base.readRoot (.arr #[Json.of (0 : Nat), .string "not a coefficient"])))
  let stale : Serialized := ⟨(Context.base (BaseContext.rational registry).infinitesimal).signature,
    point.data⟩
  bad := bad.push (← rejection "stale root predecessor" (base.readRootPacket stale)
    (some "root predecessor mismatch"))
  bad := bad.push (← rejection "stale root-set predecessor" (base.readRootSetPacket stale)
    (some "root-set predecessor mismatch"))
  bad := bad.push (← rejection "invalid root UTF-8" (base.readRootBytes (ByteArray.mk #[255]))
    (some "invalid certificate JSON or UTF-8"))
  bad := bad.push (← rejection "root byte limit" (base.readRootBytes point.writeBytes { bytes := 0 })
    (some "certificate byte limit exceeded"))
  bad := bad.push (← rejection "root-set nesting limit"
    (base.readRootSetBytes (Tower.RootSet.all (parent := base)).writeBytes { depth := 0 })
    (some "certificate nesting limit exceeded"))
  bad := bad.push (← rejection "root-set truncation" (base.readRootSetText "[")
    (some "truncated certificate syntax"))
  let unknown : Serialized := ⟨⟨⟨[{ name := "missing", version := 7 }], 0⟩, []⟩, point.data⟩
  bad := bad.push (← rejection "unknown validated provider"
    ((Catalog.empty registry).restoreRootBytes unknown.writeBytes) (some "unknown validated base"))
  emit "universal roots" base (base.roots 0) bad
  emit "empty finite roots" base (base.roots (DensePoly.C 1))
  emit "literal point order" base (.finite [⟨.point (1+1), 3, by decide⟩,
    ⟨point, 2, by decide⟩])
  let head := (x*x-DensePoly.C (1+1))*(x-DensePoly.C (1+1+1))
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := head, lower := .finite 1, upper := .finite (1+1),
        indices := [], signs := [] }
    | throw (IO.userError "selected reducible root failed")
  let extension := base.adjoin descriptor
  let selected : Tower.Root base := .selected descriptor extension rfl
  checkRoot base selected
  let .ok fields := extension.frame.toJson.getArr? | throw (IO.userError "missing frame fields")
  let mut rejected := #[]
  for (name, index, replacement) in [("changed head", 1, Json.arr #[]),
      ("changed lower endpoint", 2, Json.arr #[Json.of (0 : Nat)]),
      ("changed Thom indices", 4, Json.arr #[Json.of (99 : Nat)]),
      ("changed Thom signs", 5, Json.arr #[Json.of (2 : Int)]),
      ("missing replay graph", 6, Json.arr #[])] do
    let changed := Json.arr (fields.set! index replacement)
    rejected := rejected.push (← rejection name
      (base.readRoot (.arr #[Json.of (1 : Nat), changed])))
  emit "selected reducible root" base (.finite [⟨selected, 2, by decide⟩]) rejected
  let parent := extension.context
  let y : parent.Poly := DensePoly.ofList [0,1]
  let some nested := SignDet.Descriptor.validate parent.sign parent.signature
      { context := parent.signature, head := y*y-DensePoly.C extension.generator,
        lower := .finite 1, upper := .finite (1+1), indices := [], signs := [] }
    | throw (IO.userError "nested selected root failed")
  let child := parent.adjoin nested
  let root : Tower.Root parent := .selected nested child rfl
  emit "fresh algebraic predecessor" parent (.finite [⟨root, 3, by decide⟩,
    ⟨.point ((extension.generator-(1+1+1))⁻¹), 1, by decide⟩])
  let q := x*x-DensePoly.C (1+1)
  let linear := x-DensePoly.C (1+1+1)
  let repeated := x*x*q*q*q*linear*linear*linear*linear
  let .ok roots := base.roots? repeated | throw (IO.userError "complete repeated roots failed")
  let .finite entries := roots | throw (IO.userError "repeated polynomial returned all")
  unless entries.map (·.multiplicity) == [3,2,3,4] do
    throw (IO.userError "complete producer lost multiplicities")
  for entry in entries do
    unless entry.root.signAt repeated == 0 do
      throw (IO.userError "produced root does not annul its polynomial")
  emit "complete repeated roots" base roots
