/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots
public import HexRealClosure.LiveContext
public import HexRealClosure.SignCodec

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private abbrev base := Context.base (BaseContext.rational registry)

private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

private def emit (data : Json) : IO Unit := do
  let some text := String.fromUTF8? data.writeBytes | throw (IO.userError "invalid fixture UTF-8")
  IO.println text.trimAsciiEnd.toString
  (← IO.getStdout).flush

private def descriptor {parent : Context registry} (root : Tower.Root parent) : IO Json := do
  let .selected data _ _ := root | throw (IO.userError "expected a selected source root")
  unless data.raw.check parent.sign parent.signature data.evidence do
    throw (IO.userError "source selected-root replay failed")
  return Tower.rootData parent.codec data

private def withRoots (coefficients : List Int) (count : Nat)
    (use : List (Tower.RootEntry base) → IO Unit) : IO Unit := do
  let head : base.Poly := DensePoly.ofList
    (coefficients.map fun (coefficient : Int) => ⟨Rat.ofInt coefficient⟩)
  let .ok (.finite roots) := base.roots? head
    | throw (IO.userError "Strzeboński source root production failed")
  unless roots.length == count && roots.all (fun entry =>
      entry.multiplicity == 1 && entry.root.signAt head == 0) do
    throw (IO.userError "Strzeboński source root count, equation or multiplicity changed")
  for (left, right) in roots.zip roots.tail do
    unless left.root.compare right.root == .lt do
      throw (IO.userError "Strzeboński source roots are not ordered")
  use roots

private def withSquareRoot (constant : Int) (use : Tower.Root base → Json → IO Unit) : IO Unit :=
  withRoots [-constant, 0, 1] 2 fun roots => do
  let [_, positive] := roots | throw (IO.userError "Strzeboński square-root selection missing")
  unless positive.root.context.sign positive.root.value == 1 do
    throw (IO.userError "Strzeboński square-root selection is not positive")
  use positive.root (object [("constant", Json.of constant),
    ("roots", .arr (← roots.mapM fun entry => descriptor entry.root).toArray),
    ("multiplicities", Json.of (roots.map (·.multiplicity))),
    ("selected_index", Json.of (1 : Nat))])

private def rootJson {parent : Context registry} (entry : Tower.RootEntry parent) : IO Json := do
  let root ← match entry.root with
    | .point value => pure (object [("kind", .string "point"),
        ("value", parent.codec.encode value)])
    | .selected data _ _ => do
      unless data.raw.check parent.sign parent.signature data.evidence do
        throw (IO.userError "Strzeboński output replay failed")
      pure (object [("kind", .string "selected"),
        ("descriptor", Tower.rootData parent.codec data)])
  return object [("root", root), ("multiplicity", Json.of entry.multiplicity)]

private def runCase (number : Nat) (owner : Context registry) (head : owner.Poly)
    (inputs : Array Json) (sourceRoots : Array Json := #[]) : IO Unit := do
  let .ok (.finite roots) := owner.roots? head
    | throw (IO.userError "Strzeboński complete root production failed")
  unless roots.all (fun entry => entry.multiplicity > 0 && entry.root.signAt head == 0) do
    throw (IO.userError "Strzeboński output root equation failed")
  for (left, right) in roots.zip roots.tail do
    unless left.root.compare right.root == .lt do
      throw (IO.userError "Strzeboński complete roots are not strictly ordered")
  emit (object [("case", Json.of number),
    ("source", .string "4d26847955ecacaff4cadd0dce4550f125a726ea3f4e768d7aedd48ebcdaa7c4"),
    ("inputs", .arr inputs), ("source_roots", .arr sourceRoots),
    ("context", owner.signature.literal.toJson),
    ("head", .arr (head.toArray.map owner.codec.encode)),
    ("results", .arr (← roots.mapM rootJson).toArray)])

private def case2 : IO Unit :=
  withSquareRoot 2 fun r2 data2 =>
  withSquareRoot 3 fun r3 data3 => do
  let owners := [r2.context, r3.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners
    | throw (IO.userError "Strzeboński case 2 gathering failed")
  let owner := shared.input.context
  let a := shared.value ⟨0, by simp [owners]⟩ r2.value
  let b := shared.value ⟨1, by simp [owners]⟩ r3.value
  let sum := a + b
  runCase 2 owner (DensePoly.ofList [-1, a + Nat.cast 7, sum*sum*sum, 0, 0, 1]) #[data2, data3]

private def case3 : IO Unit :=
  withSquareRoot 7 fun root input => do
  let owner := root.context
  let a := root.value
  runCase 3 owner (DensePoly.ofList
    [-Nat.cast 11 + Nat.cast 3*a, 0, 0, a + Nat.cast 5, 0, 0, 0, 0, 0, 0, 1]) #[input]

private def case4 : IO Unit :=
  withRoots [-5, -7, 0, 1] 3 fun roots => do
  let [_, first, second] := roots | throw (IO.userError "Strzeboński cubic selections missing")
  let owners := [first.root.context, second.root.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners
    | throw (IO.userError "Strzeboński case 4 gathering failed")
  let owner := shared.input.context
  let a := shared.value ⟨0, by simp [owners]⟩ first.root.value
  let b := shared.value ⟨1, by simp [owners]⟩ second.root.value
  runCase 4 owner (DensePoly.ofList [b, a, 0, 1]) #[]
    (← roots.mapM fun entry => descriptor entry.root).toArray

/-- The executed cubic coefficient is 23 + 8√6. The original print label
instead says √5; the source's coefficient list governs this case. -/
private def case6 : IO Unit :=
  withSquareRoot 2 fun r2 data2 =>
  withSquareRoot 3 fun r3 data3 =>
  withSquareRoot 6 fun r6 data6 => do
  let owners := [r2.context, r3.context, r6.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners
    | throw (IO.userError "Strzeboński case 6 gathering failed")
  let owner := shared.input.context
  let a := shared.value ⟨0, by simp [owners]⟩ r2.value
  let b := shared.value ⟨1, by simp [owners]⟩ r3.value
  let c := shared.value ⟨2, by simp [owners]⟩ r6.value
  let n : Nat → owner.Value := Nat.cast
  runCase 6 owner (DensePoly.ofList [-n 10*a - n 8*b, n 38 + n 16*c,
    -(n 29*a - n 24*b), n 23 + n 8*c, -(n 5*a - n 2*b), 1]) #[data2, data3, data6]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["2"] => case2
  | ["3"] => case3
  | ["4"] => case4
  | ["6"] => case6
  | [] => do
    case2
    case3
    case4
    case6
  | _ => throw (IO.userError "usage: hexrealclosure_strz_conformance [2|3|4|6]")
  return 0
