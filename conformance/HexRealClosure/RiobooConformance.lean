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
  let .selected data _ _ := root | throw (IO.userError "expected a selected algebraic root")
  unless data.raw.check parent.sign parent.signature data.evidence do
    throw (IO.userError "selected-root replay failed")
  return Tower.rootData parent.codec data

private def rationalHead (coefficients : List Int) : base.Poly :=
  DensePoly.ofList (coefficients.map fun (coefficient : Int) => ⟨Rat.ofInt coefficient⟩)

private def withRoots (coefficients : List Int) (count : Nat)
    (use : List (Tower.RootEntry base) → IO Unit) : IO Unit := do
  let head := rationalHead coefficients
  let .ok (.finite roots) := base.roots? head
    | throw (IO.userError "Rioboo complete root production failed")
  unless roots.length == count && roots.all (fun entry =>
      entry.multiplicity == 1 && entry.root.signAt head == 0) do
    throw (IO.userError "Rioboo root count, equation or multiplicity changed")
  for (left, right) in roots.zip roots.tail do
    unless left.root.compare right.root == .lt do
      throw (IO.userError "Rioboo roots are not strictly ordered")
  use roots

/-- Original `rioboo1.py`: select the third and fourth roots of the actual
quartic, retain both immutable owners, and compute in their checked common field. -/
private def rioboo1 : IO Unit :=
  withRoots [1, 0, -10, 0, 1] 4 fun roots => do
  let head : List Int := [1, 0, -10, 0, 1]
  let [_, _, first, second] := roots | throw (IO.userError "Rioboo quartic selections missing")
  let owners := [first.root.context, second.root.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners
    | throw (IO.userError "Rioboo quartic owner gathering failed")
  let owner := shared.input.context
  let a := shared.value ⟨0, by simp [owners]⟩ first.root.value
  let b := shared.value ⟨1, by simp [owners]⟩ second.root.value
  let half := (a + b) / (Nat.cast 2 : owner.Value)
  let square := half * half
  let values := #[a, b, half, square, square - Nat.cast 3]
  let signs := values.map owner.sign
  unless signs == #[1, 1, 1, 1, 0] do
    throw (IO.userError "Rioboo quartic arithmetic identity failed")
  emit (object [("case", .string "cade24 rioboo1"),
    ("source", .string "51dee2d698ebe39a267d642b35d2197936739517234cd0be7039fe2ee2c5eba7"),
    ("head", Json.of head),
    ("roots", .arr (← roots.mapM fun entry => descriptor entry.root).toArray),
    ("multiplicities", Json.of (roots.map (·.multiplicity))),
    ("selected_indices", Json.of ([2, 3] : List Nat)),
    ("context", owner.signature.literal.toJson),
    ("values", .arr (values.map owner.codec.encode)), ("signs", Json.of signs.toList)])

private def withSquareRoot (constant : Int) (use : Tower.Root base → Json → IO Unit) : IO Unit :=
  withRoots [-constant, 0, 1] 2 fun roots => do
  let [_, positive] := roots | throw (IO.userError "Rioboo square-root selection missing")
  unless positive.root.context.sign positive.root.value == 1 do
    throw (IO.userError "Rioboo square-root selection is not positive")
  use positive.root (object [("constant", Json.of constant),
    ("roots", .arr (← roots.mapM fun entry => descriptor entry.root).toArray),
    ("multiplicities", Json.of (roots.map (·.multiplicity))),
    ("selected_index", Json.of (1 : Nat))])

/-- Original `rioboo2.py`: four independently selected square roots enter one
checked target before evaluating the strict comparison and square identity. -/
private def rioboo2 : IO Unit := do
  withSquareRoot 28 fun r28 data28 =>
  withSquareRoot 82 fun r82 data82 =>
  withSquareRoot 33 fun r33 data33 =>
  withSquareRoot 74 fun r74 data74 =>
  withSquareRoot 28 fun again dataAgain => do
  let owners := [r28.context, r82.context, r33.context, r74.context, again.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners
    | throw (IO.userError "Rioboo radical owner gathering failed")
  let owner := shared.input.context
  let a := shared.value ⟨0, by simp [owners]⟩ r28.value
  let b := shared.value ⟨1, by simp [owners]⟩ r82.value
  let c := shared.value ⟨2, by simp [owners]⟩ r33.value
  let d := shared.value ⟨3, by simp [owners]⟩ r74.value
  let repeated := shared.value ⟨4, by simp [owners]⟩ again.value
  let left := a + b
  let right := c + d
  let values := #[a, b, c, d, left, right, left - right,
    repeated, repeated*repeated, repeated*repeated - Nat.cast 28]
  let signs := values.map owner.sign
  unless signs == #[1, 1, 1, 1, 1, 1, -1, 1, 1, 0] do
    throw (IO.userError "Rioboo radical comparison or square identity failed")
  emit (object [("case", .string "cade24 rioboo2"),
    ("source", .string "2c13ac14e1c8783d1aaf88e56ee6ee5d40ebc730f19759b2b17321a722a70936"),
    ("inputs", .arr #[data28, data82, data33, data74, dataAgain]),
    ("context", owner.signature.literal.toJson),
    ("values", .arr (values.map owner.codec.encode)), ("signs", Json.of signs.toList)])

def main : IO Unit := do
  rioboo1
  rioboo2
