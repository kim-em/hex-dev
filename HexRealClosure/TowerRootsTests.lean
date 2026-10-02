/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots
public import HexRealClosure.TowerOrder

public section

namespace Hex.RealClosure.Tower.RootTests

private def registry : BaseContext.Registry := fun _ => none

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def check {parent : Context registry} (p : DensePoly parent.Value)
    (labels : List Nat) : IO Unit := do
  let .ok (.finite entries) := parent.roots? p
    | throw (IO.userError "native checked roots failed or returned all")
  require (entries.map (·.multiplicity) == labels) "native root labels changed"
  for entry in entries do
    let root := entry.root
    require (root.signAt p == 0) "native root value is not a root after coefficient embedding"
    require (root.context.sign (root.embed 1 - 1) == 0) "native coefficient embedding changed one"
    require (root.context.sign (root.embed 0) == 0) "native coefficient embedding changed zero"
    let conversion := root.conversion
    let composed := conversion.comp (Conversion.identity conversion.context)
    require (composed.context.sign (composed.value 1 - 1) == 0)
      "composed native root inclusion changed one"
    let z : DensePoly conversion.context.Value := DensePoly.ofCoeffs #[0, 1]
    let some descriptor := SignDet.Descriptor.validate conversion.context.sign
        conversion.context.signature
        { context := conversion.context.signature, head := z - DensePoly.C (conversion.value 1),
          lower := .negInf, upper := .posInf, indices := [], signs := [] }
      | throw (IO.userError "later root inclusion validation failed")
    let child := conversion.context.adjoin descriptor
    let next := Conversion.includeRoot conversion.context descriptor child rfl
    let transported := conversion.comp next
    require (transported.context.sign (transported.value 1 - 1) == 0)
      "later native root inclusion changed coefficients"
    require (next.context.sign (next.value root.convertedValue) == root.context.sign root.value)
      "later native root inclusion changed the selected value"
    if root.context.sign root.value != 0 then
      require (root.context.sign (root.value * root.value⁻¹ - 1) == 0)
        "native selected root arithmetic failed"
    match root with
    | .point _ =>
      require (decide (root.context.signature = parent.signature)) "point extended its context"
    | .selected _ extension _ =>
      require (decide (extension.context.signature = parent.signature.extend extension.frame))
        "selected root lost its predecessor binding"
  for (left, right) in entries.zip entries.tail do
    require (left.root.compare right.root == .lt) "native roots are not increasing"
    require (right.root.compare left.root == .gt) "native reverse comparison failed"
  for entry in entries do
    require (entry.root.compare entry.root == .eq) "native diagonal comparison failed"

private def run : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  match base.roots (0 : DensePoly base.Value) with
  | .all => pure ()
  | _ => throw (IO.userError "native zero polynomial lost all")
  let two : base.Value := 1 + 1
  let three : base.Value := two + 1
  check (DensePoly.C (three + two)) []
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let quadratic := x * x - DensePoly.C two
  let linear := x - DensePoly.C three
  let p := DensePoly.scale (-three) (x * x * quadratic * quadratic * quadratic *
    linear * linear * linear * linear * linear)
  check p [3, 2, 3, 5]
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := quadratic * linear,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "native coefficient root validation failed")
  let first := base.adjoin descriptor
  let alpha := first.generator
  let y : DensePoly first.context.Value := DensePoly.ofCoeffs #[0, 1]
  let factor := y * y - DensePoly.C alpha
  check (factor * factor * (y - DensePoly.C (1 : first.context.Value))) [2, 1, 2]
  require (base.sign two == 1) "old base values became invalid"
  require (first.context.sign alpha == 1) "old selected values became invalid"
  IO.println "native root contexts, embeddings, signs and arithmetic checks passed"

#eval run

end Hex.RealClosure.Tower.RootTests
