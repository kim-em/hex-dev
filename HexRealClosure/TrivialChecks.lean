/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TrivialTower
public import HexRealClosure.TowerOrder
public import HexRealClosure.TowerCatalog

public section

namespace Hex.RealClosure.Trivial.Checks

def registry : BaseContext.Registry := fun _ => none

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def same (a b : RealRootSet) : Bool :=
  match a, b with
  | .all, .all => true
  | .finite left, .finite right =>
    left.map (fun e => (e.root, e.multiplicity)) == right.map (fun e => (e.root, e.multiplicity))
  | _, _ => false

def check {parent : Tower.Context registry} (source : Map parent) (_ : Array RealAlgebraicNumber)
    (name : String) (p : DensePoly parent.Value) : IO Unit := do
  require (same (source.roots p) (source.polynomial p).roots)
    s!"native algebraic-coefficient roots differ from canonical backend: {name}"

def runWith (check : {parent : Tower.Context registry} → Map parent → Array RealAlgebraicNumber → String →
    DensePoly parent.Value → IO Unit) : IO Unit := do
  let base := Tower.Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let nonmonicHead := DensePoly.scale (two + 1)
    ((x * x * x - DensePoly.C two) * (x - DensePoly.C (two + 1)))
  let some nonmonic := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := nonmonicHead,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "nonmonic reducible cubic-root descriptor failed")
  let oldExtension := base.adjoin nonmonic
  let oldGenerator := oldExtension.generator
  let oldTwo : oldExtension.context.Value := 1 + 1
  require (!(decide (oldGenerator * oldGenerator * oldGenerator = oldTwo)))
    "fixture lacks distinct literal cubic representatives"
  let nonmonicMap := (Map.rational registry).adjoin nonmonic
  require (nonmonicMap.value (oldGenerator * oldGenerator * oldGenerator) == 2)
    "nonmonic selected-root conversion failed"
  let head := x * x * x - DensePoly.C two
  let some cubic := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := head,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "nonmonic reducible cubic-root descriptor failed")
  let extension := base.adjoin cubic
  let parent := extension.context
  let a := extension.generator
  let source := (Map.rational registry).adjoin cubic
  let two : parent.Value := 1 + 1
  require (parent.equal (a * a * a) two) "native cubic equation failed"
  require (source.value (a * a * a) == 2) "canonical cubic equation failed"
  require (source.value a * source.value a⁻¹ == 1) "canonical inverse differs"
  require (source.value (a - a) == 0 && source.value (a - a)⁻¹ == 0) "canonical total inverse of zero differs"
  require (source.compare a (a + 1) == parent.compare a (a + 1)) "canonical strict comparison differs"
  let y : DensePoly parent.Value := DensePoly.ofCoeffs #[0, 1]
  let some next := SignDet.Descriptor.validate parent.sign parent.signature
      { context := parent.signature, head := y * y - DensePoly.C a,
        lower := .finite (-two), upper := .finite two, indices := [1], signs := [1] }
    | throw (IO.userError "dependent quadratic Thom descriptor failed")
  let suffix : Tower.Suffix base := .root cubic (.root next .nil)
  let converted := Map.ofSuffix suffix
  let child := suffix.context
  let b : child.Value := by
    change (parent.adjoin next).context.Value
    exact (parent.adjoin next).generator
  let old : child.Value := by
    change (parent.adjoin next).context.Value
    exact (parent.adjoin next).embed a
  require (converted.value b * converted.value b == source.value a) "nested factory lost selected embedding"
  require (converted.value (b * b - old) == 0 && (converted.value b).sign == 1) "nested coefficient conversion differs"
  let .ok reread := child.read (child.write (b / old))
    | throw (IO.userError "native rational-tower value round trip failed")
  require (converted.value reread == converted.value (b / old))
    "checked reader lost canonical embedding"
  require ((child.read (parent.write a)).toOption.isNone) "stale predecessor value was accepted"
  let z : DensePoly child.Value := DensePoly.ofCoeffs #[0, 1]
  let generators := #[converted.value old, converted.value b]
  check converted generators "zero" 0
  check converted generators "constant" (DensePoly.C b)
  check converted generators "dependent linear" (z - DensePoly.C b)
  check converted generators "mixed algebraic coefficients and multiplicities"
    ((z - DensePoly.C old) * (z - DensePoly.C old) * (z - DensePoly.C b))
  check converted generators "nonlinear algebraic head" (z * z - DensePoly.C b)
  check converted generators "cubic with nonreal conjugates" (z * z * z - DensePoly.C old)
  check converted generators "point root at zero" (z * (z - DensePoly.C b))
  require (converted.root (.point 0) == 0) "native point conversion failed"

end Hex.RealClosure.Trivial.Checks
