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
  let start ← IO.monoMsNow
  IO.eprintln s!"Checking native roots: {name}"
  let produced := parent.roots p
  IO.eprintln s!"Native roots ready: {name}, {match produced with
    | .all => "all" | .finite entries => toString entries.length}"
  let nativeEnd ← IO.monoMsNow
  let converted := source.output produced
  IO.eprintln s!"Converted roots ready: {name}, {match converted with
    | .all => "all" | .finite entries => toString entries.size}"
  let convertedEnd ← IO.monoMsNow
  IO.eprintln s!"Checking canonical backend: {name}"
  let expected := (source.polynomial p).roots
  IO.eprintln s!"Canonical roots ready: {name}, {match expected with
    | .all => "all" | .finite entries => toString entries.size}"
  let backendEnd ← IO.monoMsNow
  require (same converted expected)
    s!"native algebraic-coefficient roots differ from canonical backend: {name}"
  IO.eprintln s!"Verified {name}: native {nativeEnd - start} ms, conversion {
    convertedEnd - nativeEnd} ms, backend {backendEnd - convertedEnd} ms"
  match produced with
  | .all => pure ()
  | .finite entries =>
    if name == "point root at zero" then
      require (entries.any fun e => match e.root with
        | .point value => parent.equal value 0
        | .selected _ _ _ => false) "point fixture did not produce a point root at zero"
    if name == "nonlinear algebraic head" || name == "cubic with nonreal conjugates" then
      require (!entries.isEmpty && entries.all fun e => match e.root with
        | .point _ => false
        | .selected _ _ _ => true) "nonlinear fixture did not produce selected roots"

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
        lower := .finite 1, upper := .posInf, indices := [], signs := [] }
    | throw (IO.userError "cubic-root descriptor failed")
  let extension := base.adjoin cubic
  let parent := extension.context
  let a := extension.generator
  let source := (Map.rational registry).adjoin cubic
  let rational := Map.rational registry
  let cubicRoot : Tower.Root base := .selected cubic extension rfl
  let nonmonicRoot : Tower.Root base := .selected nonmonic oldExtension rfl
  let identity := rational.compareRoots cubicRoot nonmonicRoot
  require (identity == .eq && identity == cubicRoot.compare nonmonicRoot)
    "canonical comparison lost root identity across different child contexts"
  let reverse := rational.compareRoots nonmonicRoot cubicRoot
  require (reverse == .eq && reverse == nonmonicRoot.compare cubicRoot)
    "reversed selected-root identity differs"
  let before := rational.compareRoots cubicRoot (.point two)
  require (before == .lt && before == cubicRoot.compare (.point two))
    "canonical selected-versus-point comparison differs"
  let after := rational.compareRoots (.point two) cubicRoot
  require (after == .gt && after == (Tower.Root.point two).compare cubicRoot)
    "canonical point-versus-selected comparison differs"
  let some quadratic := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C two,
        lower := .finite 1, upper := .finite two, indices := [], signs := [] }
    | throw (IO.userError "rational quadratic-root descriptor failed")
  let quadraticRoot := Tower.Root.ofSelection base (.selected quadratic)
  let distinct := rational.compareRoots cubicRoot quadraticRoot
  require (distinct == .lt && distinct == cubicRoot.compare quadraticRoot)
    "strict order of distinct selected roots differs"
  let two : parent.Value := 1 + 1
  require (parent.equal (a * a * a) two) "native cubic equation failed"
  require (source.value (a * a * a) == 2) "canonical cubic equation failed"
  require (source.value a * source.value a⁻¹ == 1) "canonical inverse differs"
  require (source.value (a - a) == 0 && source.value (a - a)⁻¹ == 0) "canonical total inverse of zero differs"
  require (source.compare a (a + 1) == parent.compare a (a + 1)) "canonical strict comparison differs"
  let y : DensePoly parent.Value := DensePoly.ofCoeffs #[0, 1]
  let some next := SignDet.Descriptor.validate parent.sign parent.signature
      { context := parent.signature, head := y * y - DensePoly.C a,
        lower := .negInf, upper := .finite a, indices := [1], signs := [1] }
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
  require (converted.compareRoots (.point 0) (.point 1) ==
    (Tower.Root.point (parent := child) 0).compare (.point 1)) "native root comparison differs"
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
