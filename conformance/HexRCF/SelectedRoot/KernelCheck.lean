/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Read
public import HexRealClosure.RootPolicy
public import Lean.Elab.Command

public section

meta section
namespace Hex.RCF.SelectedRootTests.KernelCheck
open Hex.RCF.SelectedRootTests
open Lean Meta Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Algebraic

/-- Check generated replay acceptance with active reduction diagnostics.
The rational parent construction and separately elaborated source theorems are
outside this guard; all frozen scalar, parser, root, row and collected refusal
acceptance proofs pass through it. -/
def addChecked (name : Name) (type proof : Expr) : MetaM Unit := do
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
  let env ← ofExceptKernelException <| environment.addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    (.thmDecl {name, levelParams := [], type, value := proof}) none (doCheck := true)
  let diagnostics := Kernel.getDiagnostics env
  unless diagnostics.enabled do throwError "kernel diagnostics disabled"
  unless !diagnostics.unfoldCounter.isEmpty do throwError "empty kernel diagnostics"
  for name in #[``Read.rootRead, ``Hex.RealClosure.Roots.roots?, ``Hex.RealClosure.Roots.roots,
    ``Hex.RealClosure.Roots.Policy.roots?, ``Hex.RealClosure.Roots.Policy.roots,
    ``Tower.Sample.roots, ``Tower.Context.roots, ``Tower.Context.roots?, ``NumberField.roots, ``NumberField.roots?,
    ``NumberField.Presentation.roots, ``NumberField.Presentation.roots?, ``Algebraic.Context.signPoly,
    ``Algebraic.Context.buildSigns, ``Descriptor.buildSigns, ``Descriptor.buildSignsPrepared,
    ``Hex.SignDet.buildPrepared, ``Hex.SignDet.buildTree, ``Hex.SignDet.buildTreeFrom,
    ``Algebraic.Element.ofPoly, ``Descriptor.prepareQueries] do
    if let some count := diagnostics.unfoldCounter.find? name then
      throwError "native production unfolded {name}: {count}"
  setEnv (Kernel.enableDiag env false)

end Hex.RCF.SelectedRootTests.KernelCheck
