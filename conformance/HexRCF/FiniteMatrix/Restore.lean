/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Read
import HexRCF.FiniteMatrix.Literals
import HexRCF.SelectedRoot.KernelCheck
import Lean.Elab.Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
meta section
/-- Name literal data while retaining the checked reader equation separately. -/
def retain (name : Name) (value : Expr) : MetaM Unit := do
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type := (← inferType value), value, hints := .abbrev, safety := .safe }
  addDecl declaration (forceExpose := true)
  compileDecl declaration

def restore (name : Name) (reader : Expr) : MetaM Expr := do
  let (record, proof) ← RationalRoot.checkedRecordProof reader
  retain name record
  let type ← mkEq reader (← mkAppM ``Option.some #[mkConst name])
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked (Name.str name "read_eq") type proof
    #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?]
    #[reader.getAppFn.constName!]
  return mkConst name
end
end Hex.RCF.RealCoefficients.FiniteMatrixTests
