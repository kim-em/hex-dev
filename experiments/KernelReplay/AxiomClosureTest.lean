/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
-- This audit driver intentionally loads full private import data. Under the
-- module system, ordinary imports can hide theorem bodies, unexposed
-- definitions and opaques behind placeholders, and omit private declarations.

import KernelReplay.AxiomClosure
import KernelReplay.ProofAudit
import Lean.Util.CollectAxioms

section
namespace Hex.RealClosure.Algebraic.KernelReplay.AxiomClosureTest
open Lean Meta Elab

private def reject (message : String) (action : MetaM Unit) : MetaM Unit := do
  let rejected ← try
    action
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith message do throw error
    pure true
  unless rejected do throwError "independent axiom audit accepted invalid input"

private def restored : MetaM Unit := do
  let saved ← Meta.saveState
  try
    let name ← mkFreshUserName `closureBranch
    addDecl (.thmDecl {
      name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
    unless (← AxiomClosure.collect #[name]).isEmpty do
      throwError "constructive declaration acquired an axiom"
    saved.restore
    let witness ← mkAppM ``Nonempty.intro #[mkConst ``True.intro]
    let chosen ← mkAppM ``Classical.choice #[witness]
    addDecl (.thmDecl { name, levelParams := [], type := mkConst ``True, value := chosen })
    unless (← AxiomClosure.collect #[name]) == #[`Classical.choice] do
      throwError "independent audit reused a restored environment's result"
  finally saved.restore

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let names := #[``ProofAudit.Branch, ``ProofAudit.Branch.leaf,
    ``ProofAudit.Branch.node, ``ProofAudit.Branch.rec, ``ProofAudit.Branch.casesOn,
    ``ProofAudit.opaqueIndex]
  for name in names do
    let actual ← AxiomClosure.collect #[name]
    unless actual == #[`Classical.choice] do
      throwError "direct body audit for {name} expected Classical.choice, got {actual}"
    unless (← collectAxioms name).all actual.contains do
      throwError "direct body audit omitted a reported dependency"
  let expected := #[`propext, `Classical.choice, `Quot.sound].qsort Name.lt
  let roots := names ++ #[``propext, ``Quot.sound]
  unless (← AxiomClosure.collect roots) == expected &&
      (← AxiomClosure.collect roots.reverse) == expected do
    throwError "direct body audit changed the union or depended on root order"
  unless (← AxiomClosure.collect #[]).isEmpty &&
      (← AxiomClosure.collect #[``Quot, ``Quot.mk]).isEmpty do
    throwError "empty or primitive declaration acquired an axiom"
  let witness ← mkAppM ``Nonempty.intro #[mkConst ``True.intro]
  let chosen ← mkAppM ``Classical.choice #[witness]
  let type ← mkEq chosen (mkConst ``True.intro)
  let proof ← mkEqRefl (mkConst ``True.intro)
  unless (← AxiomClosure.audit proof type) == #[`Classical.choice] do
    throwError "direct body audit omitted a proposition-only dependency"
  let .thmInfo info ← getConstInfo ``FiniteBaseProbe.product |
    throwError "finite-base product theorem missing"
  unless (← AxiomClosure.audit info.value info.type) == expected do
    throwError "finite-base product dependencies changed"
  -- Its proposition has no choice dependency; this checks an imported proof body.
  unless (← AxiomClosure.collect #[``Classical.em]).contains `Classical.choice do
    throwError "direct body audit omitted an imported theorem body"
  reject "dependency audit refuses unsafe or partial declaration" do
    let _ ← AxiomClosure.collect #[``Lean.evalConst]
    pure ()
  let missing ← mkFreshUserName `missingClosure
  reject "axiom closure cannot inspect checked declaration" do
    let _ ← AxiomClosure.collect #[missing]
    pure ()
  let incomplete ← mkFreshExprMVar (mkConst ``True)
  reject "independent axiom audit needs a complete closed" do
    let _ ← AxiomClosure.audit incomplete (mkConst ``True)
    pure ()
  reject "independent axiom audit needs a complete closed" do
    let _ ← AxiomClosure.audit (mkConst ``True.intro) incomplete
    pure ()
  if ← incomplete.mvarId!.isAssigned then
    throwError "direct body audit assigned an incomplete expression"
  withLocalDeclD `hypothesis (mkConst ``True) fun hypothesis => do
    reject "independent axiom audit needs a complete closed" do
      let _ ← AxiomClosure.audit hypothesis (mkConst ``True)
      pure ()
  reject "independent axiom audit needs a complete closed" do
    let _ ← AxiomClosure.audit (mkBVar 0) (mkConst ``True)
    pure ()
  restored

end Hex.RealClosure.Algebraic.KernelReplay.AxiomClosureTest
