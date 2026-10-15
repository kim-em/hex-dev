/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Command

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure
open Lean Meta

/-- Inspect the checked bodies directly, without using exported axiom tables.
One visited set belongs to the entire requested union. It is never reused as
an incomplete per-declaration axiom result across roots or environments.
The caller must load full private import data, as a non-module audit driver
does; hidden definitions presented as axiom placeholders are rejected by
`audit` rather than accepted using exported metadata. -/
def collect (roots : Array Name) : MetaM (Array Name) := do
  let environment := (← getEnv).setExporting false
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    Core.checkSystem "independent axiom closure"
    let name :: rest := pending | throwError "axiom closure lost a pending name"
    pending := rest
    if visited.contains name then continue
    visited := visited.insert name
    let some info := environment.checked.get.find? name |
      throwError "axiom closure cannot inspect checked declaration {name}"
    let dependencies := match info with
      | .axiomInfo info => info.type.getUsedConstants
      | .defnInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
      | .thmInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
      | .opaqueInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
      | .ctorInfo info => info.type.getUsedConstants
      | .recInfo info => info.type.getUsedConstants
      | .inductInfo info => info.type.getUsedConstants ++ info.ctors.toArray
      | .quotInfo _ => #[]
    if let .axiomInfo _ := info then axioms := axioms.insert name
    pending := dependencies.toList ++ pending
  return axioms.toArray.qsort Name.lt

/-- Audit only the constants occurring in the actual proof and proposition;
local hypotheses must be closed by the caller before this final check. -/
def audit (proof type : Expr) : MetaM (Array Name) := do
  for value in #[proof, type] do
    if value.hasSorry || value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "independent axiom audit needs a complete closed proof and proposition"
  let axioms ← collect (proof.getUsedConstants ++ type.getUsedConstants)
  for name in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "unexpected independently collected axiom {name}"
  return axioms

end Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure
