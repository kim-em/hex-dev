/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import HexRCF.ProofEvidence
public meta section
namespace Hex.RCF.ProofPaths
open Lean Meta

/-- Direct constant references in the selected module's actual theorem bodies
reachable from one root. References inherited only through imported checker
or model bodies do not count. -/
meta def references (moduleName root : Name) : MetaM NameHashSet := do
  let dependencies ← ProofEvidence.projectDependencies #[root]
  let environment ← getEnv
  let modules := environment.header.moduleNames
  let mut used : NameHashSet := {}
  for name in dependencies.toArray do
    let some index := environment.getModuleIdxFor? name | continue
    unless modules[index]! == moduleName do continue
    let .thmInfo info ← getConstInfo name | continue
    for reference in info.value.getUsedConstants do used := used.insert reference
  pure used

/-- Require actual uses in generated local proof bodies on this root's path. -/
meta def require (moduleName root : Name) (required : Array Name) : MetaM Unit := do
  let used ← references moduleName root
  for name in required do
    unless used.contains name do
      throwError "proof path {root} has no direct local use of {name}"
end Hex.RCF.ProofPaths
