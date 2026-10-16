/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFn
import HexOrderedFnTheory
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation
import Lean.Util.CollectAxioms

/-!
# Ordered-function API lint checks

Legacy imports retain imported docstring metadata for the environment linters.
The checks select the computational and semantic modules by their module roots,
and include theorem documentation.
-/

#lint- docBlame docBlameThm in HexOrderedFn

#lint- docBlame docBlameThm in HexOrderedFnTheory

-- Audit every owned constant, including generated declarations, rather than just examples.
run_cmd do
  let env ← Lean.getEnv
  let groups := [
    (`HexOrderedFn, [`HexOrderedFn, `HexOrderedFn.Search, `HexOrderedFn.Oracle,
      `HexOrderedFn.Real, `HexOrderedFn.Extension, `HexOrderedFn.Infinitesimal]),
    (`HexOrderedFnTheory, [`HexOrderedFnTheory, `HexOrderedFnTheory.Convergence,
      `HexOrderedFnTheory.Evaluation, `HexOrderedFnTheory.Extension, `HexOrderedFnTheory.Hahn,
      `HexOrderedFnTheory.Infinitesimal, `HexOrderedFnTheory.Oracle,
      `HexOrderedFnTheory.Progress, `HexOrderedFnTheory.Real, `HexOrderedFnTheory.Sign])]
  for (root, expected) in groups do
    let modules := env.allImportedModuleNames.filter root.isPrefixOf
    for moduleName in expected do
      unless env.allImportedModuleNames.contains moduleName do
        throwError "missing OrderedFn module: {moduleName}"
    for moduleName in modules do
      unless expected.contains moduleName do
        throwError "unreviewed OrderedFn module: {moduleName}"
    let mut count := 0
    for (name, info) in env.constants.toList do
      let some idx := env.getModuleIdxFor? name | continue
      unless modules.contains env.allImportedModuleNames[idx.toNat]! do continue
      if info matches .axiomInfo _ then
        throwError "owned axiom declaration: {name}"
      for axiomName in ← Lean.collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "unexpected axiom in {name}: {axiomName}"
      count := count + 1
    if count == 0 then throwError "empty OrderedFn axiom audit: {root}"
    Lean.logInfo m!"Checked axioms of {count} {root} constants in {modules.size} modules."
