/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet
import HexSignDetTheory
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Lean.Util.CollectAxioms

/-! Environment lints cover both production module roots, including theorem
documentation. The imported modules supply the docstring metadata used by these
checks. Individual proof/API and use assessment remain separate requirements. -/

-- The pinned Lean deriving handler generates three recursive equality
-- auxiliaries and two enum constructor-index identities. Their names come
-- from Lean.Elab.Deriving.Util and DecEq, not handwritten API declarations.
-- Guard the exact diagnostics so every additional lint finding still fails;
-- the computational modules need no linter imports or dependency changes.
/-- error: /- The `defsWithUnderscore` linter reports:
FOUND definitions with an underscore in their name.
This linter can be disabled with `@[nolint defsWithUnderscore]`. -/
-- HexSignDet.Codec.Value
#check Hex.SignDet.Codec.Json.instDecidableEqFields.decEq_3 /- The definition `Hex.SignDet.Codec.Json.instDecidableEqFields.decEq_3` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/
#check Hex.SignDet.Codec.Json.instDecidableEqValues.decEq_3 /- The definition `Hex.SignDet.Codec.Json.instDecidableEqValues.decEq_3` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/
#check Hex.SignDet.Codec.Json.instDecidableEqValue.decEq_3 /- The definition `Hex.SignDet.Codec.Json.instDecidableEqValue.decEq_3` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/

/- The `docBlameThm` linter reports:
THEOREMS ARE MISSING DOCUMENTATION STRINGS:
This linter can be disabled with `@[nolint docBlameThm]`. -/
-- HexSignDet.Descriptor
#check Hex.SignDet.DescriptorError.ofNat_ctorIdx /- theorem missing documentation string -/

-- HexSignDet.Produce
#check Hex.SignDet.BuildError.ofNat_ctorIdx /- theorem missing documentation string -/ -/
#guard_msgs (whitespace := lax) in
#lint- docBlame docBlameThm in HexSignDet
#lint- docBlame docBlameThm in HexSignDetTheory

-- Check the complete owned proof surface, including generated constants and fields.
run_cmd do
  let env ← Lean.getEnv
  let expected := [`HexSignDetTheory,
    `HexSignDetTheory.Basis,
    `HexSignDetTheory.CommonProduct,
    `HexSignDetTheory.ComparisonProducer,
    `HexSignDetTheory.CompletionProducer,
    `HexSignDetTheory.Convert,
    `HexSignDetTheory.DagSelectedSigns,
    `HexSignDetTheory.Derivatives,
    `HexSignDetTheory.Embedding,
    `HexSignDetTheory.FiniteSolve,
    `HexSignDetTheory.Foundation,
    `HexSignDetTheory.Naturality,
    `HexSignDetTheory.NodeBasis,
    `HexSignDetTheory.NodeChecks,
    `HexSignDetTheory.NodeProducer,
    `HexSignDetTheory.NodeSolve,
    `HexSignDetTheory.ParentSystem,
    `HexSignDetTheory.QueryHandle,
    `HexSignDetTheory.QueryReduction,
    `HexSignDetTheory.RationalSolve,
    `HexSignDetTheory.Reduction,
    `HexSignDetTheory.ReductionProducer,
    `HexSignDetTheory.Reencode,
    `HexSignDetTheory.ReencodingProducer,
    `HexSignDetTheory.ReencodingRefinement,
    `HexSignDetTheory.RootList,
    `HexSignDetTheory.RootModel,
    `HexSignDetTheory.RootProducer,
    `HexSignDetTheory.SelectedProducer,
    `HexSignDetTheory.SelectedRoot,
    `HexSignDetTheory.Solve,
    `HexSignDetTheory.TableProducer,
    `HexSignDetTheory.Tensor,
    `HexSignDetTheory.Thom,
    `HexSignDetTheory.ThomReencoding,
    `HexSignDetTheory.ThomRoots,
    `HexSignDetTheory.TreeChecks,
    `HexSignDetTheory.TreeSolve]
  let modules := env.allImportedModuleNames.filter (`HexSignDetTheory).isPrefixOf
  for moduleName in expected do
    unless modules.contains moduleName do
      throwError "missing SignDet Theory module: {moduleName}"
  for moduleName in modules do
    unless expected.contains moduleName do
      throwError "unreviewed SignDet Theory module: {moduleName}"
  let constants := env.constants.toList
  for name in [``Hex.SignDet.determine_correct, ``Hex.SignDet.Descriptor.root_spec,
      ``Hex.SignDet.Node.Counted, ``Hex.SignDet.Node.Counted.basis,
      ``Hex.SignDet.Node.Counted.checked, ``Hex.SignDet.Node.Counted.counts,
      ``Hex.SignDet.Node.Counted.cover, ``Hex.SignDet.Node.Counted.values] do
    unless (env.find? name).isSome do
      throwError "missing reviewed SignDet declaration: {name}"
  for userName in [`Hex.SignDet.ordered_cols, `Hex.SignDet.quotient_lcm] do
    unless constants.any (fun (name, _) =>
        Lean.privateToUserName name == userName && name != userName) do
      throwError "missing private SignDet proof body: {userName}"
  let mut count := 0
  for (name, info) in constants do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.allImportedModuleNames[idx.toNat]! do continue
    if info matches .axiomInfo _ then
      throwError "owned axiom declaration: {name}"
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"
    count := count + 1
  if count == 0 then throwError "empty SignDet Theory axiom audit"
  Lean.logInfo m!"Checked axioms of {count} SignDet Theory constants in {modules.size} modules."
