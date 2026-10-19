/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup
meta import Lean

public section

/-! The umbrella imports only HexBasic helpers whose public names belong to Hex. -/

run_elab do
  let env ← Lean.getEnv
  let allowed := #[`HexBasic.ArrayDecEq, `HexBasic.OfFn, `HexBasic.Kernel,
    `HexBasic.List.Nodup]
  for mod in env.header.moduleNames do
    if (`HexBasic).isPrefixOf mod && !allowed.contains mod then
      throwError "unexpected HexBasic umbrella dependency: {mod}"
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`HexBasic).isPrefixOf mod && !Lean.isPrivateName name && !(`Hex).isPrefixOf name then
        throwError "HexBasic declaration outside the Hex namespace: {name} ({mod})"

-- Hex equality instances stay scoped, so importing the tactic does not replace
-- Lean's global Array or Vector equality instances.
example : (inferInstance : DecidableEq (Array Nat)) = Array.instDecidableEq := rfl
example : (inferInstance : DecidableEq (Vector Nat 2)) = instDecidableEqVector := rfl

open scoped Hex in
example : (inferInstance : DecidableEq (Array Nat)) = Hex.instDecidableEqArray := rfl

open scoped Hex in
example : (inferInstance : DecidableEq (Vector Nat 2)) = Hex.instDecidableEqVector := rfl

open Hex Hex.PermGroup

example : HasOrder #[Perm.ofImages 3 [1, 2, 0]] 3 := by perm_group
example : GeneratesAll #[Perm.ofImages 3 [1, 2, 0], Perm.ofImages 3 [1, 0, 2]] := by
  perm_group
