/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroupMathlib.Tactic
meta import Lean

public section

/-! Regression tests for the lightweight Mathlib extension. -/

open Hex Hex.PermGroup

-- The tactic needs only the conversions, without adding a group instance for Hex permutations.
run_elab do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`HexBasic).isPrefixOf mod &&
        !#[`HexBasic.ArrayDecEq, `HexBasic.OfFn, `HexBasic.Kernel,
          `HexBasic.List.Nodup].contains mod then
      throwError "unexpected HexBasic adapter dependency: {mod}"
  unless (← Lean.Meta.synthInstance? (← Lean.Meta.mkAppM ``_root_.Group
      #[← Lean.Meta.mkAppM ``Perm #[Lean.mkNatLit 3]])).isNone do
    throwError "the lightweight adapter imported the optional Hex group instance"

namespace Hex.PermGroup.Mathlib.TacticTests

@[expose] def cycle : Equiv.Perm (Fin 3) := permOfImages 3 [1, 2, 0]
@[expose] def swap : Equiv.Perm (Fin 3) := permOfImages 3 [1, 0, 2]
noncomputable def generators : Set (Equiv.Perm (Fin 3)) := {cycle, swap}
noncomputable def symmetric : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.closure generators

theorem order : Nat.card symmetric = 6 := by perm_group
theorem member : cycle * swap ∈ symmetric := by perm_group
theorem nonmember : swap ∉ Subgroup.closure ({cycle} : Set _) := by perm_group
theorem full : symmetric = ⊤ := by perm_group

example : Nat.card (Subgroup.closure
    (↑({cycle, swap} : Finset (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3)))) = 6 := by
  perm_group
example : cycle ∈ Subgroup.closure {p : Equiv.Perm (Fin 3) | p ∈ [cycle, swap]} := by
  perm_group
example : swap ∉ Subgroup.closure {p : Equiv.Perm (Fin 3) | p ∈ [cycle]} := by
  perm_group
example : Subgroup.closure {p : Equiv.Perm (Fin 3) | p ∈ [cycle, swap]} = ⊤ := by
  perm_group
example : Nat.card (Subgroup.closure
    ({permOfImages 3 [0, 0, 1]} : Set (Equiv.Perm (Fin 3)))) = 1 := by perm_group
example : Subgroup.closure (∅ : Set (Equiv.Perm (Fin 0))) = ⊤ := by perm_group
example : Subgroup.closure (∅ : Set (Equiv.Perm (Fin 1))) = ⊤ := by perm_group

noncomputable def m11 : Set (Equiv.Perm (Fin 11)) := {
  permOfImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  permOfImages 11 [0, 1, 6, 9, 5, 3, 10, 2, 8, 4, 7]}

theorem m11_order : Nat.card (Subgroup.closure m11) = 7920 := by perm_group
theorem m11_not_mem : permOfImages 11 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10] ∉
    Subgroup.closure m11 := by perm_group

example : True := by
  fail_if_success have : Nat.card symmetric = 5 := by perm_group
  fail_if_success have : swap ∈ Subgroup.closure ({cycle} : Set _) := by perm_group
  fail_if_success have : cycle ∉ symmetric := by perm_group
  fail_if_success have : Subgroup.closure ({cycle} : Set _) = ⊤ := by perm_group
  trivial

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.m11_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_order

end Hex.PermGroup.Mathlib.TacticTests
