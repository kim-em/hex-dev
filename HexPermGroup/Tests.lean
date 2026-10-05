/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup
public section

namespace Hex.PermGroup.Tests

private def cycle : Perm 3 := Perm.mk #v[1, 2, 0]
private def swap : Perm 3 := Perm.mk #v[1, 0, 2]
private def gens : Array (Perm 3) := #[cycle, swap]

example : HasOrder gens 6 := by perm_group
example : Generated #[cycle] (cycle.comp cycle) := by perm_group
example : ¬ Generated #[cycle] swap := by perm_group
example : GeneratesAll gens := by perm_group
example : ∀ p : Perm 3, Generated gens p := by perm_group
example : HasOrder (#[] : Array (Perm 0)) 1 := by perm_group
example : HasOrder (#[] : Array (Perm 1)) 1 := by perm_group
example : Generated (#[] : Array (Perm 0)) (Perm.id 0) := by perm_group
example : ¬ Generated (#[] : Array (Perm 3)) swap := by perm_group
example : GeneratesAll (#[] : Array (Perm 0)) := by perm_group
example : GeneratesAll (#[] : Array (Perm 1)) := by perm_group
example : HasOrder #[Perm.id 3, cycle, cycle, cycle.inv] 3 := by perm_group


example : Generated #[Perm.ofImages 3 [0, 0, 1]] (Perm.id 3) := by perm_group
example : HasOrder #[Perm.ofImages 3 [0, 3, 1]] 1 := by perm_group
example : HasOrder #[Perm.ofImages 3 []] 1 := by perm_group

def symmetric11 : Array (Perm 11) := #[
  Perm.ofImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  Perm.ofImages 11 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10]]

theorem symmetric11_all : GeneratesAll symmetric11 := by perm_group
theorem symmetric11_forall : ∀ p : Perm 11, Generated symmetric11 p := by perm_group

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.symmetric11_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symmetric11_all
set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.symmetric11_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symmetric11_forall

/-- error: perm_group: full coverage check needs 100 estimated operations, exceeding maxChunkWork := 1 -/
#guard_msgs in
example : GeneratesAll (#[] : Array (Perm 100)) := by
  perm_group (maxChunkWork := 1)

def m11 : Array (Perm 11) := #[
  Perm.ofImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  Perm.ofImages 11 [0, 1, 6, 9, 5, 3, 10, 2, 8, 4, 7]]

theorem m11_order : HasOrder m11 7920 := by perm_group
theorem m11_mem : Generated m11 ((m11[0]'(by decide)).comp (m11[1]'(by decide))) := by perm_group
theorem m11_not_mem : ¬ Generated m11
    (Perm.ofImages 11 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10]) := by perm_group

/-- error: perm_group: the certified order is 7920, not 7921 -/
#guard_msgs in
example : HasOrder m11 7921 := by perm_group

/-- error: perm_group: the certified group does not generate every permutation -/
#guard_msgs in
example : GeneratesAll m11 := by perm_group

example : True := by
  fail_if_success have : Generated #[cycle] swap := by perm_group
  fail_if_success have : HasOrder m11 7920 := by perm_group (maxChunkWork := 1)
  trivial

#guard_msgs (drop info) in
#perm_group_certificate symmetricThree for gens

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.m11_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_order
set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.m11_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_mem
set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.m11_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_not_mem

end Hex.PermGroup.Tests
