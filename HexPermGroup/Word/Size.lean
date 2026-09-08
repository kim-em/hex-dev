/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Membership

public section

namespace Hex.PermGroup

/-- Compute the exact membership-program allocation from existing program
sizes and chain choices, without constructing the translated programs. -/
@[expose] def Chain.programSize : (c : Chain n) → c.Choice → Nat
  | .leaf _ _, _ => 1
  | .cons level tail, digits =>
    level.orbit.words[digits.1.val].nodes.size +
      (1 + (tail.words.toList.map fun w => w.nodes.size).sum + tail.programSize digits.2) + 1

theorem Chain.program_size (c : Chain n) (base : Nat) (h : c.checkFrom base = true) (digits : c.Choice) :
    (c.program base h digits).val.nodes.size = c.programSize digits := by
  cases c with
  | leaf S words => rfl
  | cons level tail =>
    simp only [program, Program.comp, Array.size_push, Array.size_append, Array.size_map,
      Program.substitute_size, program_size tail, programSize]
termination_by c

@[expose] def Group.programSize (G : Group n) (digits : G.chain.Choice) : Nat :=
  1 + (G.chain.words.toList.map fun w => w.nodes.size).sum + G.chain.programSize digits

theorem Group.program_size (G : Group n) (digits : G.chain.Choice) :
    (G.program digits).nodes.size = G.programSize digits := by
  simp only [program, Program.substitute_size, Chain.program_size, programSize]

end Hex.PermGroup
