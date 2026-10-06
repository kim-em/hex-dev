/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTowerProbe
public meta import KernelReplay.FiniteTowerProbe

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerUse

/-- An ordinary downstream import can adjoin the retained checked descriptor. -/
@[expose] def next := Context.adjoin FiniteTowerProbe.nestedRoot (fun _ => false)

theorem next_raw : next.root.raw = FiniteTower.nextRaw := by
  rw [next, Context.root_adjoin, FiniteTowerProbe.nestedRoot_raw]

/- The retained descriptor and both typed inventories have executable bodies. -/
/-- info: true -/
#guard_msgs in
#eval decide (next.root.raw = FiniteTower.nextRaw) &&
  FiniteTowerProbe.nestedEntries.length == 9 && FiniteTowerProbe.nestedSigns.length == 6

end Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerUse

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerUse.next_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerUse.next_raw
