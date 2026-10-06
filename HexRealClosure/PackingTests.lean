/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Packing
public meta import HexRealClosure.Packing

public section

namespace Hex.RealClosure.Algebraic.Packing.Tests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def equation : DensePoly Rat := x * x - DensePoly.C 2
private def head : DensePoly Rat := equation * (x - DensePoly.C 3)

/-- Exercise selected semantic zero, literal constants, reduction, and the
strict supplied-evidence boundary in a squarefree reducible root context. -/
private def sample (scale : Rat) (p : DensePoly Rat) : Option (Bool × Bool) := do
  let root ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := DensePoly.scale scale head,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin root (fun q => q.den == 1)
  let kept := context.reduce p
  let fact : SignFact context := ⟨kept, context.signPoly kept, rfl⟩
  let entry ← Packing.build? context.reduce rfl [fact] p
  let .ok supplied := context.root.buildSigns [kept, p - kept] | none
  let graph := SignDet.Dag.encode entry.signs.evidence
  let memo ← graph.validate? Sturm.orderSign 7 root.raw.head root.raw.lower root.raw.upper
  let wrong := SignDet.SelectedSigns.ofMemo? root [kept, p - kept]
    #v[entry.sign, 1] memo graph.root
  let missing := Packing.make? context.reduce rfl [] p supplied
  let read ← Packing.readMemo? context.reduce rfl [fact] p memo graph.root
  let outOfRange := Packing.readMemo? context.reduce rfl [fact] p memo memo.size
  return (entry.original == p && entry.representative == kept &&
    entry.value == Element.ofPoly p &&
    read.original == p && read.value == entry.value &&
    wrong.isNone && missing.isNone && outOfRange.isNone, entry.value == 0)

#guard sample 1 equation == some (true, true)
#guard sample 2 equation == some (true, true)
#guard sample 1 head == some (true, true)
#guard sample 1 0 == some (true, true)
#guard sample 1 (DensePoly.C 2) == some (true, false)
#guard sample 1 (x.natPow 4 + 1) == some (true, false)
#guard sample 2 (x.natPow 4 + 1) == some (true, false)
#check_failure Packing.mk

end Hex.RealClosure.Algebraic.Packing.Tests
