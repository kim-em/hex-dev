/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ValueSigns
public meta import HexRealClosure.ValueSigns

public section

namespace Hex.RealClosure.Algebraic.ValueSign.Tests
private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def head : DensePoly Rat := (x * x - DensePoly.C 2) * (x - DensePoly.C 3)

/-- Reading a restored polynomial above the defining degree keeps its literal
input, instead of replacing it with a packed representative. -/
private def sample (scale : Rat) : Option Bool := do
  let root ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := DensePoly.scale scale head,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin root (fun q => q.den == 1)
  let raw := x + head
  let value ← Element.restore? (context := context) raw (context.signPoly raw)
  let .ok record := ValueSign.build? value | none
  let graph := SignDet.Dag.encode record.signs.evidence
  let memo ← graph.validate? Sturm.orderSign 7 root.raw.head root.raw.lower root.raw.upper
  let read ← ValueSign.readMemo? value memo graph.root
  let badIndex := ValueSign.readMemo? value memo memo.size
  let unrelated := Element.ofPoly (context := context) (x + 1)
  let wrongKey := ValueSign.readMemo? unrelated memo graph.root
  let otherRoot ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := DensePoly.scale scale head,
      lower := .finite 0, upper := .finite 2, indices := [], signs := [] }
  let .ok otherSigns := otherRoot.buildSigns [value.polynomial] | none
  let otherGraph := SignDet.Dag.encode otherSigns.evidence
  let otherMemo ← otherGraph.validate? Sturm.orderSign 7
    otherRoot.raw.head otherRoot.raw.lower otherRoot.raw.upper
  let wrongDomain := ValueSign.readMemo? value otherMemo otherGraph.root
  let .ok zero := ValueSign.build? (0 : Element context) | none
  let zeroGraph := SignDet.Dag.encode zero.signs.evidence
  let zeroMemo ← zeroGraph.validate? Sturm.orderSign 7 root.raw.head root.raw.lower root.raw.upper
  let zeroRead ← ValueSign.readMemo? (0 : Element context) zeroMemo zeroGraph.root
  return read.value == value && read.value.polynomial == raw &&
    (scale != 1 || value != Element.ofPoly raw) &&
    badIndex.isNone && wrongKey.isNone &&
    otherSigns.values.toList == [value.sign] && wrongDomain.isNone && zeroRead.value == 0 &&
    (ValueSign.find [record] unrelated).isNone

#guard sample 1 == some true
#guard sample 2 == some true
#check_failure ValueSign.mk
end Hex.RealClosure.Algebraic.ValueSign.Tests
