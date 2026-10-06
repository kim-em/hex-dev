/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InverseEquation
public meta import HexRealClosure.InverseEquation

public section

namespace Hex.RealClosure.Algebraic.Packing.Inverse.Tests

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def head : DensePoly Rat := (x * x - DensePoly.C 2) * (x - DensePoly.C 3)

private def pack (context : Context Rat Nat Sturm.orderSign 7) (p : DensePoly Rat) :
    Option (Packing context) :=
  let kept := context.reduce p
  Packing.build? context.reduce rfl [⟨kept, context.signPoly kept, rfl⟩] p

/-- The actual reducible-head split inverse is checked independently of its
packing equation. Memo reads reject mismatched query slices and indices;
the selected-sign factory rejects changed signs and the inverse factory rejects
an altered raw candidate. The supplied-equation reader accepts that different
valid candidate and rejects an incorrect inverse, zero operand, changed
operand/domain and out-of-range index. -/
private def sample (scale : Rat) : Option Bool := do
  let root ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := DensePoly.scale scale head,
      lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin root (fun q => q.den == 1)
  let argument := Element.ofPoly (context := context) (x - DensePoly.C 3)
  let entry ← pack context argument.inverseCandidate
  let .ok record := Inverse.build? argument entry | none
  let graph := SignDet.Dag.encode record.signs.evidence
  let memo ← graph.validate? Sturm.orderSign 7 root.raw.head root.raw.lower root.raw.upper
  let read ← Inverse.readMemo? argument entry memo graph.root
  let outOfRange := Inverse.readMemo? argument entry memo memo.size
  let wrong := SignDet.SelectedSigns.ofMemo? root
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
    #v[argument.sign, 1] memo graph.root
  let changed ← pack context (argument.inverseCandidate + root.raw.head)
  let .ok supplied := context.buildSigns
    [argument.polynomial, argument.polynomial * changed.value.polynomial - 1] | none
  let altered := Inverse.make? argument changed supplied
  let suppliedMade ← Equation.make? argument changed supplied
  let suppliedGraph := SignDet.Dag.encode supplied.evidence
  let suppliedMemo ← suppliedGraph.validate? Sturm.orderSign 7
    root.raw.head root.raw.lower root.raw.upper
  let suppliedRead ← Equation.readMemo? argument changed suppliedMemo suppliedGraph.root
  let suppliedOutOfRange := Equation.readMemo? argument changed suppliedMemo suppliedMemo.size
  let bad ← pack context 1
  let .ok badSigns := context.buildSigns
    [argument.polynomial, argument.polynomial * bad.value.polynomial - 1] | none
  let badMade := Equation.make? argument bad badSigns
  let badRead := Equation.readMemo? argument bad suppliedMemo suppliedGraph.root
  let unrelated := Element.ofPoly (context := context) (x - DensePoly.C 2)
  let unrelatedRead := Inverse.readMemo? unrelated entry memo graph.root
  let suppliedUnrelated := Equation.readMemo? unrelated changed suppliedMemo suppliedGraph.root
  let differentRoot ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := DensePoly.scale scale head,
      lower := .finite (-2), upper := .finite (-1), indices := [], signs := [] }
  let .ok differentSigns := differentRoot.buildSigns
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1] | none
  let differentGraph := SignDet.Dag.encode differentSigns.evidence
  let differentMemo ← differentGraph.validate? Sturm.orderSign 7
    differentRoot.raw.head differentRoot.raw.lower differentRoot.raw.upper
  let wrongDomain := Inverse.readMemo? argument entry differentMemo differentGraph.root
  let zeroRead := Inverse.readMemo? (0 : Element context) entry memo graph.root
  let .ok zeroSigns := context.buildSigns
    [(0 : Element context).polynomial,
      (0 : Element context).polynomial * entry.value.polynomial - 1] | none
  let zeroMade := Inverse.make? (0 : Element context) entry zeroSigns
  let suppliedWrongDomain := Equation.readMemo? argument entry differentMemo differentGraph.root
  let suppliedZero := Equation.make? (0 : Element context) entry zeroSigns
  return read.argument == argument && entry.value == argument⁻¹ &&
    wrong.isNone && altered.isNone && outOfRange.isNone && unrelatedRead.isNone &&
    (scale != 1 || changed.value == entry.value) &&
    (scale == 1 || changed.value != entry.value) &&
    supplied.values.toList == [argument.sign, 0] &&
    differentSigns.values.toList == [argument.sign, 0] &&
    wrongDomain.isNone && zeroRead.isNone && zeroMade.isNone && ((0 : Element context)⁻¹ == 0) &&
    suppliedMade.argument == argument && suppliedRead.argument == argument &&
    suppliedOutOfRange.isNone && suppliedUnrelated.isNone && suppliedWrongDomain.isNone &&
    suppliedZero.isNone && badMade.isNone && badRead.isNone

/- The upstream descriptor validator checks the squarefree-head domain.
A repeated-factor head is rejected before native inverse arithmetic is exposed. -/
#guard (SignDet.Descriptor.validate Sturm.orderSign 7
  { context := 7, head := (DensePoly.ofCoeffs #[-3, 7, -5, 1] : DensePoly Rat),
    lower := .finite 2, upper := .finite 4, indices := [], signs := [] }).isNone

#guard sample 1 == some true
#guard sample 2 == some true
#check_failure Inverse.mk
#check_failure Equation.mk

end Hex.RealClosure.Algebraic.Packing.Inverse.Tests
