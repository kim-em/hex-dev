/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Gather
public meta import HexRCF.RealCoefficients.Gather
public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients.Samples
public meta import HexRealClosure.LiveContext
public meta import HexRealClosure.TowerContext

public section
open scoped List
namespace Hex.RCF.RealCoefficients.GatherTests
open Hex RealClosure RealClosure.Tower

def registry : BaseContext.Registry := fun _ => none
abbrev base := Context.base (BaseContext.rational registry)

def decisions : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some positive := SignDet.Descriptor.validate base.sign base.signature
      {context := base.signature, head := x * x - DensePoly.C (1 + 1),
       lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := []} |
    return false
  let some negative := SignDet.Descriptor.validate base.sign base.signature
      {context := base.signature, head := x * x - DensePoly.C (1 + 1),
       lower := .finite (-(1 + 1)), upper := .finite (-1), indices := [], signs := []} |
    return false
  let p := base.adjoin positive
  let n := base.adjoin negative
  let owners := [p.context, n.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners |
    return false
  let coefficients : (i : Fin owners.length) → (owners[i]).Value := by
    change (i : Fin 2) → ([p.context, n.context][i]).Value
    exact Fin.cases p.generator (Fin.cases n.generator (fun i => Fin.elim0 i))
  let source := Gather.values shared coefficients
  let v : RealFormula.Poly 3 := MvPoly.X 2
  let order := RealFormula.QF.atom ⟨v ^ 2 + MvPoly.X 0 - MvPoly.X 1, .gt⟩
  let reverse := RealFormula.QF.atom ⟨v ^ 2 + MvPoly.X 1 - MvPoly.X 0, .gt⟩
  let cancelled := RealFormula.QF.atom ⟨v ^ 2 + MvPoly.X 0 + MvPoly.X 1, .ge⟩
  let leading : RealFormula.QF 3 := RealFormula.QF.atom
    ⟨(MvPoly.X 0 + MvPoly.X 1) * v ^ 4 + v ^ 2, .ge⟩
  let zero : RealFormula.QF 3 := RealFormula.QF.atom ⟨MvPoly.X 0 + MvPoly.X 1, .eq⟩
  let degrees := (RepresentationSpecialize.prepare source leading).map DensePoly.natDegree
  return degrees == [2] && Samples.run source leading .forallReal == some true &&
    Samples.run source zero .forallReal == some true &&
    Samples.run source order .forallReal == some true &&
    Samples.run source reverse .forallReal == some false &&
    Samples.run source cancelled .forallReal == some true

#guard decisions

/-- Different defining polynomials and a repeated original owner use the same
common model. A further root is found over their gathered coefficient field. -/
def independent : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some first := SignDet.Descriptor.validate base.sign base.signature
      {context := base.signature, head := x * x - DensePoly.C (1 + 1),
       lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := []} |
    return false
  let some second := SignDet.Descriptor.validate base.sign base.signature
      {context := base.signature, head := x * x - DensePoly.C (1 + 1 + 1),
       lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := []} |
    return false
  let p := base.adjoin first
  let q := base.adjoin second
  let owners := [p.context, q.context, p.context]
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) owners |
    return false
  let coefficients : (i : Fin owners.length) → (owners[i]).Value := by
    change (i : Fin 3) → ([p.context, q.context, p.context][i]).Value
    exact Fin.cases p.generator (Fin.cases q.generator
      (Fin.cases p.generator (fun i => Fin.elim0 i)))
  let source := Gather.values shared coefficients
  let v : RealFormula.Poly 4 := MvPoly.X 3
  let order := RealFormula.QF.atom ⟨v ^ 2 + MvPoly.X 1 - MvPoly.X 0, .gt⟩
  let reverse := RealFormula.QF.atom ⟨v ^ 2 + MvPoly.X 0 - MvPoly.X 1, .gt⟩
  let leading := RealFormula.QF.atom
    ⟨(MvPoly.X 0 - MvPoly.X 2) * v ^ 4 + v ^ 2, .ge⟩
  let root := RealFormula.QF.and (.atom ⟨v ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨v - 1, .gt⟩) (.atom ⟨v - MvPoly.X 1, .lt⟩))
  let degrees := (RepresentationSpecialize.prepare source leading).map DensePoly.natDegree
  return degrees == [2] && Samples.run source leading .forallReal == some true &&
    Samples.run source order .forallReal == some true &&
    Samples.run source reverse .forallReal == some false &&
    Samples.run source root .existsReal == some true

#guard independent

/-- Empty owner collection still evaluates a genuine rational formula. -/
def empty : Bool := Id.run do
  let some shared := Shared.gather? (.pack (BaseContext.rational registry)) [] |
    return false
  let coefficients := fun i : Fin 0 => Fin.elim0 i
  let formula : RealFormula.QF 1 := .atom ⟨MvPoly.X 0 ^ 2, .ge⟩
  return Samples.run (Gather.values shared coefficients) formula .forallReal == some true

#guard empty

/-- A source registered only at β can supply coefficients to a target registered
at α and then β. The old prefix premise is false, while actual gathering and
native formula production retain the original owner's coordinate meaning.
`source` may itself contain an algebraic suffix over its registered base. -/
theorem insert_before {providers : BaseContext.Registry}
    {target : BaseContext.PackedContext providers}
    (source : Context providers) (following : target.Realization)
    (reference : Model (Context.ofBase target) ℝ)
    (α β : BaseContext.ConstantKey) (different : β ≠ α)
    (sourceKeys : source.origin.base.signature.constants = [β])
    (targetKeys : target.signature.constants = [α, β])
    (depth : source.origin.base.signature.infinitesimals ≤ target.signature.infinitesimals)
    (coefficients : (i : Fin [source].length) → ([source][i]).Value)
    (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier) :
    ¬ source.origin.base.signature.constants <+: target.signature.constants ∧
      ∃ shared : Shared target [source], Shared.gather? target [source] = some shared ∧
        ∃ model : Shared.Model shared following reference,
          ∃ result, Samples.run (Gather.values shared coefficients) formula quantifier =
              some result ∧
            (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
              (fun i => (model.owners.get i).1.value (coefficients i))) := by
  constructor
  · rw [sourceKeys, targetKeys, List.singleton_prefix_cons_iff]
    exact different
  · apply Gather.gather_subsequence following reference
    intro owner member
    have same : owner = source := by simpa only [List.mem_singleton] using member
    subst owner
    constructor
    · rw [sourceKeys, targetKeys]
      exact List.sublist_append_right [α] [β]
    · exact depth

/-- Subsequence compatibility retains provider versions and relative key order. -/
private def keyBindings : Bool :=
  let α : BaseContext.ConstantKey := ⟨"alpha", 1⟩
  let β : BaseContext.ConstantKey := ⟨"beta", 1⟩
  let stale : BaseContext.ConstantKey := ⟨"beta", 0⟩
  Decidable.decide ([β] <+ [α, β]) && !Decidable.decide ([β] <+: [α, β]) &&
    !Decidable.decide ([β, α] <+ [α, β]) && !Decidable.decide ([stale] <+ [α, β])

#guard keyBindings

end Hex.RCF.RealCoefficients.GatherTests

/-- info: 'Hex.RCF.RealCoefficients.GatherTests.insert_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.GatherTests.insert_before

/-- info: 'Hex.RCF.RealCoefficients.Gather.gather_subsequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Gather.gather_subsequence

/-- info: 'Hex.RCF.RealCoefficients.Gather.values_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Gather.values_real

/-- info: 'Hex.RCF.RealCoefficients.Gather.prepare_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Gather.prepare_eval

/-- info: 'Hex.RCF.RealCoefficients.Gather.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Gather.run_spec

/-- info: 'Hex.RCF.RealCoefficients.Gather.gather_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Gather.gather_spec

/-- info: 'Hex.RCF.RealCoefficients.Gather.run_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Gather.run_original
