/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.BoundarySigns
public import HexRCF.RealCoefficients.Samples
public section
namespace Hex.RCF.RealCoefficients.PointRows
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet HexPolyTheory.Interpret
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- A whole source row at a descriptor whose head is checked against the
linear query for the requested ordinary point. -/
structure Packet (point : parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) where
  root : Descriptor parent.Value Signature parent.sign parent.signature
  bound : (root.raw.head - Isolation.pointQuery point).isZero = true
  signs : SelectedSigns root (RepresentationSpecialize.prepare values formula)

/-- Head binding identifies this descriptor's root with the requested point. -/
theorem Packet.value {point : parent.Value} {values : Fin n → parent.Value}
    {formula : RealFormula.QF (n+1)} (packet : Packet point values formula)
    (model : Model parent ℝ) :
    packet.root.root model.value model.zero_iff model.one model.add model.sub model.mul
      model.nat model.sign = model.value point := by
  have same := (sub_isZero model.value model.zero_iff model.sub _ _).mp packet.bound
  have member := (packet.root.root_spec model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign).1
  have zero := (Polynomial.isRoot_of_mem_roots
    ((HexRealRootsTheory.Tarski.mem_rootsIn _ _ _ _).mp member).1).eq_zero
  rw [same, Isolation.pointQuery_eval model.value model.zero_iff model.one model.sub] at zero
  exact sub_eq_zero.mp zero

/-- The complete supplied row has the source formula's exact signs at that
same ordinary point. No previous source theorem or native sign query is used. -/
theorem Packet.row {point : parent.Value} {values : Fin n → parent.Value}
    {formula : RealFormula.QF (n+1)} (packet : Packet point values formula)
    (model : Model parent ℝ) :
    packet.signs.values.toList = formula.polys.map (fun q =>
      (SignType.sign (q.eval (RealFormula.append (fun i => model.value (values i))
        (model.value point))) : Int)) := by
  rw [packet.signs.values_at_root model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign, packet.value model]
  have evaluated := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (Samples.prepare_real model values formula (model.value point))
  simpa only [signsAt, List.map_map, Function.comp_def, RepresentationSpecialize.evaluate,
    Samples.valuation] using evaluated
end Hex.RCF.RealCoefficients.PointRows
