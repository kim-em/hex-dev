/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealCoefficients.Replay
public import HexRealClosureMathlib.TowerModel
public import HexRealClosureMathlib.InverseEquation

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
namespace Hex.RCF.RealCoefficients.InverseReplay
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {context : Algebraic.Context parent.Value Signature parent.sign parent.signature}

/-- Preflight every supplied original divisor before reading the supplied same-root
inverse equation. No native inverse candidate or alternate solver is used. -/
@[expose] def check (guards : List (Algebraic.Element context))
    (argument : Algebraic.Element context) (entry : Algebraic.Packing context)
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (memo : Array (Dag.Checked parent.sign parent.signature head lower upper))
    (index : Nat) : Except Replay.Error (Algebraic.Packing.Inverse.Equation entry) :=
  if !guards.all (fun divisor => divisor.sign != 0) || argument.sign == 0 then
    .error .divisor
  else match Algebraic.Packing.Inverse.Equation.readMemo? argument entry memo index with
    | none => .error .evidence
    | some record => .ok record

/-- Acceptance establishes the supplied guard preflight and binds the exact
requested operand. The supplied output need not be a native algorithm's representative. -/
theorem check_parts (guards : List (Algebraic.Element context))
    (argument : Algebraic.Element context) (entry : Algebraic.Packing context)
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (memo : Array (Dag.Checked parent.sign parent.signature head lower upper)) (index : Nat)
    (record : Algebraic.Packing.Inverse.Equation entry)
    (accepted : check guards argument entry memo index = .ok record) :
    guards.all (fun divisor => divisor.sign != 0) = true ∧
      argument.sign ≠ 0 ∧ record.argument = argument := by
  unfold check at accepted
  split at accepted
  · contradiction
  · rename_i valid
    have preflight : guards.all (fun divisor => divisor.sign != 0) = true ∧
        argument.sign ≠ 0 := by simpa using valid
    cases found : Algebraic.Packing.Inverse.Equation.readMemo? argument entry memo index with
    | none => simp only [found] at accepted; contradiction
    | some read =>
      simp only [found] at accepted
      cases Except.ok.inj accepted
      exact ⟨preflight.1, preflight.2,
        Algebraic.Packing.Inverse.Equation.readMemo?_argument argument entry memo index found⟩

/-- Every original guard is nonzero at the descriptor's same selected real
root, under the authenticated predecessor model. -/
theorem check_domains (original : Model parent ℝ)
    (guards : List (Algebraic.Element context))
    (argument : Algebraic.Element context) (entry : Algebraic.Packing context)
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (memo : Array (Dag.Checked parent.sign parent.signature head lower upper)) (index : Nat)
    (record : Algebraic.Packing.Inverse.Equation entry)
    (accepted : check guards argument entry memo index = .ok record) :
    ∀ divisor ∈ guards,
      divisor.denote original.value original.zero_iff original.one original.add original.sub
        original.mul original.nat original.sign ≠ 0 := by
  obtain ⟨preflight, _, _⟩ := check_parts guards argument entry memo index record accepted
  intro divisor present vanished
  have nonzero : divisor.sign ≠ 0 := by
    simpa using (List.all_eq_true.mp preflight divisor present)
  apply nonzero
  rw [divisor.sign_spec original.value original.zero_iff original.one original.add original.sub
    original.mul original.nat original.sign original.neg original.inv, vanished]
  simp

/-- A checked supplied output interprets the inverse of the exact authenticated
source coefficient. The source equality is explicit, not inferred from a key
or an unselected polynomial equation. -/
theorem check_source (original : Model parent ℝ)
    (guards : List (Algebraic.Element context))
    (argument : Algebraic.Element context) (entry : Algebraic.Packing context)
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (memo : Array (Dag.Checked parent.sign parent.signature head lower upper)) (index : Nat)
    (record : Algebraic.Packing.Inverse.Equation entry)
    (accepted : check guards argument entry memo index = .ok record)
    (source : ℝ)
    (authenticated : argument.denote original.value original.zero_iff original.one original.add
      original.sub original.mul original.nat original.sign = source) :
    entry.value.denote original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign = source⁻¹ ∧ source ≠ 0 := by
  obtain ⟨_, nonzero, same⟩ := check_parts guards argument entry memo index record accepted
  constructor
  · have equation := record.denote_inv original.value original.zero_iff original.one
      original.add original.sub original.mul original.nat original.sign
    simpa only [same, authenticated] using equation
  · intro zero
    apply nonzero
    rw [argument.sign_spec original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign original.neg original.inv, authenticated, zero]
    simp
end Hex.RCF.RealCoefficients.InverseReplay

/-- info: 'Hex.RCF.RealCoefficients.InverseReplay.check_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.InverseReplay.check_parts
/-- info: 'Hex.RCF.RealCoefficients.InverseReplay.check_domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.InverseReplay.check_domains
/-- info: 'Hex.RCF.RealCoefficients.InverseReplay.check_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.InverseReplay.check_source
