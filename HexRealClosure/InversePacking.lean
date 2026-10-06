/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Packing
import all HexRealClosure.Algebraic

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- The nonzero inverse operation retains its actual input and native candidate,
with a checked input sign and inverse equation at the same selected root.
Inversion of canonical zero returns zero directly and needs no candidate. -/
structure Inverse (entry : Packing context) where
  private mk ::
  argument : Element context
  nonzero : argument.sign ≠ 0
  candidate : entry.original = argument.inverseCandidate
  signs : SelectedSigns context.root
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
  observed : signs.values.toList = [argument.sign, 0]

/-- Check an inverse's input, literal candidate and joint replay without
producing a new query. Same-value candidates do not replace the actual one. -/
def Inverse.make? (argument : Element context) (entry : Packing context)
    (signs : SelectedSigns context.root
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]) :
    Option (Inverse entry) :=
  if nonzero : argument.sign ≠ 0 then
    if candidate : entry.original = argument.inverseCandidate then
      if observed : signs.values.toList = [argument.sign, 0] then
        some ⟨argument, nonzero, candidate, signs, observed⟩
      else none
    else none
  else none

/-- Successful construction retains the requested input literally. -/
theorem Inverse.make?_argument (argument : Element context) (entry : Packing context)
    (signs : SelectedSigns context.root
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1])
    {record : Inverse entry}
    (accepted : Inverse.make? argument entry signs = some record) :
    record.argument = argument := by
  unfold Inverse.make? at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · have projected := congrArg
          (fun result : Option (Inverse entry) => result.map Inverse.argument) accepted
        exact (Option.some.inj projected).symm
      · cases accepted
    · cases accepted
  · cases accepted

/-- Rechecking an accepted record succeeds with the same retained evidence. -/
theorem Inverse.make?_self {entry : Packing context} (record : Inverse entry) :
    Inverse.make? record.argument entry record.signs = some record := by
  cases record
  rename_i argument nonzero candidate signs observed
  simp [Inverse.make?, nonzero, candidate, observed]

/-- The record binds the output to the actual native local splitting inverse.
The equation follows from the retained raw candidate, without rerunning a sign
query or comparing two independently computed inverse values. -/
theorem Inverse.native {entry : Packing context} (record : Inverse entry) :
    entry.value = record.argument⁻¹ := by
  change entry.value = Element.inv record.argument
  unfold Element.inv
  cases stored : record.argument.stored with
  | none =>
    have vanished : record.argument.sign = 0 := by
      unfold Element.sign
      rw [stored]
    exact (record.nonzero vanished).elim
  | some value =>
    exact entry.native.trans (congrArg Element.ofPoly record.candidate)

/-- Read the extra inverse equation from an already checked finite graph memo. -/
def Inverse.readMemo? (argument : Element context) (entry : Packing context)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper))
    (index : Nat) : Option (Inverse entry) := do
  let signs ← SelectedSigns.readMemo? context.root
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
    ⟨#[argument.sign, 0], rfl⟩ memo index
  Inverse.make? argument entry signs

/-- Produce only the additional input-sign and inverse-equation replay;
the packing record retains its original independent checked bindings. -/
def Inverse.build? (argument : Element context) (entry : Packing context) :
    Except BuildError (Inverse entry) := do
  let signs ← context.buildSigns
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
  match Inverse.make? argument entry signs with
  | some record => return record
  | none => throw .replay

/-- Successful native production retains the requested operand literally. -/
theorem Inverse.build?_argument (argument : Element context) (entry : Packing context)
    {record : Inverse entry} (accepted : Inverse.build? argument entry = .ok record) :
    record.argument = argument := by
  unfold Inverse.build? at accepted
  cases produced : context.buildSigns
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1] with
  | error error => simp [produced, bind, Except.bind] at accepted
  | ok signs =>
    simp only [produced, bind, Except.bind] at accepted
    cases made : Inverse.make? argument entry signs with
    | none =>
      simp only [made] at accepted
      change Except.error BuildError.replay = Except.ok record at accepted
      cases accepted
    | some result =>
      simp only [made, pure, Except.pure] at accepted
      cases Except.ok.inj accepted
      exact Inverse.make?_argument argument entry signs made

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.native

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

private theorem invZero_proof : (0 : Element context)⁻¹ = 0 := rfl

/-- Canonical zero follows the native zero branch without an inverse candidate. -/
theorem Element.inv_zero : (0 : Element context)⁻¹ = 0 := invZero_proof

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.make?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.make?_self

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.build?_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.build?_argument

/-- info: 'Hex.RealClosure.Algebraic.Element.inv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.inv_zero
