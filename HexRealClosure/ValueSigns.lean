/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts

public section

namespace Hex.RealClosure.Algebraic
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- A checked sign of the actual stored value. Repacking its polynomial is
unnecessary and could replace a restored literal by a different representative. -/
structure ValueSign (context : Context E Ctx coeffSign parent) where
  private mk ::
  value : Element context
  signs : SelectedSigns context.root [value.polynomial]
  observed : signs.values.toList = [value.sign]

/-- Bind supplied evidence to the input's retained polynomial and cached tag. -/
def ValueSign.make? (value : Element context)
    (signs : SelectedSigns context.root [value.polynomial]) : Option (ValueSign context) :=
  if observed : signs.values.toList = [value.sign] then
    some ⟨value, signs, observed⟩
  else none

theorem ValueSign.make?_value (value : Element context)
    (signs : SelectedSigns context.root [value.polynomial])
    {record : ValueSign context} (accepted : ValueSign.make? value signs = some record) :
    record.value = value := by
  unfold make? at accepted
  split at accepted
  · cases Option.some.inj accepted
    rfl
  · cases accepted

theorem ValueSign.make?_self (record : ValueSign context) :
    ValueSign.make? record.value record.signs = some record := by
  cases record
  rename_i value signs observed
  simp [make?, observed]

/-- Read a sign without isolation or evidence production. The existing reader
checks the exact context, head, interval, selected root, query and claimed tag. -/
def ValueSign.readMemo? (value : Element context)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (ValueSign context) := do
  let signs ← SelectedSigns.readMemo? context.root [value.polynomial] #v[value.sign] memo index
  ValueSign.make? value signs

/-- Produce a replay of the stored polynomial and use the same checked factory. -/
def ValueSign.build? (value : Element context) : Except BuildError (ValueSign context) := do
  let signs ← context.buildSigns [value.polynomial]
  match ValueSign.make? value signs with
  | some record => return record
  | none => throw .replay

/-- Lookup binds the actual element, including its cached sign and stored
representative. Values with the same denotation need not have the same key. -/
@[expose] def ValueSign.find (records : List (ValueSign context)) (value : Element context) :
    Option (ValueSign context) :=
  match records with
  | [] => none
  | record :: rest =>
    if record.value = value then some record else ValueSign.find rest value

theorem ValueSign.find_value (records : List (ValueSign context)) (value : Element context)
    {record : ValueSign context} (found : ValueSign.find records value = some record) :
    record.value = value := by
  induction records with
  | nil => simp [find] at found
  | cons first rest ih =>
    unfold find at found
    split at found
    · cases Option.some.inj found
      assumption
    · exact ih found

/-- Compiled fallback reads the native cached tag. Ordinary-kernel replay
stops here until evidence for this exact value is supplied. -/
opaque Element.missingSign (value : Element context) :
    {sign : Int // sign = value.sign} := ⟨value.sign, rfl⟩

/-- Every sign read requires evidence for the actual stored value, including
canonical zero. No input is silently repacked to manufacture another key. -/
@[expose] def Element.replaySign (records : List (ValueSign context))
    (value : Element context) : Int :=
  match ValueSign.find records value with
  | some record => record.value.sign
  | none => (Element.missingSign value).val

theorem Element.replaySign_eq (records : List (ValueSign context))
    (value : Element context) : Element.replaySign records value = value.sign := by
  unfold replaySign
  cases found : ValueSign.find records value with
  | none => exact (Element.missingSign value).property
  | some record => exact congrArg Element.sign (ValueSign.find_value records value found)

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Element.replaySign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.replaySign_eq
