/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Packing
public import HexRealClosure.ValueSigns
public import HexSignDet.SelectedSigns
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecordExt
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

omit [Neg E] [Inv E] [Div E] in
private theorem signs_eq {d : Descriptor E Ctx coeffSign parent} {qs : List (DensePoly E)}
    (a b : SelectedSigns d qs) (values : a.values = b.values)
    (evidence : a.evidence = b.evidence) : a = b := by
  cases a
  cases b
  cases values
  cases evidence
  rfl

private theorem packing_eq_proof (a b : Packing context)
    (original : a.original = b.original) (representative : a.representative = b.representative)
    (value : a.value = b.value) (sign : a.sign = b.sign)
    (values : a.signs.values = b.signs.values) (evidence : a.signs.evidence = b.signs.evidence) :
    a = b := by
  cases a
  cases b
  dsimp only at *
  cases original
  cases representative
  cases value
  cases sign
  have same := signs_eq _ _ values evidence
  cases same
  rfl

private theorem valueSign_eq_proof (a b : ValueSign context) (value : a.value = b.value)
    (values : a.signs.values = b.signs.values) (evidence : a.signs.evidence = b.signs.evidence) :
    a = b := by
  cases a
  cases b
  dsimp only at *
  cases value
  have same := signs_eq _ _ values evidence
  cases same
  rfl

public section

theorem packing_eq (a b : Packing context)
    (original : a.original = b.original) (representative : a.representative = b.representative)
    (value : a.value = b.value) (sign : a.sign = b.sign)
    (values : a.signs.values = b.signs.values) (evidence : a.signs.evidence = b.signs.evidence) :
    a = b := packing_eq_proof a b original representative value sign values evidence

theorem valueSign_eq (a b : ValueSign context) (value : a.value = b.value)
    (values : a.signs.values = b.signs.values) (evidence : a.signs.evidence = b.signs.evidence) :
    a = b := valueSign_eq_proof a b value values evidence

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.GuardRecordExt.packing_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packing_eq

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.GuardRecordExt.valueSign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms valueSign_eq

end

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecordExt
