/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Packing

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [zero : Zero E] [dec : DecidableEq E]
variable [one : One E] [add : Add E] [neg : Neg E] [sub : Sub E]
variable [mul : Mul E] [inv : Inv E] [div : Div E] [natCast : NatCast E]
variable [decCtx : DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

local notation "Carrier" =>
  @Element E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context
local notation "Record" =>
  @Packing E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context
/-- Compute polynomial addition with equal predecessor operations, retaining
this extension's original carrier and packing with complete packing records. -/
@[expose, instance_reducible] def Element.replayAdd (predecessor : Add E)
    (_equal : predecessor = add) (entries : List Record) : Add Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessor
  ⟨fun a b => pack (polynomial a + polynomial b)⟩

theorem Element.replayAdd_eq (predecessor : Add E) (equal : predecessor = add)
    (entries : List Record) :
    @Element.replayAdd E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal entries = (inferInstance : Add Carrier) := by
  cases equal
  simp only [Element.replayAdd, Element.replayPack_eq]
  rfl

/-- Complete-record packing with an equal predecessor Sub operation. -/
@[expose, instance_reducible] def Element.replaySub (predecessor : Sub E)
    (_equal : predecessor = sub) (entries : List Record) : Sub Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessor
  ⟨fun a b => pack (polynomial a - polynomial b)⟩

theorem Element.replaySub_eq (predecessor : Sub E) (equal : predecessor = sub)
    (entries : List Record) :
    @Element.replaySub E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal entries = (inferInstance : Sub Carrier) := by
  cases equal
  simp only [Element.replaySub, Element.replayPack_eq]
  rfl

/-- Polynomial multiplication uses both predecessor addition and
multiplication, followed by complete-record packing in the original carrier. -/
@[expose, instance_reducible] def Element.replayMul
    (predecessorAdd : Add E) (predecessorMul : Mul E)
    (_ha : predecessorAdd = add) (_hm : predecessorMul = mul)
    (entries : List Record) : Mul Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessorAdd
  letI := predecessorMul
  ⟨fun a b => pack (polynomial a * polynomial b)⟩

theorem Element.replayMul_eq
    (predecessorAdd : Add E) (predecessorMul : Mul E)
    (ha : predecessorAdd = add) (hm : predecessorMul = mul)
    (entries : List Record) :
    @Element.replayMul E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorAdd predecessorMul ha hm entries =
      (inferInstance : Mul Carrier) := by
  cases ha
  cases hm
  simp only [Element.replayMul, Element.replayPack_eq]
  rfl

/-- Negate as `0 - p` with equal predecessor subtraction, then pack
from complete packing records in the original carrier. -/
@[expose, instance_reducible] def Element.replayNeg (predecessor : Sub E)
    (_equal : predecessor = sub) (entries : List Record) : Neg Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessor
  ⟨fun a => pack (0 - polynomial a)⟩

theorem Element.replayNeg_eq (predecessor : Sub E) (equal : predecessor = sub)
    (entries : List Record) :
    @Element.replayNeg E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal entries = (inferInstance : Neg Carrier) := by
  cases equal
  simp only [Element.replayNeg, Element.replayPack_eq]
  rfl

/-- Complete-record packing with an equal predecessor One operation. -/
@[expose, instance_reducible] def Element.replayOne (predecessor : One E)
    (_equal : predecessor = one) (entries : List Record) : One Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  letI := predecessor
  ⟨pack 1⟩

theorem Element.replayOne_eq (predecessor : One E) (equal : predecessor = one)
    (entries : List Record) :
    @Element.replayOne E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal entries = (inferInstance : One Carrier) := by
  cases equal
  simp only [Element.replayOne, Element.replayPack_eq]
  rfl

/-- Complete-record packing with an equal predecessor NatCast operation. -/
@[expose, instance_reducible] def Element.replayNatCast (predecessor : NatCast E)
    (_equal : predecessor = natCast) (entries : List Record) : NatCast Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  letI := predecessor
  ⟨fun n => pack (DensePoly.C n)⟩

theorem Element.replayNatCast_eq (predecessor : NatCast E) (equal : predecessor = natCast)
    (entries : List Record) :
    @Element.replayNatCast E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal entries = (inferInstance : NatCast Carrier) := by
  cases equal
  simp only [Element.replayNatCast, Element.replayPack_eq]
  rfl

/-- Invert using equal predecessor arithmetic and the same gcd/Bézout
algorithm as native inversion, then pack from complete packing records. -/
@[expose, instance_reducible] def Element.replayInv
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (_ho : predecessorOne = one) (_ha : predecessorAdd = add)
    (_hs : predecessorSub = sub) (_hm : predecessorMul = mul)
    (_hi : predecessorInv = inv) (_hd : predecessorDiv = div)
    (entries : List Record) : Inv Carrier :=
  let pack := @Element.replayPack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context entries
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  let stored := @Element.stored E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context
  let empty := @Element.zero E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context
  let root := @Context.root E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context
  let head := (@SignDet.Descriptor.raw E Ctx zero dec one add sub mul natCast decCtx
    coeffSign parent root).head
  letI := predecessorOne
  letI := predecessorAdd
  letI := predecessorSub
  letI := predecessorMul
  letI := predecessorInv
  letI := predecessorDiv
  ⟨fun a => match stored a with
    | none => empty
    | some _ => pack (Element.inversePolynomial head (polynomial a))⟩

theorem Element.replayInv_eq
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul)
    (hi : predecessorInv = inv) (hd : predecessorDiv = div)
    (entries : List Record) :
    @Element.replayInv E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorOne predecessorAdd predecessorSub predecessorMul
      predecessorInv predecessorDiv ho ha hs hm hi hd entries =
      (inferInstance : Inv Carrier) := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hi
  cases hd
  simp only [Element.replayInv, Element.replayPack_eq]
  rfl

/-- Division uses the same explicit predecessor arithmetic for inversion and
multiplication. The carrier remains bound to the original context. -/
@[expose, instance_reducible] def Element.replayDiv
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul)
    (hi : predecessorInv = inv) (hd : predecessorDiv = div)
    (entries : List Record) : Div Carrier :=
  let multiply := @Element.replayMul E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context predecessorAdd predecessorMul ha hm entries
  let invert := @Element.replayInv E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context predecessorOne predecessorAdd predecessorSub predecessorMul
    predecessorInv predecessorDiv ho ha hs hm hi hd entries
  ⟨fun a b => multiply.mul a (invert.inv b)⟩

theorem Element.replayDiv_eq
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul)
    (hi : predecessorInv = inv) (hd : predecessorDiv = div)
    (entries : List Record) :
    @Element.replayDiv E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorOne predecessorAdd predecessorSub predecessorMul
      predecessorInv predecessorDiv ho ha hs hm hi hd entries =
      (inferInstance : Div Carrier) := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hi
  cases hd
  unfold Element.replayDiv
  rw [Element.replayMul_eq, Element.replayInv_eq]
  rfl

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Element.replayDiv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.replayDiv_eq
