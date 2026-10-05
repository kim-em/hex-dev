/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [zero : Zero E] [dec : DecidableEq E]
variable [one : One E] [add : Add E] [neg : Neg E] [sub : Sub E]
variable [mul : Mul E] [inv : Inv E] [div : Div E] [natCast : NatCast E]
variable [decCtx : DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

local notation "Carrier" =>
  @Element E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context
local notation "Fact" =>
  @SignFact E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context
local notation "nativeReduce" =>
  @Context.reduce E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent context

/-- Apply the original reduction policy with equal predecessor operations.
A clean monic head uses the existing monic-division algorithm; other contexts
retain the input literally. The original context and checked policy are fixed.
The monic division loop uses subtraction and multiplication; its generic Add
parameter is unused. The stored policy may evaluate native constant one. -/
@[expose] def Context.factReduce (subject : Context E Ctx coeffSign parent)
    (predecessorOne : One E) (predecessorSub : Sub E) (predecessorMul : Mul E)
    (ho : predecessorOne = one) (_hs : predecessorSub = sub) (_hm : predecessorMul = mul)
    (p : DensePoly E) : DensePoly E :=
  let root := @Context.root E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent subject
  let head := (@SignDet.Descriptor.raw E Ctx zero dec one add sub mul natCast decCtx
    coeffSign parent root).head
  let canReduce := @Context.canReduce E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent subject
  let monic := @Context.monic_of_reduce E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent subject
  letI := predecessorOne
  letI := predecessorSub
  letI := predecessorMul
  if h : canReduce = true then
    (DensePoly.divModMonic p head (by
      change head.leadingCoeff = @One.one E predecessorOne
      rw [ho]
      exact monic h)).2
  else p

theorem Context.factReduce_eq (subject : Context E Ctx coeffSign parent)
    (predecessorOne : One E) (predecessorSub : Sub E) (predecessorMul : Mul E)
    (ho : predecessorOne = one) (hs : predecessorSub = sub) (hm : predecessorMul = mul) :
    @Context.factReduce E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent subject predecessorOne predecessorSub predecessorMul ho hs hm =
      @Context.reduce E Ctx zero dec one add neg sub mul inv div natCast decCtx
        coeffSign parent subject := by
  cases ho
  cases hs
  cases hm
  rfl

/-- Compute polynomial addition with equal predecessor operations, retaining
this extension's original carrier and packing with supplied scalar facts. -/
@[expose, instance_reducible] def Element.factAdd (predecessor : Add E)
    (_equal : predecessor = add) (reduce : DensePoly E → DensePoly E)
    (hr : reduce = nativeReduce) (facts : List Fact) : Add Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessor
  ⟨fun a b => pack (polynomial a + polynomial b)⟩

theorem Element.factAdd_eq (predecessor : Add E) (equal : predecessor = add)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factAdd E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal reduce hr facts = (inferInstance : Add Carrier) := by
  cases equal
  exact Element.cachedAdd_eq reduce hr facts

/-- Supplied-fact packing with an equal predecessor Sub operation. -/
@[expose, instance_reducible] def Element.factSub (predecessor : Sub E)
    (_equal : predecessor = sub) (reduce : DensePoly E → DensePoly E)
    (hr : reduce = nativeReduce) (facts : List Fact) : Sub Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessor
  ⟨fun a b => pack (polynomial a - polynomial b)⟩

theorem Element.factSub_eq (predecessor : Sub E) (equal : predecessor = sub)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factSub E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal reduce hr facts = (inferInstance : Sub Carrier) := by
  cases equal
  exact Element.cachedSub_eq reduce hr facts

/-- Polynomial multiplication uses both predecessor addition and
multiplication, followed by supplied-fact packing in the original carrier. -/
@[expose, instance_reducible] def Element.factMul
    (predecessorAdd : Add E) (predecessorMul : Mul E)
    (_ha : predecessorAdd = add) (_hm : predecessorMul = mul)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) : Mul Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessorAdd
  letI := predecessorMul
  ⟨fun a b => pack (polynomial a * polynomial b)⟩

theorem Element.factMul_eq
    (predecessorAdd : Add E) (predecessorMul : Mul E)
    (ha : predecessorAdd = add) (hm : predecessorMul = mul)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factMul E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorAdd predecessorMul ha hm reduce hr facts =
      (inferInstance : Mul Carrier) := by
  cases ha
  cases hm
  exact Element.cachedMul_eq reduce hr facts

/-- Negate as `0 - p` with equal predecessor subtraction, then pack
from supplied scalar facts in the original carrier. -/
@[expose, instance_reducible] def Element.factNeg (predecessor : Sub E)
    (_equal : predecessor = sub) (reduce : DensePoly E → DensePoly E)
    (hr : reduce = nativeReduce) (facts : List Fact) : Neg Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
  let polynomial := @Element.polynomial E Ctx zero dec one add neg sub mul inv div natCast
    decCtx coeffSign parent context
  letI := predecessor
  ⟨fun a => pack (0 - polynomial a)⟩

theorem Element.factNeg_eq (predecessor : Sub E) (equal : predecessor = sub)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factNeg E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal reduce hr facts = (inferInstance : Neg Carrier) := by
  cases equal
  exact Element.cachedNeg_eq reduce hr facts

/-- Supplied-fact packing with an equal predecessor One operation. -/
@[expose, instance_reducible] def Element.factOne (predecessor : One E)
    (_equal : predecessor = one) (reduce : DensePoly E → DensePoly E)
    (hr : reduce = nativeReduce) (facts : List Fact) : One Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
  letI := predecessor
  ⟨pack 1⟩

theorem Element.factOne_eq (predecessor : One E) (equal : predecessor = one)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factOne E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal reduce hr facts = (inferInstance : One Carrier) := by
  cases equal
  exact Element.cachedOne_eq reduce hr facts

/-- Supplied-fact packing with an equal predecessor NatCast operation. -/
@[expose, instance_reducible] def Element.factNatCast (predecessor : NatCast E)
    (_equal : predecessor = natCast) (reduce : DensePoly E → DensePoly E)
    (hr : reduce = nativeReduce) (facts : List Fact) : NatCast Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
  letI := predecessor
  ⟨fun n => pack (DensePoly.C n)⟩

theorem Element.factNatCast_eq (predecessor : NatCast E) (equal : predecessor = natCast)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factNatCast E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessor equal reduce hr facts = (inferInstance : NatCast Carrier) := by
  cases equal
  exact Element.cachedNatCast_eq reduce hr facts

/-- Invert using equal predecessor arithmetic and the same gcd/Bézout
algorithm as native inversion, then pack from supplied scalar facts. -/
@[expose, instance_reducible] def Element.factInv
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (_ho : predecessorOne = one) (_ha : predecessorAdd = add)
    (_hs : predecessorSub = sub) (_hm : predecessorMul = mul)
    (_hi : predecessorInv = inv) (_hd : predecessorDiv = div)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) : Inv Carrier :=
  let pack := @Element.pack E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context reduce hr facts
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

theorem Element.factInv_eq
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul)
    (hi : predecessorInv = inv) (hd : predecessorDiv = div)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factInv E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorOne predecessorAdd predecessorSub predecessorMul
      predecessorInv predecessorDiv ho ha hs hm hi hd reduce hr facts =
      (inferInstance : Inv Carrier) := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hi
  cases hd
  exact Element.cachedInv_eq reduce hr facts

/-- Division uses the same explicit predecessor arithmetic for inversion and
multiplication. The carrier remains bound to the original context. -/
@[expose, instance_reducible] def Element.factDiv
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul)
    (hi : predecessorInv = inv) (hd : predecessorDiv = div)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) : Div Carrier :=
  let multiply := @Element.factMul E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context predecessorAdd predecessorMul ha hm reduce hr facts
  let invert := @Element.factInv E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context predecessorOne predecessorAdd predecessorSub predecessorMul
    predecessorInv predecessorDiv ho ha hs hm hi hd reduce hr facts
  ⟨fun a b => multiply.mul a (invert.inv b)⟩

theorem Element.factDiv_eq
    (predecessorOne : One E) (predecessorAdd : Add E)
    (predecessorSub : Sub E) (predecessorMul : Mul E)
    (predecessorInv : Inv E) (predecessorDiv : Div E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul)
    (hi : predecessorInv = inv) (hd : predecessorDiv = div)
    (reduce : DensePoly E → DensePoly E) (hr : reduce = nativeReduce)
    (facts : List Fact) :
    @Element.factDiv E Ctx zero dec one add neg sub mul inv div natCast decCtx
      coeffSign parent context predecessorOne predecessorAdd predecessorSub predecessorMul
      predecessorInv predecessorDiv ho ha hs hm hi hd reduce hr facts =
      (inferInstance : Div Carrier) := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hi
  cases hd
  exact Element.cachedDiv_eq reduce hr facts

end Hex.RealClosure.Algebraic
