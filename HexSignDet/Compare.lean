/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.CommonProduct
public import HexSignDet.Reencode

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Thom comparison is applicable only to full derivative encodings of the
same literal head. Equal derivative vectors from different heads are rejected. -/
@[expose] def Descriptor.fullOrder {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) : Option Ordering :=
  if left.raw.head = right.raw.head ∧
      left.raw.indices = (List.range left.raw.head.natDegree).map (· + 1) ∧
      right.raw.indices = (List.range right.raw.head.natDegree).map (· + 1) then
    Thom.compareSigns left.raw.signs right.raw.signs
  else none

/-- Acceptance retains the applicability guards and the exact finite rule. -/
theorem Descriptor.fullOrder_eq {sign : E → Int} {context : Ctx}
    {left right : Descriptor E Ctx sign context} {order : Ordering}
    (h : left.fullOrder right = some order) :
    (left.raw.head = right.raw.head ∧
      left.raw.indices = (List.range left.raw.head.natDegree).map (· + 1) ∧
      right.raw.indices = (List.range right.raw.head.natDegree).map (· + 1)) ∧
    Thom.compareSigns left.raw.signs right.raw.signs = some order := by
  unfold fullOrder at h
  split at h
  · rename_i hg
    exact ⟨hg, h⟩
  · contradiction

/-- Cross-polynomial comparison retains both root-preserving re-encodings
and the common-product identities, not just the two final derivative words. -/
structure Comparison {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) where
  common : CommonProduct E Ctx
  commonChecked : common.check context left.raw.head right.raw.head = true
  leftEncoding : Reencoding left common.head .negInf .posInf
  rightEncoding : Reencoding right common.head .negInf .posInf
  order : Ordering
  ordered : leftEncoding.target.fullOrder rightEncoding.target = some order

variable [Neg E] [Inv E] [Div E]

/-- Compare roots through a squarefree common product on the whole line.
The re-encoding queries retain each original open interval, so a root of one
head at the other's endpoint cannot invalidate the common domain. Internal
failures remain diagnostic until producer and Thom totality are proved. -/
def Descriptor.buildComparison {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) : Except BuildError (Comparison left right) :=
  match CommonProduct.build context left.raw.head right.raw.head with
  | .error err => .error err
  | .ok common =>
    match left.buildReencoding common.val.head .negInf .posInf with
    | .error err => .error err
    | .ok none => .error .replay
    | .ok (some l) =>
      match right.buildReencoding common.val.head .negInf .posInf with
      | .error err => .error err
      | .ok none => .error .replay
      | .ok (some r) =>
        match ho : l.target.fullOrder r.target with
        | none => .error .system
        | some order => .ok ⟨common.val, common.property, l, r, order, ho⟩

end Hex.SignDet
