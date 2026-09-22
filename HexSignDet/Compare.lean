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
