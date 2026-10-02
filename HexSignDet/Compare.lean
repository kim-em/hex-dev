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
failures remain diagnostic; the companion proves that this producer succeeds
and preserves the mathematical order of both selected roots. -/
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

/-- Successful shared construction, both actual re-encodings and the
full-word comparison give the result of the actual comparison producer. -/
theorem Descriptor.buildComparison_of_success {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context)
    (common : {c : CommonProduct E Ctx // c.check context left.raw.head right.raw.head = true})
    (hc : CommonProduct.build context left.raw.head right.raw.head = .ok common)
    (l : Reencoding left common.val.head .negInf .posInf)
    (r : Reencoding right common.val.head .negInf .posInf)
    (hl : left.buildReencoding common.val.head .negInf .posInf = .ok (some l))
    (hr : right.buildReencoding common.val.head .negInf .posInf = .ok (some r))
    (order : Ordering) (ho : l.target.fullOrder r.target = some order) :
    left.buildComparison right = .ok ⟨common.val, common.property, l, r, order, ho⟩ := by
  simp only [Descriptor.buildComparison, hc, hl, hr]
  split
  · rename_i hnone
    simp only [ho] at hnone
    cases hnone
  · rename_i order' ho'
    have he : order' = order := Option.some.inj (ho'.symm.trans ho)
    subst order'
    rfl

/-- Compare completed encodings directly when their stored heads agree.
Different heads retain the checked common-product path. Literal equality is
only a sufficient shortcut: distinct representations of equal polynomials
continue through joint re-encoding. -/
@[expose] def Descriptor.buildOrder {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) : Except BuildError Ordering :=
  if left.raw.head = right.raw.head then
    match left.buildCompletion with
    | .error err => .error err
    | .ok l =>
      match right.buildCompletion with
      | .error err => .error err
      | .ok r =>
        match l.descriptor.fullOrder r.descriptor with
        | some order => .ok order
        | none => .error .system
  else
    match left.buildComparison right with
    | .error err => .error err
    | .ok c => .ok c.order

/-- The direct path uses only the two actual completions and Thom order. -/
theorem Descriptor.buildOrder_ofCompletion {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) (hh : left.raw.head = right.raw.head)
    (l : Completion left) (r : Completion right)
    (hl : left.buildCompletion = .ok l) (hr : right.buildCompletion = .ok r)
    (order : Ordering) (ho : l.descriptor.fullOrder r.descriptor = some order) :
    left.buildOrder right = .ok order := by
  simp [Descriptor.buildOrder, hh, hl, hr, ho]

/-- Different literal heads use the actual common-head comparison record. -/
theorem Descriptor.buildOrder_ofComparison {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) (hh : left.raw.head ≠ right.raw.head)
    (c : Comparison left right) (hc : left.buildComparison right = .ok c) :
    left.buildOrder right = .ok c.order := by
  simp [Descriptor.buildOrder, hh, hc]

/-- The order of two validated roots, using completion for equal stored
heads and checked common-head comparison otherwise. An internal failure
emits a diagnostic and returns `eq`; the companion proves this fallback
unreachable under lawful coefficients. -/
@[expose] def Descriptor.compare {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) : Ordering :=
  match left.buildOrder right with
  | .ok order => order
  | .error err =>
    letI : Inhabited Ordering := ⟨.eq⟩
    panic! s!"Descriptor.compare: internal error {repr err}"

/-- The total operation returns the order from its successful construction. -/
theorem Descriptor.compare_ofBuild {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) (order : Ordering)
    (h : left.buildOrder right = .ok order) : left.compare right = order := by
  simp only [Descriptor.compare, h]

/-- The diagnostic fallback is exactly `eq`, independently of the global
inhabited instance for `Ordering`. Lawful interpretations exclude this case. -/
theorem Descriptor.compare_ofError {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) (err : BuildError)
    (h : left.buildOrder right = .error err) : left.compare right = .eq := by
  simp [Descriptor.compare, h]

end Hex.SignDet
