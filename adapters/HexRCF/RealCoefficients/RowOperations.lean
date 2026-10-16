/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootReplay
public import HexRealClosure.SignEvidence
public import HexSignDet.DescriptorOperations
public section
namespace Hex.RCF.RealCoefficients.RowOperations
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {E : Type} {Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [one : One E] [add : Add E] [sub : Sub E] [mul : Mul E] [nat : NatCast E]

/-- The operation-parametric supplied row reader. It never constructs signs. -/
@[expose] def read (value : ValueCodec E) (context : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (root : @Descriptor E Ctx _ _ one add sub mul nat _ sign binding)
    (queries : List (DensePoly E)) (packet : Codec.Json) :
    Except Replay.Error (@SelectedSigns E Ctx _ _ one add sub mul nat _ sign binding root queries) := do
  let evidence ← match (Algebraic.SignEvidence.codec value context root.raw).decode packet with
    | .error _ => .error .evidence
    | .ok evidence => .ok evidence
  if same : evidence.queries = queries then
    match evidence.graph.selectedSigns? root evidence.queries evidence.values with
    | none => .error .evidence
    | some selected => .ok (same ▸ selected)
  else .error .binding

/-- Change the descriptor and checked row together, retaining literal data. -/
@[expose] def changeOps (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E)
    (otherMul : Mul E) (otherNat : NatCast E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub)
    (hm : otherMul = mul) (hn : otherNat = nat)
    (sign : E → Int) (binding : Ctx)
    (root : @Descriptor E Ctx _ _ otherOne otherAdd otherSub otherMul otherNat _ sign binding)
    (queries : List (DensePoly E))
    (selected : @SelectedSigns E Ctx _ _ otherOne otherAdd otherSub otherMul otherNat _ sign binding root queries) :
    @SelectedSigns E Ctx _ _ one add sub mul nat _ sign binding
      (@Descriptor.changeOps E Ctx _ _ _ one add sub mul nat otherOne otherAdd otherSub otherMul otherNat
        ho ha hs hm hn sign binding root) queries :=
  @SelectedSigns.mk E Ctx _ _ one add sub mul nat _ sign binding _ queries selected.values selected.evidence (by
    cases ho; cases ha; cases hs; cases hm; cases hn
    simpa only [Descriptor.changeOps_self] using selected.accepted)

/-- Retarget equal root and query subjects while retaining the row data. -/
@[expose] def retarget (sign : E → Int) (binding : Ctx)
    {first second : Descriptor E Ctx sign binding} (rootEq : first = second)
    {before after : List (DensePoly E)} (queryEq : before = after)
    (source : SelectedSigns first before) : SelectedSigns second after :=
  ⟨source.values.cast (congrArg List.length queryEq), source.evidence, by
    cases rootEq
    cases queryEq
    exact source.accepted⟩

theorem retarget_values (sign : E → Int) (binding : Ctx)
    {first second : Descriptor E Ctx sign binding} (rootEq : first = second)
    {before after : List (DensePoly E)} (queryEq : before = after)
    (source : SelectedSigns first before) :
    (retarget sign binding rootEq queryEq source).values.toList = source.values.toList := rfl

/-- Equal root/query subjects transport the entire reader result, including
all malformed-input and binding failures. -/
theorem retarget_read (value : ValueCodec E) (context : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx)
    {first second : Descriptor E Ctx sign binding} (rootEq : first = second)
    {before after : List (DensePoly E)} (queryEq : before = after) (packet : Codec.Json) :
    (do
      let source ← read value context sign binding first before packet
      pure (retarget sign binding rootEq queryEq source)) =
      read value context sign binding second after packet := by
  cases rootEq
  cases queryEq
  cases read value context sign binding first before packet with
  | error cause => rfl
  | ok source => cases source; rfl
end Hex.RCF.RealCoefficients.RowOperations
