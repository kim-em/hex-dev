/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.KernelReplay
public meta import Lean.Meta.Transform
import all HexRealClosure.Algebraic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeValues

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Rebuild a native literal from its stored polynomial and tag. The packet
producer uses this helper only on the fields of an existing valid element;
its checked reader keeps the original request and its original proof objects. -/
@[expose] def restoreValue (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) : Element context :=
  (Element.restore? p claimed).getD 0

/-- Rechecking an existing value preserves its exact stored representation,
including noncanonical representatives and canonical zero. -/
theorem restoreValue_eq (context : Context E Ctx coeffSign parent) (value : Element context) :
    restoreValue context value.polynomial value.sign = value := by
  cases stored : value.stored with
  | none =>
    have vanished : value = 0 := Element.ext (stored.trans Element.stored_zero.symm)
    subst value
    simp [restoreValue, Element.restore?, Element.polynomial_zero, Element.sign_zero]
  | some literal =>
    have restored : Element.restore? value.polynomial value.sign = some value := by
      simpa only [Element.polynomial, Element.sign, stored] using
        Element.restore?_stored value literal stored
    simp only [restoreValue, restored, Option.getD_some]

public meta section
open Lean Meta

/-- Recover open literal data before native packet production. Complete closed
inputs retain their original expressions. Open proof-bearing coefficient objects
are replaced by native reconstruction of the same stored polynomial and tag.
Original owner expressions control the types; the caller
keeps the untouched request for ordinary-kernel checking of the output data.
Opaque runtime locals remain locals and are rejected by packet production. -/
partial def prepare (owners : Array Expr) (expression : Expr) (fuel : Nat := 128) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasSorry then throwError "incomplete native value input"
  go fuel expression
where
  original (owner : Expr) : MetaM Expr := do
    for retained in owners do
      if ← withTransparency .all (isDefEq owner retained) then return retained
    if owner.hasFVar then throwError "native value has no closed original owner"
    return owner
  go (remaining : Nat) (expression : Expr) : MetaM Expr := do
    let remaining + 1 := remaining | throwError "native value reconstruction exhausted its depth bound"
    -- Closed inputs already have their compiled definitions and erased
    -- proofs. Let the native producer evaluate their data; reducing a closed
    -- polynomial here can instead execute all coefficient work in Meta.
    if !expression.hasFVar then return expression
    transform expression (pre := fun term => do
      if term.isFVar || (← isProof term) || (← isProp term) then return .done term
      if term.getAppFn.isConstOf ``Element then
        let owner ← original term.getAppArgs.back!
        return .done (← mkAppM ``Element #[owner])
      let type ← withTransparency .all (whnf (← inferType term))
      if type.getAppFn.isConstOf ``Element then
        if !term.hasFVar then return .done term
        let owner ← original type.getAppArgs.back!
        let polynomial ← withTransparency .all
          (reduce (← mkAppM ``Element.polynomial #[term]) (explicitOnly := true))
        let claimed ← withTransparency .all
          (reduce (← mkAppM ``Element.sign #[term]) (explicitOnly := true))
        return .done (← mkAppM ``restoreValue #[owner, ← go remaining polynomial, claimed])
      if type.getAppFn.isConstOf ``DensePoly then
        let coefficients ← withTransparency .all
          (reduce (← mkAppM ``DensePoly.toArray #[term]) (explicitOnly := true))
        return .done (← mkAppM ``DensePoly.ofCoeffs #[← go remaining coefficients])
      if !term.hasFVar then return .done term
      return .continue)

end
end Hex.RealClosure.Algebraic.KernelReplay.NativeValues
