/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureTheory.FiniteBase
import all KernelReplay.FiniteBase

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.BaseLookup
open FiniteBaseProbe

/-- Retained membership remains available after a long repeated prefix.
The optional trace measures lookup cost; this control asserts success. -/
@[expose] def inputs : List (BaseContext.Element base) :=
  List.replicate 256 delta ++ FiniteBaseProbe.inputs

@[expose] def epsilonAlias : BaseContext.Element base := epsilon

@[expose] def zeroPoly : DensePoly (BaseContext.Element base) := DensePoly.ofCoeffs #[0]
@[expose] def unitPoly : DensePoly (BaseContext.Element base) := DensePoly.ofCoeffs #[1]

@[expose] def twoPoly : DensePoly (BaseContext.Element base) :=
  DensePoly.ofCoeffs #[((1 + 1 : Nat) : BaseContext.Element base)]

@[expose] def computedTwoPoly : DensePoly (BaseContext.Element base) :=
  DensePoly.ofCoeffs #[0 + 1 * (0 + ((0 + 1 + 1 : Nat) : BaseContext.Element base) * 1)]

theorem agreement : Transport.Inventory.Agreement (base.partialRead interpretation)
    (base.partialDomain interpretation) BaseContext.Element.sign
    (fun x : ℝ => (SignType.sign x : Int)) inputs := by
  have retained : delta ∈ FiniteBaseProbe.inputs := by decide
  intro value member
  apply FiniteBaseProbe.agreement value
  simp only [inputs, List.mem_append, List.mem_replicate] at member
  rcases member with ⟨_, rfl⟩ | member
  · exact retained
  · exact member

public meta section
open Lean Meta Elab Command

syntax (name := baseLookup) "#base_lookup" : command
@[command_elab baseLookup]
def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    let base ← FiniteData.Base.ofClosed (mkConst ``FiniteBaseProbe.closed)
    let supplier := FiniteData.agreementSupplier (mkConst ``agreement)
    let constants := base.domains (fun _ => pure none)
    let computed ← mkAppM ``DensePoly.coeff #[mkConst ``computedTwoPoly, toExpr (0 : Nat)]
    let computedType := mkApp base.domain computed
    let computedProof ← mkAppM ``Transport.Closed.natCast #[base.closed, toExpr (2 : Nat)]
    kernelCheck `__baseComputedNatural computedType computedProof
    let some computedProof ← constants computedType
      | throwError "computed natural coefficient required a finite inventory"
    kernelCheck `__baseComputedNaturalSupply computedType computedProof
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.naturalMembership,
      levelParams := [], type := computedType, value := computedProof })
    let coefficient ← mkAppM ``DensePoly.coeff #[mkConst ``twoPoly, toExpr (0 : Nat)]
    let requested := mkApp base.domain coefficient
    let some proof ← constants requested
      | throwError "natural coefficient required a finite inventory"
    kernelCheck `__baseNaturalSupply requested proof
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let original ← mkAppM ``Transport.Closed.natCast #[base.closed, n]
      let requested ← inferType original
      let some proof ← constants requested
        | throwError "symbolic natural cast required a finite inventory"
      kernelCheck `__baseSymbolicNatural
        (← mkForallFVars #[n] requested) (← mkLambdaFVars #[n] proof)
    for (polynomial, name) in #[(``zeroPoly, `__baseClosedZero), (``unitPoly, `__baseClosedUnit)] do
      let coefficient ← mkAppM ``DensePoly.coeff #[mkConst polynomial, toExpr (0 : Nat)]
      let requested := mkApp base.domain coefficient
      let some proof ← constants requested
        | throwError "closed-domain constant required a finite inventory"
      kernelCheck name requested proof
    if (← constants (mkApp base.domain (mkConst ``epsilon))).isSome then
      throwError "closed-domain constants supplied an unrelated coefficient"
    let unknownConstant ← mkFreshExprMVar (some (← inferType (mkConst ``epsilon)))
    if (← constants (mkApp base.domain unknownConstant)).isSome then
      throwError "closed-domain constants chose the caller's coefficient metavariable"
    if ← unknownConstant.mvarId!.isAssigned then
      throwError "closed-domain constants assigned the caller's coefficient metavariable"
    let unknownInterpretation ← mkFreshExprMVar (some (← inferType (mkConst ``interpretation)))
    let unknownDomain := base.domain.replace fun expression =>
      if expression == mkConst ``interpretation then some unknownInterpretation else none
    if (← constants (mkApp unknownDomain computed)).isSome then
      throwError "closed natural cast chose the caller's interpretation metavariable"
    if ← unknownInterpretation.mvarId!.isAssigned then
      throwError "closed natural cast assigned the caller's interpretation metavariable"
    let checkInterpretation (supply : FiniteData.Supplier) (value : Expr) (label : String) :
        MetaM Unit := do
      let unknown ← mkFreshExprMVar (some (← inferType (mkConst ``interpretation)))
      let domain := base.domain.replace fun expression =>
        if expression == mkConst ``interpretation then some unknown else none
      if (← supply (mkApp domain value)).isSome then
        throwError "{label} chose the caller's interpretation metavariable"
      if ← unknown.mvarId!.isAssigned then
        throwError "{label} assigned the caller's interpretation metavariable"
    for polynomial in #[``zeroPoly, ``unitPoly] do
      let value ← mkAppM ``DensePoly.coeff #[mkConst polynomial, toExpr (0 : Nat)]
      checkInterpretation constants value "closed constant"
    checkInterpretation supplier (mkConst ``epsilon) "retained coefficient"
    let type := mkApp base.domain (mkConst ``epsilon)
    let before ← IO.getNumHeartbeats
    let some proof ← supplier type
      | throwError "retained coefficient was not found after the finite prefix"
    let supplied ← IO.getNumHeartbeats
    kernelCheck `__baseLookup type proof
    let checked ← IO.getNumHeartbeats
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"base lookup: padding=256 supply_heartbeats={(supplied-before)/1000} kernel_heartbeats={(checked-supplied)/1000}"
        handle.flush
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.membership,
      levelParams := [], type, value := proof })
    let aliasType := mkApp base.domain (mkConst ``epsilonAlias)
    let aliasBefore ← IO.getNumHeartbeats
    let some aliasProof ← supplier aliasType
      | throwError "definitionally equal retained coefficient was rejected"
    let aliasSupplied ← IO.getNumHeartbeats
    kernelCheck `__baseLookupAlias aliasType aliasProof
    let aliasChecked ← IO.getNumHeartbeats
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"base alias lookup: padding=256 supply_heartbeats={(aliasSupplied-aliasBefore)/1000} kernel_heartbeats={(aliasChecked-aliasSupplied)/1000}"
        handle.flush
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.aliasMembership,
      levelParams := [], type := aliasType, value := aliasProof })
    let .defnInfo original ← getConstInfo ``interpretation
      | throwError "base interpretation is not a retained definition"
    let agreementType ← inferType (mkConst ``agreement)
    let rawType := agreementType.replace fun expression =>
      if expression == mkConst ``interpretation then some original.value else none
    unless rawType != agreementType do
      throwError "choice-expression control did not change its interpretation"
    let rawProof ← withTransparency .all do
      mkAppOptM ``id #[some rawType, some (mkConst ``agreement)]
    let bound ← base.bindAgreement rawProof
    let boundType ← inferType bound
    let boundArgs := boundType.getAppArgs
    unless boundArgs[boundArgs.size - 5]! == base.read &&
        boundArgs[boundArgs.size - 4]! == base.domain do
      throwError "retained agreement lost its exact named reader or domain"
    let rebound := FiniteData.agreementSupplier bound
    checkInterpretation rebound (mkConst ``epsilonAlias) "bound coefficient"
    let some reboundProof ← rebound aliasType
      | throwError "bound choice agreement lost the retained coefficient"
    kernelCheck `__baseBoundAgreement aliasType reboundProof
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.boundMembership,
      levelParams := [], type := aliasType, value := reboundProof })
    let leading ← mkAppM ``Transport.Leading #[base.read, mkConst ``FiniteBaseProbe.left]
    let leadingProof ← FiniteData.buildClosed leading (base.supply rebound rebound)
    kernelCheck `__baseBoundLeading leading leadingProof
    withLocalDeclD `localAgreement rawType fun localAgreement => do
      let localBound ← base.bindAgreement localAgreement
      unless localBound.hasFVar do
        throwError "open base agreement lost its caller hypothesis"
      let localArgs := (← inferType localBound).getAppArgs
      unless localArgs[localArgs.size - 5]! == base.read &&
          localArgs[localArgs.size - 4]! == base.domain do
        throwError "open choice agreement lost its exact named reader or domain"
      let localSupplier := FiniteData.agreementSupplier localBound
      let some localProof ← localSupplier type
        | throwError "open base agreement lost its retained coefficient"
      kernelCheck `__baseOpenAgreement
        (← mkForallFVars #[localAgreement] type)
        (← mkLambdaFVars #[localAgreement] localProof)
    withLocalDeclD `otherInterpretation (← inferType (mkConst ``interpretation)) fun other => do
      let otherDomain := base.domain.replace fun expression =>
        if expression == mkConst ``interpretation then some other else none
      unless otherDomain != base.domain do
        throwError "foreign interpretation control did not change its guarded domain"
      if (← supplier (mkApp otherDomain (mkConst ``epsilon))).isSome then
        throwError "coefficient match supplied a different interpretation's domain"
      if (← rebound (mkApp otherDomain (mkConst ``epsilon))).isSome then
        throwError "bound agreement supplied a different interpretation's domain"
      let zero ← mkAppM ``DensePoly.coeff #[mkConst ``zeroPoly, toExpr (0 : Nat)]
      if (← constants (mkApp otherDomain zero)).isSome then
        throwError "closed-domain constant supplied a foreign interpretation's domain"
      if (← constants (mkApp otherDomain computed)).isSome then
        throwError "closed natural cast supplied a foreign interpretation's domain"
      let unknown ← mkFreshExprMVar (some (← inferType (mkConst ``epsilon)))
      if (← supplier (mkApp otherDomain unknown)).isSome then
        throwError "coefficient metavariable supplied a foreign interpretation's domain"
      if ← unknown.mvarId!.isAssigned then
        throwError "rejected coefficient search assigned the caller's metavariable"
      let foreignType := agreementType.replace fun expression =>
        if expression == mkConst ``interpretation then some other else none
      withLocalDeclD `foreignAgreement foreignType fun foreign => do
        let accepted ← observing? (base.bindAgreement foreign)
        if accepted.isSome then
          throwError "base agreement binding accepted a foreign interpretation"
    logInfo "retained base coefficient found after 256 unrelated inventory entries"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- info: retained base coefficient found after 256 unrelated inventory entries -/
#guard_msgs in
#base_lookup

end Hex.RealClosure.Algebraic.KernelReplay.BaseLookup

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.membership

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.naturalMembership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.naturalMembership

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.aliasMembership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.aliasMembership

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.boundMembership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.BaseLookup.boundMembership
