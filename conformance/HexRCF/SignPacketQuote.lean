/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SelectedRoot.Data
import HexRCF.CellReplay.Algebraic.Scalars
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.RealCoefficients.ScalarPacketQuote
import HexRCF.RealCoefficients.ScalarQuote
import HexRCF.RealCoefficients.RootQuote
import HexRCF.RealCoefficients.RationalQuote
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.SignPacketQuote
open CellReplayTests.Algebraic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

run_meta do
  let codec ← mkAppM ``Tower.Context.codec #[mkConst ``Data.base]
  let decode : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let outcome ← RootQuote.runWith do
    let root ← RootQuote.quoteWith (mkConst ``Data.lowerRead) decode
    addDecl (.defnDecl {
      name := `Hex.RCF.SignPacketQuote.frozen_root,levelParams := [],
      type := ← inferType root.value,value := root.value,hints := .regular 0,safety := .safe})
      (forceExpose := true)
    let rootStatement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``Data.lowerRead])
      (← mkAppM ``Option.some #[mkConst `Hex.RCF.SignPacketQuote.frozen_root])
    Hex.RealFormula.Reify.accountProof root.proof
    let rootProof ← Hex.RCF.checkProof `quotedParent rootStatement root.proof
    addDecl (.thmDecl {
      name := `Hex.RCF.SignPacketQuote.root_read,levelParams := [],
      type := rootStatement,value := rootProof})
    let clean ← mkAppM ``Tower.Context.isClean #[mkConst ``Data.base]
    let context ← mkAppM ``Algebraic.Context.adjoin
      #[mkConst `Hex.RCF.SignPacketQuote.frozen_root,clean]
    addDecl (.defnDecl {
      name := `Hex.RCF.SignPacketQuote.frozen_context,levelParams := [],
      type := ← inferType context,value := context,hints := .regular 0,safety := .safe})
      (forceExpose := true)
    let lowerType ← mkEq (mkConst ``Data.lower) (mkConst `Hex.RCF.SignPacketQuote.frozen_root)
    let lowerProof ← mkAppM ``Option.get_of_eq_some #[mkConst ``Data.lowerAccepted,rootProof]
    Hex.RealFormula.Reify.accountProof lowerProof
    let lowerProof ← Hex.RCF.checkProof `quotedParentIdentity lowerType lowerProof
    let makeContext ← withLocalDeclD `root (← inferType (mkConst ``Data.lower)) fun root => do
      mkLambdaFVars #[root] (← mkAppM ``Algebraic.Context.adjoin #[root,clean])
    let same ← mkAppM ``congrArg #[makeContext,lowerProof]
    Hex.RealFormula.Reify.accountProof makeContext
    Hex.RealFormula.Reify.accountProof same
    let sameType ← mkEq (mkConst ``Data.native) (mkConst `Hex.RCF.SignPacketQuote.frozen_context)
    let same ← Hex.RCF.checkProof `quotedContextIdentity sameType same
    let reader ← mkAppM ``ScalarPacket.read
      #[mkConst ``Data.rational,codec,mkConst ``Data.native,
        mkConst ``Scalars.p0,mkConst ``Scalars.s0,mkConst ``Scalars.g0]
    ScalarPacket.quoteWith reader (mkConst `Hex.RCF.SignPacketQuote.frozen_context) same decode
  let quoted ← match outcome with
    | .ok result => pure result
    | .error error => throwError "supplied sign packet quotation: {Hex.RealFormula.Reify.Error.toMessageData error}"
  for name in #[`Hex.RCF.SignPacketQuote.frozen_root,`Hex.RCF.SignPacketQuote.frozen_context] do
    let .defnInfo info ← getConstInfo name | throwError "frozen declaration missing"
    compileDecl (.defnDecl info) (logErrors := true)
  let reader ← mkAppM ``ScalarPacket.read
    #[mkConst ``Data.rational,codec,mkConst ``Data.native,
      mkConst ``Scalars.p0,mkConst ``Scalars.s0,mkConst ``Scalars.g0]
  unless quoted.usage.proofNodes == 54777 do
    throwError "sign packet accounting changed: {quoted.usage.proofNodes}"
  logInfo m!"sign packet quotation proofNodes={quoted.usage.proofNodes}"
  let declaration := Declaration.defnDecl {
    name := `Hex.RCF.SignPacketQuote.fact,levelParams := [],
    type := ← inferType quoted.value,value := quoted.value,hints := .regular 0,safety := .safe}
  addDecl declaration (forceExpose := true)
  compileDecl declaration (logErrors := true)
  let statement ← mkEq reader (← mkAppM ``Option.some #[mkConst `Hex.RCF.SignPacketQuote.fact])
  let proof ← Hex.RCF.checkProof `quotedSignPacket statement quoted.proof
  addDecl (.thmDecl {
    name := `Hex.RCF.SignPacketQuote.read_checked,levelParams := [],type := statement,value := proof})

theorem sign : fact.sign = -1 := by rfl

theorem lower_eq : Data.lower = frozen_root :=
  Option.get_of_eq_some Data.lowerAccepted root_read

theorem context_eq : Data.native = frozen_context :=
  congrArg (fun root => Algebraic.Context.adjoin root Data.base.isClean) lower_eq

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let variableCount := (← getMCtx).decls.toList.length
  action
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names &&
      (← getMCtx).decls.toList.length == variableCount do
    throwError "sign packet failure retained caller state"

run_meta do
  let codec ← mkAppM ``Tower.Context.codec #[mkConst ``Data.base]
  let reader ← mkAppM ``ScalarPacket.read
    #[mkConst ``Data.rational,codec,mkConst ``Data.native,
      mkConst ``Scalars.p0,mkConst ``Scalars.s0,mkConst ``Scalars.g0]
  let prepared := mkConst ``frozen_context
  let same := mkConst ``context_eq
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let touched ← IO.mkRef false
  let decode : RootQuote.DecoderM := fun expression => do
    unless ← sentinel.mvarId!.isAssigned do
      sentinel.mvarId!.assign (mkNatLit 1)
      let _ ← mkFreshExprMVar (mkConst ``Nat)
    touched.set true
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let action := ScalarPacket.quoteWith reader prepared same decode
  let .ok result ← RootQuote.runWith action
    | throwError "standalone sign packet quotation failed"
  unless (← touched.get) && !(← sentinel.mvarId!.isAssigned) do
    throwError "successful packet quotation did not restore the mutated caller"
  unless result.usage.proofNodes == 32815 do
    throwError "standalone sign packet accounting changed: {result.usage.proofNodes}"
  let statement ← mkEq reader (← mkAppM ``Option.some #[mkConst ``fact])
  let proof ← Hex.RCF.checkProof `standalonePacket statement result.proof
  addDecl (.thmDecl {
    name := `Hex.RCF.SignPacketQuote.standalone_read,levelParams := [],
    type := statement,value := proof})
  let config : Nat → Hex.RealFormula.Reify.Config := fun limit =>
    {ring := {budget := {Hex.Reflect.Budget.default with proofNodes := limit}}}
  let .ok exact ← RootQuote.runWith action (config result.usage.proofNodes)
    | throwError "exact sign packet budget failed"
  unless exact.usage == result.usage do throwError "exact sign packet usage changed"
  touched.set false
  unchanged do
    let .error (.budget exhausted) ←
        RootQuote.runWith action (config (result.usage.proofNodes-1))
      | throwError "one-below sign packet budget did not exhaust"
    unless exhausted.dimension == .proofNodes && exhausted.consumed == 32792 &&
        exhausted.requested == 23 do throwError "wrong sign packet budget boundary"
    logInfo m!"sign packet final exhaustion: {exhausted.consumed}+{exhausted.requested}"
  unless (← touched.get) && !(← sentinel.mvarId!.isAssigned) do
    throwError "exhausted packet quotation did not restore the mutated caller"
  logInfo m!"standalone sign packet proofNodes={result.usage.proofNodes}"
  let invalidArgs := reader.getAppArgs.set! (reader.getAppNumArgs-1)
    (mkApp (mkConst ``Codec.Json.Value.array) (mkConst ``Codec.Json.Values.nil))
  let invalid := mkAppN reader.getAppFn invalidArgs
  unchanged do
    let .error (.providerFailure (.invalidProviderEvidence ⟨key,version⟩ _) _) ←
        RootQuote.runWith (ScalarPacket.quoteWith invalid prepared same decode)
      | throwError "missing sign packet graph did not reject"
    unless key == `Hex.RCF.RealCoefficients.RootQuote && version == 0 do
      throwError "missing sign packet graph failed at another boundary"
  for (label,index,replacement) in #[
      ("sign",reader.getAppNumArgs-2,mkIntLit 1),
      ("polynomial",reader.getAppNumArgs-3,mkConst ``Scalars.p1)] do
    let changed := mkAppN reader.getAppFn (reader.getAppArgs.set! index replacement)
    touched.set false
    unchanged do
      let .error (.providerFailure (.invalidProviderEvidence ⟨key,version⟩ _) _) ←
          RootQuote.runWith (ScalarPacket.quoteWith changed prepared same decode)
        | throwError "valid graph with mismatched {label} was accepted"
      unless key == `Hex.RCF.RealCoefficients.RootQuote && version == 0 do
        throwError "mismatched {label} failed at another boundary"
    unless (← touched.get) && !(← sentinel.mvarId!.isAssigned) do
      throwError "mismatched {label} did not decode and restore the mutated caller"
    logInfo m!"sign packet valid-graph rejection: {label}; caller restored"
  unchanged do
    let candidate := mkExpectedPropHint (← mkEqRefl (mkNatLit 0))
      (← mkEq (mkConst ``Data.native) prepared)
    unless ← withNewMCtxDepth <| isDefEq (← inferType candidate) (← inferType same) do
      throwError "forged context control did not present the expected type hint"
    let probes ← IO.mkRef (0 : Nat)
    let failed ← (fun context state coreContext coreState => do
      try
        let _ ← (RootQuote.runWith (ScalarPacket.quoteWith reader prepared candidate
          (fun expression => do probes.modify (·+1);decode expression)))
          context state coreContext coreState
        pure false
      catch error =>
        if error.isMaxHeartbeat || error.isMaxRecDepth then throw error
        match error with
        | .error _ _ => pure true
        | _ => throw error : MetaM Bool)
    unless failed && (← probes.get) == 0 do
      throwError "forged context proof was accepted or reached packet decoding"

theorem original_accepted :
    (ScalarPacket.read Data.rational Data.base.codec Data.native
      Scalars.p0 Scalars.s0 Scalars.g0).isSome = true := by
  exact congrArg Option.isSome read_checked

def original := ScalarPacket.restore Data.rational Data.base.codec Data.native
  Scalars.p0 Scalars.s0 Scalars.g0 original_accepted

theorem original_read :
    ScalarPacket.read Data.rational Data.base.codec Data.native
      Scalars.p0 Scalars.s0 Scalars.g0 = some original :=
  ScalarPacket.read_restore _ _ _ _ _ _ original_accepted

theorem original_sign : original.sign = -1 := by rfl

/-- The coefficient is decoded using the newly quoted packet alone. -/
def literal : Codec.Json := .array (.cons Scalars.p0 (.cons (.number (-1)) .nil))

run_meta do
  let codec : Q(ValueCodec (Algebraic.Element Data.native)) :=
    q(Algebraic.Element.codec (context := Data.native) Data.base.codec)
  let facts ← mkAppM ``List.cons #[mkConst ``fact,
    ← mkAppOptM ``List.nil #[some (← inferType (mkConst ``fact))]]
  let decode : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let .ok quoted ← RootQuote.runWith
      (ScalarQuote.quoteWith codec facts (mkConst ``literal) decode)
    | throwError "newly quoted packet did not decode its coefficient"
  let declaration := Declaration.defnDecl {
    name := `Hex.RCF.SignPacketQuote.coefficient,levelParams := [],
    type := ← inferType quoted.value,value := quoted.value,hints := .regular 0,safety := .safe}
  addDecl declaration (forceExpose := true)
  compileDecl declaration (logErrors := true)
  let reader := mkApp3 (mkConst ``ValueCodec.decode) (← inferType quoted.value) codec
    (mkConst ``literal)
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[mkConst `Hex.RCF.SignPacketQuote.coefficient])
  let proof ← Hex.RCF.checkProof `coefficientFromPacket statement quoted.proof
  addDecl (.thmDecl {
    name := `Hex.RCF.SignPacketQuote.coefficient_read,levelParams := [],type := statement,value := proof})
  unless quoted.usage.proofNodes == 966 do
    throwError "new packet coefficient accounting changed: {quoted.usage.proofNodes}"
  logInfo m!"coefficient from new packet proofNodes={quoted.usage.proofNodes}"

theorem coefficient_polynomial : coefficient.polynomial =
    DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(-2 : Rat)⟩] : Array Data.base.Value) := by rfl

theorem coefficient_sign : coefficient.sign = -1 := by rfl

private theorem polynomial_value :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(-2 : Rat)⟩] : Array Data.base.Value)) =
        Polynomial.C (-2 : ℝ) * Polynomial.X := by
  ext i
  rw [HexPolyTheory.Interpret.coeff_interpret]
  rcases i with _ | _ | i
  · change Data.rational.value (0 : Data.base.Value) = _
    rw [Data.rationalZero]
    norm_num
  · change Data.rational.value (-2 : Data.base.Value) = _
    rw [Data.rationalNegativeTwo]
    norm_num
  · rw [DensePoly.coeff_eq_zero_of_size_le _ (by change 2 ≤ i+1+1; omega)]
    change Data.rational.value (0 : Data.base.Value) = _
    rw [Data.rationalZero]
    simp

theorem coefficient_value : Data.original.value coefficient = -2 * Real.sqrt 2 := by
  change (Data.rational.root (.base (BaseContext.rational Data.registry))
    Data.lower Data.frozenFrame Data.frameEncoded).value coefficient = _
  erw [Tower.Model.root_value]
  unfold Algebraic.Element.denote
  erw [coefficient_polynomial]
  change (HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
    (DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(-2 : Rat)⟩] : Array Data.base.Value))).eval
      Data.selectedReal = _
  rw [polynomial_value, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Data.selectedSqrt]

/-- Both packet-backed decoding and its real interpretation are consumed. -/
theorem decoded_value :
    ((Algebraic.Element.codec (context := Data.native) Data.base.codec).decode literal).toOption.map
      Data.original.value = some (-2 * Real.sqrt 2) := by
  rw [coefficient_read]
  exact congrArg some coefficient_value

end Hex.RCF.SignPacketQuote
