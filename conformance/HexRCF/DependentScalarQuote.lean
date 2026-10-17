/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.PublicSignPacketValues
public meta import HexRCF.RealCoefficients.ScalarQuote
public meta import HexRCF.RealCoefficients.RationalQuote
public section
namespace Hex.RCF.DependentScalarQuote
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.PublicSignPacket
theorem value {a : Algebraic.Element context}
    (h : (Algebraic.Element.codec RootQuoteTests.base.codec).decode literal = .ok a) : a.sign = 1 := by
  have accepted : (Algebraic.Element.codec RootQuoteTests.base.codec).decode literal = .ok coefficient :=
    RootQuote.read_eq _ _ coefficient_read
  have same := Except.ok.inj (accepted.symm.trans h)
  rw [← same]
  exact coefficient_sign
@[expose] def reader : Option {a : Algebraic.Element context // a.sign = 1} :=
  match h : (Algebraic.Element.codec (context := context) RootQuoteTests.base.codec).decode literal with
  | .error _ => none
  | .ok a => some ⟨a,value h⟩
abbrev secondCodec := RootQuoteTests.base.codec
@[expose] noncomputable def nested : Option (Algebraic.Element context × Algebraic.Element context) :=
  @Except.rec String (Algebraic.Element context)
    (fun result => (Algebraic.Element.codec RootQuoteTests.base.codec).decode literal = result →
      Option (Algebraic.Element context × Algebraic.Element context))
    (fun _ _ => none)
    (fun a _ =>
      @Except.rec String (Algebraic.Element context)
        (fun result => (Algebraic.Element.codec secondCodec).decode literal = result →
          Option (Algebraic.Element context × Algebraic.Element context))
        (fun _ _ => none)
        (fun b _ => some (a,b))
        ((Algebraic.Element.codec secondCodec).decode literal) rfl)
    ((Algebraic.Element.codec RootQuoteTests.base.codec).decode literal) rfl
end Hex.RCF.DependentScalarQuote

public meta section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
namespace Hex.RCF.DependentScalarQuote
run_meta do
  withoutExporting do
    for name in [``reader,``nested] do
      let some input ← unfoldDefinition? (mkConst name)
        | throwError "dependent scalar reader is not exposed"
      let facts ← mkAppM ``List.cons #[mkConst ``Hex.RCF.PublicSignPacket.fact,
        ← mkAppOptM ``List.nil #[some (← inferType (mkConst ``Hex.RCF.PublicSignPacket.fact))]]
      let decoder : RootQuote.DecoderM := ScalarQuote.decoderWith
        (fun _ => pure (some facts))
        (fun expression => liftM (RationalQuote.decoder (mkConst ``Hex.RCF.RootQuoteTests.registry) expression))
      let .ok result ← RootQuote.runWith (RootQuote.quoteOptionWith input decoder)
        | throwError "dependent scalar quotation declined"
      let config : Hex.RealFormula.Reify.Config := {}
      let exactConfig := {config with ring := {config.ring with budget :=
        {config.ring.budget with proofNodes := result.usage.proofNodes}}}
      let .ok exactResult ← RootQuote.runWith (RootQuote.quoteOptionWith input decoder) exactConfig
        | throwError "dependent scalar quotation failed at its exact budget"
      unless exactResult.usage.proofNodes == result.usage.proofNodes do
        throwError "dependent scalar quotation has unstable accounting"
      let small := {config with ring := {config.ring with budget :=
        {config.ring.budget with proofNodes := result.usage.proofNodes-1}}}
      let .error (.budget exhausted) ← RootQuote.runWith (RootQuote.quoteOptionWith input decoder) small
        | throwError "dependent scalar quotation did not exhaust one node below its budget"
      unless exhausted.dimension == .proofNodes do
        throwError "dependent scalar quotation exhausted a different resource"
      let statement ← mkEq input (← mkAppM ``Option.some #[result.value])
      let proof ← Hex.RCF.checkProof `dependentScalar statement result.proof
      withExporting (isExporting := true) do
        addDecl (.thmDecl {
          name := if name == ``reader then `Hex.RCF.DependentScalarQuote.read_checked
            else `Hex.RCF.DependentScalarQuote.nested_checked,
          levelParams := [],type := statement,value := proof})
      logInfo m!"dependent scalar original reader checked {name}; nodes={result.usage.proofNodes}"
end Hex.RCF.DependentScalarQuote
