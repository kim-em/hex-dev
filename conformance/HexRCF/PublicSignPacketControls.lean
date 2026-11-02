/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.PublicSignPacket
public meta import HexRCF.PublicSignPacket
public meta import HexRCF.RealCoefficients.RootQuote

public section

/-! Reject changed scalar queries and full context identities at both graph
nodes and nested moments. Compiled rejection is checked separately from
ordinary quotation refusal and caller-state restoration. -/

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.PublicSignPacket

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

@[expose] def foreignSignature : Tower.Signature :=
  RootQuoteTests.base.signature.extend (.array .nil)

theorem foreign_ne : foreignSignature ≠ RootQuoteTests.base.signature := by
  intro same
  have lengths := congrArg (fun s : Tower.Signature => s.roots.length) same
  simp only [foreignSignature, Tower.Signature.extend, List.length_append,
    List.length_singleton] at lengths
  omega

@[expose] def otherPolynomial : Codec.Json := .array (.cons RootQuoteTests.j5
  (.cons (.array (.cons (.number 0) (.cons (.number 2) (.cons (.number 1) .nil)))) .nil))

private meta def arrayExpr (items : Array Expr) : Expr :=
  mkApp (mkConst ``Codec.Json.Value.array)
    (items.toList.foldr (fun item rest => mkApp2 (mkConst ``Codec.Json.Values.cons) item rest)
      (mkConst ``Codec.Json.Values.nil))

private meta def arrayItems (expression : Expr) : MetaM (Array Expr) := do
  let expression ← whnf expression
  unless expression.isAppOfArity ``Codec.Json.Value.array 1 do
    throwError "control expected a JSON array"
  let mut rest := expression.appArg!
  let mut items := #[]
  while true do
    let node ← whnf rest
    if node.isConstOf ``Codec.Json.Values.nil then return items
    unless node.isAppOfArity ``Codec.Json.Values.cons 2 do
      throwError "control expected a JSON array spine"
    items := items.push node.getAppArgs[0]!
    rest := node.getAppArgs[1]!
  throwError "unreachable array control"

private meta def changedGraph (nested : Bool) : MetaM Expr := do
  let graph ← arrayItems (mkConst ``evidence)
  let entries ← arrayItems graph[2]!
  unless !entries.isEmpty do throwError "control needs a nonempty graph"
  let entry ← arrayItems entries[0]!
  let node ← arrayItems entry[0]!
  let foreign ← mkAppM ``ValueCodec.encode
    #[mkConst ``Tower.Signature.codec,mkConst ``foreignSignature]
  let node ← if nested then do
    let moments ← arrayItems node[7]!
    unless !moments.isEmpty do throwError "control needs a nested moment"
    let moment ← arrayItems moments[0]!
    pure (node.set! 7 (arrayExpr (moments.set! 0 (arrayExpr (moment.set! 0 foreign)))))
  else pure (node.set! 0 foreign)
  return arrayExpr (graph.set! 2
    (arrayExpr (entries.set! 0 (arrayExpr (entry.set! 0 (arrayExpr node))))))

private meta def controlDecoder : RootQuote.DecoderM := fun expression => do
  if let .proj ``Decidable 0 decision := expression then
    let type ← whnf (← inferType decision)
    if type.isAppOfArity ``Decidable 1 then
      let proposition := type.appArg!
      let expected ← mkEq (mkConst ``foreignSignature)
        (← mkAppM ``Tower.Context.signature #[mkConst ``RootQuoteTests.base])
      if ← withNewMCtxDepth <| withTransparency .all <| isDefEq proposition expected then
        return some (mkApp3 (mkConst ``decide_eq_false) proposition decision (mkConst ``foreign_ne))
  decoder expression

run_meta do
  for (name,nested) in #[(`Hex.RCF.PublicSignPacket.foreignNode,false),
      (`Hex.RCF.PublicSignPacket.foreignMoment,true)] do
    let declaration := Declaration.defnDecl {
      name,levelParams := [],type := mkConst ``Codec.Json.Value,
      value := ← changedGraph nested,hints := .regular 0,safety := .safe}
    addDecl declaration (forceExpose := true)
    compileDecl declaration (logErrors := true)
  let codec ← mkAppM ``Tower.Context.codec #[mkConst ``RootQuoteTests.base]
  for (label,polynomial,sign,graph) in #[
      ("sign",mkConst ``polynomial,mkIntLit (-1),mkConst ``evidence),
      ("polynomial",mkConst ``otherPolynomial,mkIntLit 1,mkConst ``evidence),
      ("empty graph",mkConst ``polynomial,mkIntLit 1,arrayExpr #[]),
      ("node context",mkConst ``polynomial,mkIntLit 1,mkConst `Hex.RCF.PublicSignPacket.foreignNode),
      ("moment context",mkConst ``polynomial,mkIntLit 1,mkConst `Hex.RCF.PublicSignPacket.foreignMoment)] do
    let reader ← mkAppM ``ScalarPacket.read
      #[mkConst ``model,codec,mkConst ``context,polynomial,sign,graph]
    let observed ← mkAppM ``Option.isSome #[reader]
    unless !(← evalExpr Bool (mkConst ``Bool) observed) do
      throwError "compiled public packet accepted changed {label}"
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let .error (.providerFailure (.invalidProviderEvidence ⟨key,version⟩ _) _) ←
        RootQuote.runWith (RootQuote.quoteOptionWith reader fun expression => do
          unless ← sentinel.mvarId!.isAssigned do sentinel.mvarId!.assign (mkNatLit 9)
          let _ ← mkFreshExprMVar (mkConst ``Nat)
          controlDecoder expression) quoteConfig
      | throwError "public quotation did not reject changed {label}"
    unless key == `Hex.RCF.RealCoefficients.RootQuote && version == 0 do
      throwError "changed {label} failed at a different boundary"
    let after ← getMCtx
    unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter &&
        before.eAssignment.toList == after.eAssignment.toList &&
        before.lAssignment.toList == after.lAssignment.toList &&
        before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "changed {label} retained caller state"
    logInfo m!"public packet compiled rejection/quotation refusal/caller restoration: {label}"

end Hex.RCF.PublicSignPacket
