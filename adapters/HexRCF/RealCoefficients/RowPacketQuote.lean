/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RowQuote
public meta import HexRCF.RealCoefficients.RootQuote
public section
namespace Hex.RCF.RealCoefficients.RowQuote
open Hex Hex.SignDet Hex.RealClosure
variable {E Ctx : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [DecidableEq Ctx] {sign : E → Int} {binding : Ctx}

/-- Compose independently checked parsing, query binding and graph selection. -/
theorem read_eq (value : ValueCodec E) (context : ValueCodec Ctx)
    (root : Descriptor E Ctx sign binding) (queries : List (DensePoly E))
    (packet : Codec.Json) (data : Algebraic.SignEvidence E Ctx)
    (selected : SelectedSigns root data.queries)
    (decoded : (Algebraic.SignEvidence.codec value context root.raw).decode packet = .ok data)
    (same : data.queries = queries)
    (checked : data.graph.selectedSigns? root data.queries data.values = some selected) :
    RowOperations.read value context sign binding root queries packet = .ok (same ▸ selected) := by
  simp only [RowOperations.read,decoded,bind,Except.bind]
  rw [dite_eq_left same,checked]

@[expose] def queryDecision (test : Bool) : Except Hex.RCF.RealCoefficients.Replay.Error Bool :=
  if test then .ok true else .ok false

theorem queryDecision_true (test : Bool)
    (checked : (queryDecision test).toOption = some true) : test = true := by
  cases test <;> simp [queryDecision,Except.toOption] at *

end Hex.RCF.RealCoefficients.RowQuote

public meta section
namespace Hex.RCF.RealCoefficients.RowQuote
open Lean Meta Hex Hex.SignDet Hex.RealClosure
initialize registerTraceClass `Hex.RCF.RowQuote

private def freeze (reader : Expr) (decode : RootQuote.DecoderM) :
    Hex.RealFormula.Reify.ReifyM (Expr × Expr) := do
  let quoted ← RootQuote.quoteWith reader decode
  let kind ← inferType quoted.value
  Hex.RealFormula.Reify.accountProof kind
  Hex.RealFormula.Reify.accountProof quoted.value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `RowStageData)
  let value ← mkAuxDefinition name kind quoted.value (compile := false)
  let strict ← mkAppM ``RootQuote.read_eq #[reader,quoted.value,quoted.proof]
  let resultType ← whnf (← inferType reader)
  let accepted ← mkAppOptM ``Except.ok
    #[some resultType.getAppArgs[0]!,some resultType.getAppArgs[1]!,some value]
  let target ← mkEq reader accepted
  Hex.RealFormula.Reify.accountProof target
  Hex.RealFormula.Reify.accountProof strict
  return (value,← Hex.RCF.checkProof `RowStage.reader target (mkExpectedPropHint strict target))


private structure MemoEntry where
  key : Array Expr
  value : Expr
  proof : Expr
private structure MemoState where
  entries : Array MemoEntry := #[]
  hits : Nat := 0
  misses : Nat := 0
private abbrev Cache := IO.Ref MemoState
private def restore (cache : Cache) (reader : Expr) (decode : RootQuote.DecoderM) :
    Hex.RealFormula.Reify.ReifyM (Expr × Expr) := do
  let mut key := #[reader.getAppFn]
  for argument in reader.getAppArgs do
    Hex.RealFormula.Reify.charge .proofNodes 1
    let argument ← withTransparency .all (whnf argument)
    Hex.RealFormula.Reify.accountProof argument
    key := key.push argument
  for entry in (← cache.get).entries do
    Hex.RealFormula.Reify.charge .proofNodes 1
    if entry.key == key then
      let target ← mkEq reader (← mkAppM ``Option.some #[entry.value])
      Hex.RealFormula.Reify.accountProof target
      Hex.RealFormula.Reify.accountProof entry.proof
      let checked ← Hex.RCF.checkProof `RowMemo.reused target
        (mkExpectedPropHint entry.proof target)
      cache.modify fun s => {s with hits := s.hits+1}
      return (entry.value,checked)
  let quoted ← RootQuote.quoteOptionWith reader decode
  let kind ← inferType quoted.value
  Hex.RealFormula.Reify.accountProof kind
  Hex.RealFormula.Reify.accountProof quoted.value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `RowMemoData)
  let value ← mkAuxDefinition name kind quoted.value (compile := false)
  let target ← mkEq reader (← mkAppM ``Option.some #[value])
  Hex.RealFormula.Reify.accountProof target
  Hex.RealFormula.Reify.accountProof quoted.proof
  let checked ← Hex.RCF.checkProof `RowMemo.original target
    (mkExpectedPropHint quoted.proof target)
  cache.modify fun s => {s with
    entries := s.entries.push ⟨key,value,checked⟩
    misses := s.misses+1}
  return (value,checked)

/-- Preserve the descriptor's exact operation indices. Reinferring equal
cached operations would ask conversion to unfold canonical arithmetic. -/
private def atRoot (name : Name) (root : Expr) (arguments : Array Expr) :
    Hex.RealFormula.Reify.ReifyM Expr := do
  Hex.RealFormula.Reify.charge .proofNodes 1
  let kind ← whnf (← inferType root)
  unless kind.getAppFn.isConstOf ``Descriptor do
    throwError "rcf: row reader lost its descriptor index"
  Hex.RealFormula.Reify.accountProof kind
  mkAppOptM name ((kind.getAppArgs ++ arguments).map some)

private def quoteRow (cache : Cache) (reader : Expr) (decode : RootQuote.DecoderM) :
    Hex.RealFormula.Reify.ReifyM Expr := do
  unless reader.getAppFn.isConstOf ``RowOperations.read do throwError "expected original row reader"
  let args := reader.getAppArgs
  let info ← getFunInfoNArgs reader.getAppFn args.size
  let inputs := args.zipIdx |>.filterMap fun (arg,i) =>
    if info.paramInfo[i]!.binderInfo.isExplicit then some arg else none
  unless inputs.size == 7 do throwError "row reader explicit arity changed: {inputs.size}"
  let raw ← atRoot ``Descriptor.raw inputs[4]! #[inputs[4]!]
  let codec ← mkAppM ``Algebraic.SignEvidence.codec #[inputs[0]!,inputs[1]!,raw]
  let parsed ← mkAppM ``ValueCodec.decode #[codec,inputs[6]!]
  let (data,decoded) ← freeze parsed decode
  let queries ← mkAppM ``Algebraic.SignEvidence.queries #[data]
  let equality ← mkEq queries inputs[5]!
  let decision ← mkDecide equality
  let guardReader ← mkAppM ``queryDecision #[decision]
  let guarded ← RootQuote.quoteWith guardReader decode
  unless guarded.value.isConstOf ``Bool.true do
    Hex.RealFormula.Reify.abort (.providerFailure (.invalidProviderEvidence
      ⟨`Hex.RCF.RealCoefficients.RowQuote,0⟩ "literal row query binding rejected") #[])
  let decided ← mkAppM ``queryDecision_true #[decision,guarded.proof]
  let same ← mkAppM ``of_decide_eq_true #[decided]
  Hex.RealFormula.Reify.accountProof equality
  Hex.RealFormula.Reify.accountProof same
  let same ← Hex.RCF.checkProof `RowStage.queries equality same
  let values ← mkAppM ``Algebraic.SignEvidence.values #[data]
  let graph ← mkAppM ``Algebraic.SignEvidence.graph #[data]
  let head ← mkAppM ``RawDescriptor.head #[raw]
  let lower ← mkAppM ``RawDescriptor.lower #[raw]
  let upper ← mkAppM ``RawDescriptor.upper #[raw]
  let validation ← atRoot ``Dag.validate? inputs[4]! #[head,lower,upper,graph]
  let (memo,validated) ← restore cache validation decode
  let index ← mkAppM ``Dag.root #[graph]
  let selection ← atRoot ``SelectedSigns.ofMemo? inputs[4]! #[inputs[4]!,queries,values,memo,index]
  let quoted ← RootQuote.quoteOptionWith selection decode
  let sameSelection ← atRoot ``Dag.selectedSigns_memo inputs[4]!
    #[inputs[4]!,queries,values,graph,memo,validated]
  let checked ← mkEqTrans (← mkEqSymm sameSelection) quoted.proof
  let candidate ← atRoot ``read_eq inputs[4]!
    #[inputs[0]!,inputs[1]!,inputs[4]!,inputs[5]!,inputs[6]!,data,quoted.value,
      decoded,same,checked]
  Hex.RealFormula.Reify.accountProof candidate
  let target ← inferType candidate
  Hex.RealFormula.Reify.accountProof target
  Hex.RCF.checkProof `RowStage.original target candidate

/-- Share checked graph validation within one quotation attempt. Every key
retains the function, operations, sign, context, head, endpoints and full graph.
A reused equation is kernel checked at the exact new reader before selection.
The cache is local to this call; failures never select a different solver. -/
def withDecoder (decode : RootQuote.DecoderM)
    (consume : RootQuote.DecoderM → Hex.RealFormula.Reify.ReifyM α) :
    Hex.RealFormula.Reify.ReifyM α := do
  let cache ← IO.mkRef ({} : MemoState)
  let result ← consume fun expression => do
    if expression.getAppFn.isConstOf ``RowOperations.read then
      return some (← quoteRow cache expression decode)
    decode expression
  let state ← cache.get
  trace[Hex.RCF.RowQuote] "checked graph memos: reused={state.hits}; validated={state.misses}"
  return result
end Hex.RCF.RealCoefficients.RowQuote
