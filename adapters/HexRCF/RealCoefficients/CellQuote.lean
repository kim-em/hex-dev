/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellReplay
public import HexRCF.RealCoefficients.CompleteReplay
public import HexRCF.RealCoefficients.CellOperations
public meta import HexRCF.RealCoefficients.Quote
public meta import HexRCF.RealCoefficients.RootQuote
public meta import HexRCF.RealCoefficients.RowPacketQuote
public meta section
namespace Hex.RCF.RealCoefficients.CellQuote
open Lean Meta

initialize registerTraceClass `Hex.RCF.CellQuote

/-- Retain a checked reader result as data, so later stages use its exact
dependent indices without reducing the original reader again. -/
private def freeze (reader : Expr) (decode : RootQuote.DecoderM) :
    Hex.RealFormula.Reify.ReifyM (Expr × Expr) := do
  trace[Hex.RCF.CellQuote] "reader begins: {reader.getAppFn.constName?}; nodes={(← get).budget.consumed.proofNodes}"
  let result ← RootQuote.quoteWith reader decode
  trace[Hex.RCF.CellQuote] "reader checked: {reader.getAppFn.constName?}; nodes={(← get).budget.consumed.proofNodes}"
  let kind ← inferType result.value
  Hex.RealFormula.Reify.accountProof kind
  Hex.RealFormula.Reify.accountProof result.value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `CellData)
  let value ← mkAuxDefinition name kind result.value (compile := false)
  let equation ← mkAppM ``RootQuote.read_eq #[reader,result.value,result.proof]
  let type ← whnf (← inferType reader)
  let accepted ← mkAppOptM ``Except.ok
    #[some type.getAppArgs[0]!,some type.getAppArgs[1]!,some value]
  let target ← mkEq reader accepted
  Hex.RealFormula.Reify.accountProof target
  Hex.RealFormula.Reify.accountProof equation
  return (value,← Hex.RCF.checkProof `CellQuote.reader target
    (mkExpectedPropHint equation target))

/-- Retain the supplied schema once rather than copying its syntax into every
root and row conversion. The original checker remains the proof target. -/
private def shareFormula (formula : Expr) : Hex.RealFormula.Reify.ReifyM Expr := do
  if formula.isConst || formula.hasFVar || formula.hasLooseBVars then return formula
  let kind ← inferType formula
  Hex.RealFormula.Reify.accountProof kind
  Hex.RealFormula.Reify.accountProof formula
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `CellFormula)
  mkAuxDefinition name kind formula (compile := false)

/-- Build a dependent finite function from its checked entries, including the
empty family. Constructor reduction identifies every literal index. -/
private partial def buildFamily (family : Expr) (entries : Array Expr) :
    Hex.RealFormula.Reify.ReifyM Expr := Core.withIncRecDepth do
  Hex.RealFormula.Reify.charge .proofNodes 1
  if entries.isEmpty then
    withLocalDeclD `i (← mkAppM ``Fin #[mkNatLit 0]) fun i => do
      let value ← mkAppOptM ``Fin.elim0 #[some (mkApp family i),some i]
      mkLambdaFVars #[i] value
  else
    let count := entries.size-1
    let tailFamily ← withLocalDeclD `i (← mkAppM ``Fin #[mkNatLit count]) fun i => do
      mkLambdaFVars #[i] (mkApp family (← mkAppM ``Fin.succ #[i]))
    let tail ← buildFamily tailFamily (entries.extract 1 entries.size)
    mkAppOptM ``Fin.cases #[some (mkNatLit count),some family,some entries[0]!,some tail]

/-- Quote every member directly, before the dependent collection introduces
its vector and alignment proofs. All child work stays in the enclosing budget. -/
private def collectRows (reader : Expr) (decode : RootQuote.DecoderM) :
    Hex.RealFormula.Reify.ReifyM (Expr × Expr) := do
  let .forallE _ domain _ _ ← whnf (← inferType reader)
    | throwError "rcf: expected an indexed cell reader"
  unless domain.isAppOfArity ``Fin 1 do throwError "rcf: expected finite cell indices"
  let bound := domain.appArg!
  let some count ← getNatValue? (← withTransparency .all (whnf bound))
    | throwError "rcf: cell count is not a closed numeral"
  let family ← withLocalDeclD `i domain fun i => do
    let type ← whnf (← inferType (mkApp reader i))
    unless type.isAppOfArity ``Except 2 do throwError "rcf: indexed cell reader lost its result"
    mkLambdaFVars #[i] type.getAppArgs[1]!
  let mut values : Array Expr := #[]
  let mut proofs : Array Expr := #[]
  for i in [:count] do
    Hex.RealFormula.Reify.charge .proofNodes 1
    let index ← mkAppM ``Fin.mk #[mkNatLit i,← mkDecideProof (← mkLt (mkNatLit i) bound)]
    let (value,proof) ← freeze (mkApp reader index).headBeta decode
    values := values.push value
    proofs := proofs.push proof
  trace[Hex.RCF.CellQuote] "finite family begins: {count} entries"
  let value ← instantiateMVars (← buildFamily family values)
  let kind ← inferType value
  Hex.RealFormula.Reify.accountProof kind
  Hex.RealFormula.Reify.accountProof value
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `CellFamily)
  let value ← mkAuxDefinition name kind value (compile := false)
  let equations ← withLocalDeclD `i domain fun i => do
    let source := mkApp reader i
    let type ← whnf (← inferType source)
    let output ← mkAppOptM ``Except.ok
      #[some type.getAppArgs[0]!,some type.getAppArgs[1]!,some (mkApp value i)]
    mkLambdaFVars #[i] (← mkEq source output)
  let proof ← instantiateMVars (← buildFamily equations proofs)
  let target ← withLocalDeclD `i domain fun i => mkForallFVars #[i] (mkApp equations i).headBeta
  Hex.RealFormula.Reify.accountProof target
  Hex.RealFormula.Reify.accountProof proof
  let checked ← Hex.RCF.checkProof `CellQuote.family target proof
  trace[Hex.RCF.CellQuote] "finite family checked: {count} entries; nodes={(← get).budget.consumed.proofNodes}"
  return (value,checked)

/-- Restore the literal layout, quote each section and sector, and compose
their checked pointwise equations without normalizing the finite collector. -/
private def readCellsWith (operations codec guards roots values formula packet guarded : Expr)
    (decode : RootQuote.DecoderM) : Hex.RealFormula.Reify.ReifyM (Expr × Expr) := do
  let rootList ← mkAppM ``RootReplay.Result.roots #[roots]
  let count ← mkAppM ``List.length #[rootList]
  let cuts ← mkAppM ``Nat.add #[count,mkNatLit 1]
  let (fields,layout) ← freeze (← mkAppM ``Hex.SignDet.Codec.tuple #[mkNatLit 2,packet]) decode
  let field := fun (i : Nat) => do
    let index ← mkAppM ``Fin.mk
      #[mkNatLit i,← mkDecideProof (← mkLt (mkNatLit i) (mkNatLit 2))]
    mkAppM ``Vector.get #[fields,index]
  let (sectionFields,sectionLayout) ← freeze
    (← mkAppM ``Hex.SignDet.Codec.tuple #[count,← field 0]) decode
  let (sectorFields,sectorLayout) ← freeze
    (← mkAppM ``Hex.SignDet.Codec.tuple #[cuts,← field 1]) decode
  let sectionReader ← withLocalDeclD `i (← mkAppM ``Fin #[count]) fun i => do
    let root ← mkAppM ``List.get #[rootList,i]
    let data ← mkAppM ``Vector.get #[sectionFields,i]
    mkLambdaFVars #[i] (← mkAppM ``CellOperations.formulaRow
      #[operations,codec,root,values,formula,data])
  let (sections,sectionChecked) ← collectRows sectionReader decode
  let sectorReader ← withLocalDeclD `cut (← mkAppM ``Fin #[cuts]) fun cut => do
    let data ← mkAppM ``Vector.get #[sectorFields,cut]
    mkLambdaFVars #[cut] (← mkAppM ``CellOperations.formulaSector
      #[operations,codec,roots,cut,values,formula,data])
  let (sectors,sectorChecked) ← collectRows sectorReader decode
  let sectorValues ← withLocalDeclD `cut (← mkAppM ``Fin #[cuts]) fun cut => do
    mkLambdaFVars #[cut] (← mkAppM ``SectorReplay.Result.sector #[mkApp sectors cut])
  let sectorRows ← withLocalDeclD `cut (← mkAppM ``Fin #[cuts]) fun cut => do
    mkLambdaFVars #[cut] (← mkAppM ``SectorReplay.Result.row #[mkApp sectors cut])
  let constructor ← mkConstWithFreshMVarLevels ``CellReplay.Evidence.mk
  let arguments : Array (Option Expr) ← forallTelescope (← inferType constructor) fun binders _ =>
    binders.mapM fun binder => do
      let name := (← getFVarLocalDecl binder).userName
      return match name with
        | `roots => some roots
        | `values => some values
        | `formula => some formula
        | `sections => some sections
        | `sectors => some sectorValues
        | `sectorRows => some sectorRows
        | _ => none
  let data ← mkAppOptM' constructor arguments
  let kind ← inferType data
  Hex.RealFormula.Reify.accountProof kind
  Hex.RealFormula.Reify.accountProof data
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `CellRows)
  let data ← mkAuxDefinition name kind data (compile := false)
  let candidate ← mkAppM ``CellOperations.readCells_of_parts
    #[operations,codec,guards,roots,values,formula,packet,fields,sectionFields,sectorFields,
      sections,sectors,guarded,layout,sectionLayout,sectorLayout,sectionChecked,sectorChecked]
  let reader ← mkAppM ``CellOperations.readCells
    #[operations,codec,guards,roots,values,formula,packet]
  let type ← whnf (← inferType reader)
  let accepted ← mkAppOptM ``Except.ok
    #[some type.getAppArgs[0]!,some type.getAppArgs[1]!,some data]
  let target ← mkEq reader accepted
  Hex.RealFormula.Reify.accountProof target
  Hex.RealFormula.Reify.accountProof candidate
  return (data,← Hex.RCF.checkProof `CellQuote.cells target (mkExpectedPropHint candidate target))

/-- Quote the supplied-operation checker in three stages: the complete root
table, its dependent cells, and the strict fold. Each stage consumes the same
reflection budget. Their checked equations compose at the original checker;
false remains a diagnostic result and a rejected stage is terminal. The caller
provides the transaction, for example through `RootQuote.runWith`. -/
private def replayCore (program : Expr) (decode : RootQuote.DecoderM := fun _ => pure none) :
    Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let program ← instantiateMVars program
  Hex.RealFormula.Reify.accountProof program
  let program ← Hex.RCF.checkExpr `CellQuote.program program
  Meta.check program
  unless program.getAppFn.isConstOf ``CellOperations.check do
    throwError "rcf: expected the supplied-operation complete checker"
  let arguments := program.getAppArgs
  let info ← getFunInfoNArgs program.getAppFn arguments.size
  unless arguments.size == info.paramInfo.size do
    throwError "rcf: incomplete supplied-operation checker"
  let inputs := arguments.zipIdx |>.filterMap fun (argument,index) =>
    if info.paramInfo[index]!.binderInfo.isExplicit then some argument else none
  unless inputs.size == 9 do throwError "rcf: incorrect supplied-operation checker arity"
  let operations := inputs[0]!
  let codec := inputs[1]!
  let values := inputs[2]!
  let formula ← shareFormula inputs[3]!
  let guards := inputs[4]!
  let cert := inputs[5]!
  let quantifier := inputs[6]!
  let core ← mkAppM ``RadicalCert.core #[cert]
  let polynomialType ← whnf (← inferType core)
  unless polynomialType.getAppFn.isConstOf ``Hex.DensePoly do
    throwError "rcf: radical core is not a dense polynomial"
  let element := polynomialType.getAppArgs[0]!
  let lower := mkApp (mkConst ``Hex.Endpoint.negInf [.zero]) element
  let upper := mkApp (mkConst ``Hex.Endpoint.posInf [.zero]) element
  let mut arithmetic : Array Expr := #[]
  for field in #[``Hex.RealClosure.Replay.Operations.one,``Hex.RealClosure.Replay.Operations.add,
      ``Hex.RealClosure.Replay.Operations.sub,``Hex.RealClosure.Replay.Operations.mul,
      ``Hex.RealClosure.Replay.Operations.natCast,``Hex.RealClosure.Replay.Operations.one_eq,
      ``Hex.RealClosure.Replay.Operations.add_eq,``Hex.RealClosure.Replay.Operations.sub_eq,
      ``Hex.RealClosure.Replay.Operations.mul_eq,``Hex.RealClosure.Replay.Operations.natCast_eq] do
    arithmetic := arithmetic.push (← mkAppM field #[operations])
  let rootReader ← mkAppM ``RootReplay.readWith
    (#[codec,guards,core,lower,upper] ++ arithmetic ++ #[inputs[7]!])
  let (roots,rootChecked) ← freeze rootReader decode
  let readSame ← mkAppM ``RootReplay.readWith_eq
    (#[codec,guards,core,lower,upper] ++ arithmetic ++ #[inputs[7]!])
  let rootAccepted ← mkEqTrans (← mkEqSymm readSame) rootChecked
  let guarded ← mkAppM ``RootReplay.read_guards
    #[codec,guards,core,lower,upper,inputs[7]!,roots,rootAccepted]
  let (cells,cellsChecked) ← readCellsWith operations codec guards roots values formula
    inputs[8]! guarded decode
  trace[Hex.RCF.CellQuote] "cells checked; nodes={(← get).budget.consumed.proofNodes}"
  let fold ← mkAppM ``CellOperations.fold
    #[operations,values,formula,guards,cert,roots,cells,quantifier]
  trace[Hex.RCF.CellQuote] "fold begins; nodes={(← get).budget.consumed.proofNodes}"
  let verdict ← RootQuote.quoteWith fold decode
  trace[Hex.RCF.CellQuote] "fold checked; nodes={(← get).budget.consumed.proofNodes}"
  let foldChecked ← mkAppM ``RootQuote.read_eq #[fold,verdict.value,verdict.proof]
  let equation ← mkAppM ``CellOperations.check_of_parts
    (inputs ++ #[roots,cells,verdict.value,rootChecked,cellsChecked,foldChecked])
  let original ← mkAppM ``Except.toOption #[program]
  let statement ← mkEq original (← mkAppM ``Option.some #[verdict.value])
  let candidate ← mkAppM ``RootQuote.read_some #[program,verdict.value,equation]
  Hex.RealFormula.Reify.accountProof candidate
  let proof ← Hex.RCF.checkProof `CellQuote.replay statement candidate
  return ⟨verdict.value,proof,(← get).budget.consumed⟩

/-- Quote the exact complete checker with one attempt-local cache of checked
row graphs. All child work consumes the caller's reflection budget. -/
def replayWith (program : Expr) (decode : RootQuote.DecoderM := fun _ => pure none) :
    Hex.RealFormula.Reify.ReifyM RootQuote.Result :=
  RowQuote.withDecoder decode (fun decoder => replayCore program decoder)

/-- Shared original-source authentication for typed cells and independently
read complete packets. Both entrypoints retain ordered guards and rollback. -/
private def finishWith (packet : Bool) (target checker accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let target ← Hex.RCF.checkExpr `CellQuote.target target
    let checker ← Hex.RCF.checkExpr `CellQuote.checker checker
    let checkerName := if packet then ``CompleteReplay.check else ``CellReplay.check
    unless checker.getAppFn.isConstOf checkerName do
      throwError "rcf: expected the canonical cell checker"
    let arguments := checker.getAppArgs
    let information ← getFunInfoNArgs checker.getAppFn arguments.size
    let mut inputs : Array Expr := #[]
    for i in [:min arguments.size information.paramInfo.size] do
      if information.paramInfo[i]!.binderInfo.isExplicit then inputs := inputs.push arguments[i]!
    unless inputs.size == (if packet then 8 else 7) do
      throwError "rcf: incorrect cell checker arity"
    let offset := if packet then 1 else 0
    let values := inputs[offset]!
    let matrix := inputs[offset+1]!
    let guards := inputs[offset+2]!
    let quantifier := inputs[if packet then 5 else 6]!
    let model ← Hex.RCF.checkExpr `CellQuote.model model
    let resultType ← whnf (← inferType checker)
    let trueResult := mkAppN (mkConst ``Except.ok [.zero, .zero])
      (resultType.getAppArgs.push (mkConst ``Bool.true))
    let accepted ← Hex.RCF.checkProof `CellQuote.accepted (← mkEq checker trueResult) accepted
    let source ← match ← Reify.prepare target with
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
      | .ok source => pure source
    unless guardIdentities.size == source.divisors.size do
      throwError "rcf: cell checker has a different original divisor identity count"
    let length ← mkAppM ``List.length #[guards]
    let count ← mkEq length (mkNatLit source.divisors.size)
    let decision ← mkDecide count
    let result ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) decision)
    unless result.isConstOf ``Bool.true do
      throwError "rcf: cell checker has a different original divisor count"
    let _ ← Hex.RCF.checkProof `CellQuote.guardCount count (← mkDecideProof count)
    let proofInputs := #[model] ++ inputs
    let domains ← mkAppM (if packet then ``CompleteReplay.check_domains else ``CellReplay.check_domains)
      ((proofInputs.push (mkConst ``Bool.true)).push accepted)
    let domains ← Hex.RCF.checkProof `CellQuote.domains (← inferType domains) domains
    for i in [:source.divisors.size] do
      let bound ← mkDecideProof (← mkLt (mkNatLit i) length)
      let index ← mkAppM ``Fin.mk #[mkNatLit i, bound]
      let guard ← mkAppM ``List.get #[guards, index]
      let interpreted ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model, guard]
      let identity ← Hex.RCF.checkProof `CellQuote.guardIdentity
        (← mkEq interpreted source.divisors[i]!) guardIdentities[i]!
      let member ← mkAppM ``List.get_mem #[guards, index]
      let nonzero ← mkAppM' domains #[guard, member]
      let realZero := (← inferType nonzero).getAppArgs.back!
      let comparison ← withLocalDeclD `value (← inferType interpreted) fun value => do
        let body ← mkAppM ``Ne #[value, realZero]
        mkAppM ``congrArg #[← mkLambdaFVars #[value] body, identity]
      let conclusion ← mkAppM ``Eq.mp #[comparison, nonzero]
      let _ ← Hex.RCF.checkProof `CellQuote.divisor
        (← mkAppM ``Ne #[source.divisors[i]!, realZero]) conclusion
    let .forallE _ domain _ _ ← whnf (← inferType values)
      | throwError "rcf: cell coefficients are not a finite valuation"
    let valuation ← withLocalDeclD `i domain fun i => do
      let value ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model, mkApp values i]
      mkLambdaFVars #[i] value
    let valuationIdentity ← Hex.RCF.checkProof `CellQuote.valuationIdentity
      (← mkEq valuation source.valuation) valuationIdentity
    let formula ← mkAppM ``Hex.RealFormula.Prenex.quant
      #[quantifier, ← mkAppM ``Hex.RealFormula.Prenex.matrix #[matrix]]
    let formulaIdentity ← Quote.formulaEquality formula source.formula
    let formulaIdentity ← Hex.RCF.checkProof `CellQuote.formulaIdentity
      (← mkEq formula source.formula) formulaIdentity
    let sentence ← mkAppM (if packet then ``CompleteReplay.check_sound else ``CellReplay.check_sound)
      (proofInputs.push accepted)
    let sentence ← Hex.RCF.checkProof `CellQuote.sentence
      (← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation]) sentence
    let formulaCongr ← withLocalDeclD `sentence (← inferType formula) fun sentence => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[sentence, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[sentence] body, formulaIdentity]
    let fixed ← mkAppM ``Eq.mp #[formulaCongr, sentence]
    let valuationCongr ← withLocalDeclD `valuation (← inferType source.valuation) fun valuation => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[valuation] body, valuationIdentity]
    let specialized ← mkAppM ``Eq.mp #[valuationCongr, fixed]
    let proof ← mkAppM ``Iff.mp #[source.proof, specialized]
    Hex.RCF.checkProof `CellQuote.source source.original proof)
    (fun result => unless result.isSome do saved.restore)
  return result
/-- Quote a checked typed cell fold at the freshly reified original goal. -/
def finish (target checker accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr :=
  finishWith false target checker accepted model valuationIdentity guardIdentities

/-- Quote independently checked full root/cell packets, retaining the same
source formula, fixed valuation, original divisor and state-restoration checks. -/
def finishPacket (target checker accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr :=
  finishWith true target checker accepted model valuationIdentity guardIdentities

/-- Quote an owner's supplied-operation acceptance proof at the original goal.
The exact `accept?` equation is kernel checked before transport to the canonical
checker. A reduced conversion proof receives its original expected type without
asking the elaborator to repeat the reader reduction. All original source,
valuation and divisor checks remain those of `finishPacket`. -/
def finishOperations (target program accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr := do
  let saved ← saveState
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `CellQuote)
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <|
      withOptions (fun options => debug.skipKernelTC.set (Elab.async.set options false) false) do
    let program ← Hex.RCF.checkExpr `CellQuote.program program
    let function := program.getAppFn
    unless function.isConstOf ``CellOperations.accept? do
      throwError "rcf: expected the supplied-operation complete checker"
    let arguments := program.getAppArgs
    let information ← getFunInfoNArgs function arguments.size
    let mut count := 0
    let mut operation : Option Nat := none
    for i in [:min arguments.size information.paramInfo.size] do
      if information.paramInfo[i]!.binderInfo.isExplicit then
        count := count + 1
        if operation.isNone then operation := some i
    unless count == 9 && arguments.size == information.paramInfo.size do
      throwError "rcf: incorrect supplied-operation checker arity"
    let some operationIndex := operation
      | throwError "rcf: supplied-operation checker lost its dictionary"
    let statement ← mkEq program (← mkAppM ``Option.some #[mkConst ``Unit.unit])
    let accepted ← Hex.RCF.checkProof `CellQuote.operationAcceptance statement
      (mkExpectedPropHint accepted statement)
    -- These declarations have the same parameters; the canonical checker
    -- omits only the first explicit argument, the operation dictionary.
    let equivalent := mkAppN (mkConst ``CellOperations.accept?_iff function.constLevels!) arguments
    let accepted ← mkAppM ``Iff.mp #[equivalent,accepted]
    let canonical := arguments.extract 0 operationIndex ++ arguments.extract (operationIndex+1) arguments.size
    let checker := mkAppN (mkConst ``CompleteReplay.check function.constLevels!) canonical
    finishPacket target checker accepted model valuationIdentity guardIdentities) fun outcome => do
      match outcome with
      | some _ => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | none => saved.restore
  return result

end Hex.RCF.RealCoefficients.CellQuote
