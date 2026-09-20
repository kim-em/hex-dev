/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Reify
public meta import HexRCF.DecisionCheck

public section

/-!
# The `rcf` tactic

The tactic runs certificate construction as compiled meta code, embeds the
result as literal data, and closes true goals only through the kernel-facing
Boolean checker and its soundness theorem. False verdicts are diagnostics.
-/

namespace Hex.RCF

open Lean Elab Tactic Meta

/-- An optional handler either declines the source syntax, reports a terminal
failure (including false verdicts and exhausted/rejected replay), or proposes
an ordinary proof of the original goal. -/
meta inductive HandlerResult where
  /-- This handler does not recognize the source syntax. -/
  | declined
  /-- Recognized syntax failed; no subsequent handler may run. -/
  | failed (message : MessageData)
  /-- A candidate proof, checked by the base before goal assignment. -/
  | proved (proof : Expr)

/-- Optional coefficient solvers receive the unchanged source target. -/
meta abbrev Handler := Expr → MetaM HandlerResult

private meta initialize handlerExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.flatten
    addEntryFn := fun entries name => entries.push name
  }

meta initialize registerBuiltinAttribute {
  name := `rcf_handler
  descr := "register an optional closed-coefficient handler for rcf"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    ensureAttrDeclIsMeta `rcf_handler decl kind
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `rcf_handler kind
    let info ← getConstInfo decl
    unless info.levelParams.isEmpty &&
        (← MetaM.run' <| isDefEq info.type (mkConst ``Handler)) do
      throwAttrDeclNotOfExpectedType `rcf_handler decl info.type (mkConst ``Handler)
    modifyEnv fun env => handlerExt.addEntry env decl
}

/-- Registered declaration names, deduplicated and sorted by `Name.lt`.
Lookup order is independent of attribute and import order. -/
meta def handlerNames : CoreM (Array Name) := do
  let names := (handlerExt.getState (← getEnv)).qsort Name.lt
  return names.foldl (fun acc name =>
    if acc.back? == some name then acc else acc.push name) #[]

private meta unsafe def evalHandlerUnsafe (name : Name) : MetaM Handler :=
  evalConst Handler name

@[implemented_by evalHandlerUnsafe]
private meta opaque evalHandler (name : Name) : MetaM Handler

/-- Try handlers transactionally. Even successful handlers export only their
fully instantiated proof, not assignments to metavariables in the target.
Exceptions and structured failures are terminal; only `declined` continues. -/
private meta def dispatchHandlers (target : Expr)
    (reason : Reify.UnsupportedCoefficient) : MetaM Expr := do
  for name in ← handlerNames do
    let saved ← saveState
    let result : HandlerResult ← try
        let handler ← evalHandler name
        match ← handler target with
        | .proved proof => pure (.proved (← instantiateMVars proof))
        | .failed message => pure (.failed (← addMessageContext message))
        | .declined => pure .declined
      finally saved.restore
    match result with
    | .declined => pure ()
    | .failed message => throwError message
    | .proved proof =>
        if proof.hasMVar then
          throwError "rcf: handler {name} returned an unresolved proof"
        check proof
        unless ← withNewMCtxDepth <| isDefEq (← inferType proof) target do
          throwError "rcf: handler {name} proposed a proof of a different goal"
        return proof
  throwError reason.message

/-- Whether a cell participates in the sentence's quantifier fold. -/
private meta def relevantCell (sentence : Sentence) (data : CellsCert)
    (cell : Cell data.isolations.intervals.size) : Bool :=
  match sentence, data.iocCmps with
  | .forallReal _, _ | .existsReal _, _ => true
  | .forallIoc a b _, some cmps | .existsIoc a b _, some cmps =>
      Cell.meetsIocOn a b cmps cell
  | _, none => false

/-- Locate the first checked universal counterexample cell. -/
private meta def failingCell? (sentence : Sentence) (data : CellsCert) :
    Option (Cell data.isolations.intervals.size) :=
  (Cell.all data.isolations.intervals.size).find? fun cell =>
    relevantCell sentence data cell &&
      data.signs.evalCell? sentence data.isolations cell == some false

/-- Render the exact sample or isolating interval attached to a cell. -/
private meta def describeCell (data : CellsCert)
    (cell : Cell data.isolations.intervals.size) : MessageData :=
  match cell with
  | .open cut =>
      m!"open cell at dyadic sample {data.isolations.openPoint cut |>.toRat}"
  | .root i =>
      let interval := data.isolations.intervals[i]
      m!"root cell isolated in ({interval.lower.toRat}, {interval.upper.toRat}]"

/-- Diagnostic for a checked false verdict. False results never enter the
proof-producing path. -/
private meta def falseMessage (sentence : Sentence)
    (certificate : Certificate) : MessageData :=
  match sentence with
  | .existsReal _ | .existsIoc _ _ _ =>
      "rcf: the existential sentence is false. Every relevant decomposition\n\
        cell was checked and found false, so there is no witness"
  | .forallReal _ | .forallIoc _ _ _ =>
      match certificate with
      | .cells data =>
          match failingCell? sentence data with
          | some cell => m!"rcf: the universal sentence is false on the {describeCell data cell}"
          | none => "rcf: the universal sentence is false on a checked decomposition cell"
      | .noRoots _ | .constants =>
          "rcf: the universal sentence is false on the sole open cell at dyadic sample 0"
      | .emptyIoc =>
          "rcf: internal error: an empty-domain universal produced false"

/-- Construct the proof for a supported true sentence. The compiled builder
selects evidence, while `Certificate.check` and `check_sound` are the only
certificate trust boundary. -/
private meta def proveRational (target : Expr) (reflected : Reify.SentenceResult) : MetaM Expr := do
  let sentence ← Reify.sentenceExpr reflected.sentence
  unless ← isDefEq sentence reflected.expr do
    throwError "rcf: internal runtime/literal sentence mismatch"
  let some result := build? reflected.sentence
    | throwError "rcf: certificate construction failed"
  unless result.verdict do
    throwError (falseMessage reflected.sentence result.certificate)
  unless result.certificate.check reflected.sentence do
    throwError "rcf: internal error: a true builder verdict failed replay"
  let certificate ← Reify.certificateExpr result.certificate
  let check ← mkAppM ``Certificate.check #[sentence, certificate]
  let checkType ← mkAppM ``Eq #[check, mkConst ``Bool.true]
  let checked ← mkDecideProof checkType
  let sound ← mkAppM ``check_sound
    #[sentence, certificate, checked]
  let proof ← mkAppM ``Iff.mp #[reflected.proof, sound]
  unless ← isDefEq (← inferType proof) target do
    throwError "rcf: internal final proof mismatch"
  return proof

/-- Prove a rational goal, or dispatch only a typed closed-coefficient decline.
Every unsuccessful attempt restores its metavariable state, including runtime
exceptions. Existing rational search and replay remain terminal. -/
meta def proveGoal (target : Expr) : MetaM Expr := do
  let saved ← saveState
  let (proof, _) ← tryFinally' (do
    match ← (Reify.recognizeSentence target).run with
    | .ok reflected => proveRational target reflected
    | .error reason => do
        saved.restore
        dispatchHandlers target reason)
    (fun result => unless result.isSome do saved.restore)
  return proof

/-- Decide a supported singly quantified univariate real polynomial goal by
building and replaying a literal certificate. -/
syntax (name := rcfTac) "rcf" : tactic

/-- Elaborate `rcf` by constructing and replaying a checked certificate. -/
@[tactic rcfTac] meta def evalRCFTac : Tactic := fun stx => do
  match stx with
  | `(tactic| rcf) =>
      let saved ← saveState
      let _ ← tryFinally' (do
        let goal ← getMainGoal
        goal.withContext do
          let target ← instantiateMVars (← goal.getType)
          let proof ← proveGoal target
          goal.assign proof
        replaceMainGoal [])
        (fun result => unless result.isSome do saved.restore)
  | _ => throwUnsupportedSyntax

end Hex.RCF
