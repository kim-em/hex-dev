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
private meta def proveRCFGoal (target : Expr) : MetaM Expr := do
  let reflected ← Reify.reifySentence target
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

/-- Decide a supported singly quantified univariate real polynomial goal by
building and replaying a literal certificate. -/
syntax (name := rcfTac) "rcf" : tactic

/-- Elaborate `rcf` by constructing and replaying a checked certificate. -/
@[tactic rcfTac] meta def evalRCFTac : Tactic := fun stx => do
  match stx with
  | `(tactic| rcf) =>
      let goal ← getMainGoal
      goal.withContext do
        let target ← instantiateMVars (← goal.getType)
        let proof ← proveRCFGoal target
        goal.assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

end Hex.RCF
