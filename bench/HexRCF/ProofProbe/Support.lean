/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Tactic
public meta import HexRCF.BenchHash

public section

/-!
Shared imports, canonical cases, and precompiled command elaborators for the
HexRCF fresh-module proof probes. Measured modules import only this support
module; no measured module imports another measured module.
-/

namespace Hex.RCF.ProofProbe

open Lean Elab Command Term Meta

syntax "rcfQuadraticGoal" : term
macro_rules
  | `(rcfQuadraticGoal) => `(∀ x : ℝ, x ^ 2 + 1 > 0)

syntax "rcfDegree10Goal" : term
macro_rules
  | `(rcfDegree10Goal) => `(
      ∀ x : ℝ,
        x ^ 10 + x ^ 7 - x ^ 5 + 2 * x ^ 3 - x + 1 ≠ 0 ∨
          (x ^ 10 + x ^ 9 + x ^ 6 - 2 * x ^ 4 + x ^ 2 - 1 ≤ 0 ∧
           x ^ 10 - x ^ 7 + x ^ 5 - x ^ 3 + x + 2 > 0))

syntax "rcfDegree50Goal" : term
macro_rules
  | `(rcfDegree50Goal) => `(∃ x : ℝ, x ^ 50 - 100 * x ^ 2 + 20 * x - 1 = 0)

syntax "rcfQuadraticSentence" : term
macro_rules
  | `(rcfQuadraticSentence) => `(
      Sentence.forallReal (.atom ⟨
        DensePoly.ofCoeffs #[(1 : Int), 0, 1], .gt⟩))

syntax "rcfDegree10Sentence" : term
macro_rules
  | `(rcfDegree10Sentence) => `(
      Sentence.forallReal (.or
        (.atom ⟨DensePoly.ofCoeffs
          #[(1 : Int), -1, 0, 2, 0, -1, 0, 1, 0, 0, 1], .ne⟩)
        (.and
          (.atom ⟨DensePoly.ofCoeffs
            #[(-1 : Int), 0, 1, 0, -2, 0, 1, 0, 0, 1, 1], .le⟩)
          (.atom ⟨DensePoly.ofCoeffs
            #[(2 : Int), 1, 0, -1, 0, 1, 0, -1, 0, 0, 1], .gt⟩))))

syntax "rcfDegree50Sentence" : term
macro_rules
  | `(rcfDegree50Sentence) => `(
      Sentence.existsReal (.atom ⟨DensePoly.ofCoeffs #[
        (-1 : Int), 20, -100,
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 1], .eq⟩))

def quadraticSentence : Sentence := rcfQuadraticSentence
def degree10Sentence : Sentence := rcfDegree10Sentence
def degree50Sentence : Sentence := rcfDegree50Sentence

inductive Case where
  | quadratic
  | degree10
  | degree50
  deriving DecidableEq

private meta def caseOfIdent (caseStx : Syntax) : CommandElabM Case := do
  match caseStx.getId with
  | `quadratic => return .quadratic
  | `degree10 => return .degree10
  | `degree50 => return .degree50
  | _ => throwErrorAt caseStx
      "expected one of 'quadratic', 'degree10', or 'degree50'"

private meta unsafe def evalSentenceUnsafe (expr : Expr) :
    MetaM (Except String Sentence) :=
  try
    return .ok (← evalExpr Sentence (mkConst ``Sentence) expr)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalSentenceUnsafe]
private meta opaque evalSentenceCore (expr : Expr) :
    MetaM (Except String Sentence)

private meta def evalSentence (expr : Expr) : MetaM Sentence := do
  match ← evalSentenceCore expr with
  | .ok sentence => return sentence
  | .error msg =>
      throwError "rcf proof probe: failed to evaluate the reflected sentence\n{msg}"

private meta def expectedSentence : Case → MetaM Sentence
  | .quadratic => evalSentence (mkConst ``quadraticSentence)
  | .degree10 => evalSentence (mkConst ``degree10Sentence)
  | .degree50 => evalSentence (mkConst ``degree50Sentence)

private meta def Case.sentenceHash : Case → UInt64
  | .quadratic => 18299206717047047745
  | .degree10 => 8690280657240424051
  | .degree50 => 5026187539705201033

private meta def Case.certificateHash : Case → UInt64
  | .quadratic => 9571910545552258391
  | .degree10 => 2309428790428157609
  | .degree50 => 14503462794369963085

private meta def requireExpected (case : Case) (actual : Sentence) : MetaM Unit := do
  unless actual = (← expectedSentence case) do
    throwError "rcf proof probe: reflected sentence does not match the fixed case"
  unless hash actual = case.sentenceHash do
    throwError "rcf proof probe: reflected sentence checksum changed"

/-- Reify a source proposition and check that it produced the fixed reflected case. -/
syntax "rcf_reify_probe " ident " : " term : command

elab_rules : command
  | `(rcf_reify_probe $caseStx:ident : $goal:term) => do
      let case ← caseOfIdent caseStx
      liftTermElabM do
        let target ← elabType goal
        synthesizeSyntheticMVarsNoPostponing
        let target ← instantiateMVars target
        let reflected ← Reify.reifySentence target
        requireExpected case reflected.sentence
        let expected ← Reify.sentenceExpr (← expectedSentence case)
        unless ← isDefEq reflected.expr expected do
          throwError "rcf proof probe: reflected expression does not match the literal"

/-- Elaborate a reflected input, build its certificate, and validate its true verdict. -/
syntax "rcf_search_probe " ident " : " term : command

elab_rules : command
  | `(rcf_search_probe $caseStx:ident : $sentenceStx:term) => do
      let case ← caseOfIdent caseStx
      liftTermElabM do
        let sentenceExpr ← elabTermEnsuringType sentenceStx (some (mkConst ``Sentence))
        synthesizeSyntheticMVarsNoPostponing
        let sentence ← evalSentence (← instantiateMVars sentenceExpr)
        requireExpected case sentence
        let some result := build? sentence
          | throwError "rcf proof probe: certificate construction failed"
        unless result.verdict do
          throwError "rcf proof probe: the fixed sentence unexpectedly evaluated to false"
        unless result.certificate.check sentence do
          throwError "rcf proof probe: the built certificate failed replay"
        unless hash result.certificate = case.certificateHash do
          throwError "rcf proof probe: certificate checksum changed"

/-- Replay a literal certificate through the public checker and soundness theorem. -/
syntax "rcf_replay% " term " with " term : term

elab_rules : term
  | `(rcf_replay% $sentenceStx:term with $certificateStx:term) => do
      let sentence ← elabTermEnsuringType sentenceStx (some (mkConst ``Sentence))
      let certificate ← elabTermEnsuringType certificateStx
        (some (mkConst ``Certificate))
      synthesizeSyntheticMVarsNoPostponing
      let sentence ← instantiateMVars sentence
      let certificate ← instantiateMVars certificate
      let check ← mkAppM ``Certificate.check #[sentence, certificate]
      let checkType ← mkAppM ``Eq #[check, mkConst ``Bool.true]
      let checked ← mkDecideProof checkType
      mkAppM ``check_sound #[sentence, certificate, checked]

/-- Development-only emitter used to generate committed literal certificate macros. -/
syntax "#rcf_emit_certificate " ident : command

elab_rules : command
  | `(#rcf_emit_certificate $caseStx:ident) => do
      let case ← caseOfIdent caseStx
      liftTermElabM do
        let sentence ← expectedSentence case
        let some result := build? sentence
          | throwError "rcf proof probe: certificate construction failed"
        unless result.verdict && result.certificate.check sentence do
          throwError "rcf proof probe: cannot emit an unaccepted certificate"
        let rendered ← withOptions (fun options =>
            options.setBool `pp.fullNames true
              |>.setBool `pp.deepTerms true
              |>.set `pp.maxSteps (1000000 : Nat)
              |>.set `format.width (100 : Int)) do
          ppExpr (← Reify.certificateExpr result.certificate)
        let expectedProofs := match result.certificate with
          | .cells data => data.isolations.intervals.size
          | _ => 0
        let pieces := (toString rendered).splitOn "⋯"
        unless pieces.length = expectedProofs + 1 do
          throwError "rcf proof probe: certificate printer omitted a non-order term"
        let source := String.intercalate "by decide" pieces
        logInfo m!"RCF_CERT_{caseStx.getId}_BEGIN\n{source}\nRCF_CERT_{caseStx.getId}_END"

#guard decide quadraticSentence == some true
#guard decide degree10Sentence == some true
#guard decide degree50Sentence == some true

end Hex.RCF.ProofProbe
