/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.Tactic
public meta import HexRCF.Tactic
public section

namespace CadSampleCosts
open Lean Elab Command Term Meta Hex.RCF

/-- Emit untrusted literal data for the existing RCF checker. -/
syntax "#cad_emit " ident " : " term : command
elab_rules : command
  | `(#cad_emit $name:ident : $goal:term) => liftTermElabM do
    let target ← elabType goal
    synthesizeSyntheticMVarsNoPostponing
    let reflected ← Reify.reifySentence (← instantiateMVars target)
    let some result := build? reflected.sentence
      | throwError "certificate construction failed"
    unless result.verdict && result.certificate.check reflected.sentence do
      throwError "expected an accepted true sentence"
    let render (e : Expr) := withOptions (fun o =>
      o.setBool `pp.fullNames true |>.setBool `pp.deepTerms true
        |>.set `pp.maxSteps (1000000 : Nat) |>.set `format.width (100 : Int)) (ppExpr e)
    let input ← render (← Reify.sentenceExpr reflected.sentence)
    let certificate ← render (← Reify.certificateExpr result.certificate)
    let expected := match result.certificate with
      | .cells data => data.isolations.intervals.size
      | _ => 0
    let pieces := (toString certificate).splitOn "⋯"
    unless pieces.length = expected + 1 do
      throwError "unexpected elided certificate fields"
    logInfo m!"CAD_{name.getId}_INPUT_BEGIN\n{input}\nCAD_{name.getId}_INPUT_END"
    logInfo m!"CAD_{name.getId}_CERT_BEGIN\n{String.intercalate "by decide" pieces}\nCAD_{name.getId}_CERT_END"

/-- Bind a source formula to its reflected literal without running certificate search. -/
syntax "cad_correspondence% " term : term
elab_rules : term
  | `(cad_correspondence% $goal:term) => do
    let target ← elabType goal
    synthesizeSyntheticMVarsNoPostponing
    let reflected ← Reify.reifySentence (← instantiateMVars target)
    return reflected.proof

end CadSampleCosts
