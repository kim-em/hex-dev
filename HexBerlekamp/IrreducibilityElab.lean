/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.FactorPolyElab
public import HexBerlekamp.FactorPolyElab

public section

/-!
The `irreducibility` term elaborator and tactic.

`irreducibility f` elaborates to a proof of `Hex.FpPoly.Irreducible f`
(further input types via providers): the compiled Rabin certificate generator
runs at elaboration time, and the emitted proof applies
`Berlekamp.irreducible_of_checkMonicCert_scale` to reified literal data, so
the kernel replays only the certificate check.

Tactic forms: `irreducibility f` adds `this : … .Irreducible f`,
`irreducibility h : f` names it `h`, and bare `irreducibility` closes a goal
of the form `FpPoly.Irreducible e` (providers extend the goal shapes).
-/

namespace Hex.FactorTactic

open Lean Meta Elab

/-- Instance-carrying core of the `irreducibility` elaboration for
`f : FpPoly p`: returns the proof of `Hex.FpPoly.Irreducible f` as a raw
`Expr` over reified literal data. -/
meta def elabFpIrredCore (tactic : String) (p : Nat)
    [Hex.ZMod64.Bounds p] (hpt : Hex.Nat.isPrimeTrial p = true)
    (pE boundsE fE : Expr) : MetaM Expr := do
      let hp : Hex.Nat.Prime p := Hex.Nat.isPrimeTrial_isPrime hpt
      let f ← evalFpPoly tactic p pE boundsE fE
      let fLit := Hex.CertReify.reifyFpPolyOfNats pE boundsE
        (Hex.CertReify.fpCoeffNats f)
      unless ← isDefEq fLit fE do
        throwError "{tactic}: the polynomial{indentExpr fE}\
            \nevaluates to{indentExpr fLit}\
            \nbut is not definitionally transparent to the elaborator (an \
            imported definition without `@[expose]`?); the kernel could not \
            check the emitted certificate against it"
      if f.size = 0 then
        throwError "{tactic}: the zero polynomial is not irreducible"
      if f.size = 1 then
        throwError "{tactic}: the polynomial{indentExpr fE}\
            \nis a nonzero constant, hence a unit over F_{p}, not irreducible"
      checkReplayBudget tactic p f.size
      let (unit, m) := Hex.FpPoly.normalizeMonic f
      if hmonic : Hex.DensePoly.leadingCoeff m = 1 then
        match Hex.Berlekamp.buildIrreducibilityCertificate? m (by exact hmonic) with
        | none =>
            let (_, factors) := fpFactorSearch p hp f
            throwError "{tactic}: the polynomial{indentExpr fE}\
                \nis not irreducible over F_{p}: factor_poly finds \
                {factors.length} irreducible factors (with multiplicity)"
        | some cert =>
            let mE := Hex.CertReify.reifyFpPolyOfNats pE boundsE
              (Hex.CertReify.fpCoeffNats m)
            let cE := Hex.CertReify.reifyZMod64 pE boundsE unit.toNat
            let certE := Hex.CertReify.reifyRabinCert cert
            -- Untrusted-search self-checks before emitting anything.
            unless decide (unit = 0) = false &&
                Hex.DensePoly.beqCoeffs (Hex.DensePoly.scale unit m) f &&
                Hex.Berlekamp.checkMonicCert m cert do
              throwError "{tactic}: internal error: the generated certificate \
                  fails its own checks; please report this"
            return mkApp10
              (mkConst ``Hex.Berlekamp.irreducible_of_checkMonicCert_scale)
              pE boundsE fE mE cE certE
              Hex.CertReify.reflTrue Hex.CertReify.reflFalse
              Hex.CertReify.reflTrue Hex.CertReify.reflTrue
      else
        throwError "{tactic}: internal error: non-monic normalization; \
            please report this"

/-- Dispatch the `irreducibility` elaboration for `f : FpPoly p`. -/
meta def elabIrreducibilityFp (tactic : String) (p : Nat)
    (pE boundsE fE : Expr) : MetaM Expr := do
  if hpt : Hex.Nat.isPrimeTrial p = true then
    if h1 : 0 < p then
      if h2 : p < 2 ^ 31 then
        @elabFpIrredCore tactic p ⟨h1, h2⟩ hpt pE boundsE fE
      else
        throwError "{tactic}: internal error: modulus over the ZMod64 bound \
            despite a Bounds instance"
    else
      throwError "{tactic}: internal error: zero modulus despite a Bounds \
          instance"
  else
    throwError "{tactic}: the modulus {p} is not prime; irreducibility over \
        Z/{p} needs a prime field"

/-- Elaborate an `irreducibility` argument and produce the proof, dispatching
to providers for non-`FpPoly` input types. -/
meta def elabIrreducibilityCore (stx : Syntax) (t : Syntax)
    (expectedType? : Option Expr) : Term.TermElabM Expr := do
  let pE ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let pE ← instantiateMVars pE
  checkClosed "irreducibility" pE
  let ty ← inferType pE
  match ← classify ty with
  | .fp p pE' boundsE _ _ _ =>
      elabIrreducibilityFp "irreducibility" p pE' boundsE pE
  | _ =>
      dispatch (fun prov => prov.irreducibility? stx pE ty expectedType?)
        (fun declines =>
          throwError (unsupportedMessage "irreducibility" ty declines))

/-- `irreducibility f` elaborates to a proof that `f` is irreducible
(`Hex.FpPoly.Irreducible f` for `f : FpPoly p`; providers add further input
types). -/
syntax (name := irreducibilityTerm) "irreducibility" term:max : term

@[term_elab irreducibilityTerm] meta def elabIrreducibility : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(irreducibility $t) => do
        let e ← elabIrreducibilityCore stx t expectedType?
        Term.ensureHasType expectedType? e
    | _ => Elab.throwUnsupportedSyntax

/-- Try to close a goal of the form `Hex.FpPoly.Irreducible e` natively;
return `false` when the goal has a different shape. -/
meta def goalIrredFp (goal : MVarId) : Tactic.TacticM Bool := do
  goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    let fn := tgt.getAppFn
    unless fn.isConstOf ``Hex.FpPoly.Irreducible && tgt.getAppNumArgs == 3 do
      return false
    let args := tgt.getAppArgs
    let (pE, boundsE, fE) := (args[0]!, args[1]!, args[2]!)
    let some p := pE.nat? |
      throwError "irreducibility: the modulus in the goal{indentExpr tgt}\
          \nis not a numeral"
    checkClosed "irreducibility" fE
    let proof ← elabIrreducibilityFp "irreducibility" p pE boundsE fE
    unless ← isDefEq (← inferType proof) tgt do
      throwError "irreducibility: the certified statement\
          {indentExpr (← inferType proof)}\
          \nis not definitionally equal to the goal{indentExpr tgt}"
    goal.assign proof
    Tactic.replaceMainGoal []
    return true

/-- Tactic forms of `irreducibility`: bare `irreducibility` closes a goal of
the form `… .Irreducible e`; `irreducibility f` adds the proof as `this`;
`irreducibility h : f` names it `h`. -/
syntax (name := irreducibilityTac)
  "irreducibility" (atomic(ident " : "))? (term:max)? : tactic

@[tactic irreducibilityTac] meta def evalIrreducibilityTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| irreducibility) => do
        let goal ← Tactic.getMainGoal
        if ← goalIrredFp goal then
          return
        -- Providers get the goal next; collect decline diagnostics.
        let mut declines : Array MessageData := #[]
        for prov in (← providers) do
          match ← prov.goalIrred? goal with
          | .success e =>
              goal.assign e
              Tactic.replaceMainGoal []
              return
          | .notApplicable => pure ()
          | .declined why => declines := declines.push why
          | .fatal msg => throwError msg
        let tgt ← goal.getType
        throwError (unsupportedMessage "irreducibility" tgt declines ++
          m!"\n\nGoal-mode `irreducibility` expects a goal of the form \
            `… .Irreducible e`.")
    | `(tactic| irreducibility $t:term) => do
        let proof ← Tactic.withMainContext do
          elabIrreducibilityCore stx t none
        Tactic.liftMetaTactic fun g => do
          let ty ← inferType proof
          let (_, g) ← (← g.assert `this ty proof).intro1P
          return [g]
    | `(tactic| irreducibility $h:ident : $t:term) => do
        let proof ← Tactic.withMainContext do
          elabIrreducibilityCore stx t none
        Tactic.liftMetaTactic fun g => do
          let ty ← inferType proof
          let (_, g) ← (← g.assert h.getId ty proof).intro1P
          return [g]
    | _ => Elab.throwUnsupportedSyntax

end Hex.FactorTactic
