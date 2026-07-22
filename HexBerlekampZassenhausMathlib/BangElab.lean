/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhausMathlib.FactorProvider
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampZassenhausMathlib.FactorProvider

public section

/-!
The kernel-decide fallbacks `irreducibility!` and `factor_poly!`.

Each bang form first runs the normal certificate pipeline (the same driver
entry points as the plain forms, including all providers). Only when that
fails — balanced inputs outside both the single-prime witness and the
multi-prime degree-obstruction languages, e.g. Swinnerton-Dyer polynomials
or `X⁴+1` — does it fall back to a kernel `decide` through
`Hex.ZPoly.instDecidableIrreducible`: the emitted proof is
`Hex.ZPoly.irreducible_of_decide f (Eq.refl true)` (or its `Polynomial ℤ` /
`Factored` transports), so **the kernel re-runs the Berlekamp-Zassenhaus
factorizer** to verify it.

Two costs follow, stated here because they land on the *calling* module:

- **`import all` closure.** The factorizer's bodies are not `@[expose]`d,
  and the kernel of a downstream module only sees exposed bodies, so the
  calling module must `import all` the executable closure (the
  `HexArith`/`HexModArith`/`HexPoly`/`HexPolyZ`/`HexPolyFp`/`HexBerlekamp`/
  `HexBerlekampZassenhaus`/`HexHensel`/`HexMatrix`/`HexRowReduce` module
  files on the factorize path, plus `Init.Data.Fin.Fold` and the
  `Init.Data.Array` basics — see the header block of
  `HexBerlekampZassenhausMathlib/FactorPolyTests.lean` for a working set).
  The elaborator prechecks kernel reducibility with `Lean.Kernel.whnf` and
  fails with a clear message when the closure is missing, instead of
  leaking a bare kernel type mismatch.
- **Wall clock.** The kernel replay is roughly the compiled factorizer
  re-run by the kernel evaluator, twice (precheck + final check): quartics
  are sub-second, degree 8 takes a few seconds, degree 12 tens of seconds.
  Inputs above dense size `bangBudget` (degree 12) are rejected at
  elaboration time. Inputs that the classical tier declines (routed to the
  lattice tier, whose FFI `lllNative` has no kernel-reducible body) cannot
  be certified this way at any size.

The plain forms never pay these costs: their emitted terms replay only
cheap checkers on literal data, and the factorizer never reaches the
kernel. Prefer them whenever they apply.
-/

namespace HexBerlekampZassenhausMathlib.FactorTactic

open Lean Meta Elab
open HexBerlekampZassenhaus.FactorTactic (evalZPoly checkTransparent)

/-- Dense-size cap (degree + 1) for the kernel factorizer replay: degree 12
already costs tens of seconds of kernel time per input. -/
meta def bangBudget : Nat := 13

/-- Reject inputs whose kernel factorizer replay would be over budget. -/
meta def checkBangBudget (tactic : String) (f : Hex.ZPoly) : MetaM Unit := do
  if f.size > bangBudget then
    throwError "{tactic}: the kernel factorizer replay is capped at dense \
        size {bangBudget} (degree {bangBudget - 1}), but the input has dense \
        size {f.size}; degree 12 already takes tens of seconds of kernel time"

/-- Precheck that the kernel can reduce `decide prop` to `true` in the
current environment, so a missing `import all` closure fails here with a
clear message instead of a bare kernel type mismatch at declaration time. -/
meta def kernelDecideTrue (tactic : String) (prop : Expr) : MetaM Unit := do
  let d ← mkDecide prop
  match Lean.Kernel.whnf (← getEnv) {} d with
  | .ok r =>
      unless r.isConstOf ``Bool.true do
        throwError "{tactic}: the kernel cannot reduce the factorizer replay \
            for{indentExpr prop}\nThe calling module must `import all` the \
            executable closure (see the module docstring of \
            HexBerlekampZassenhausMathlib.BangElab and the header block of \
            HexBerlekampZassenhausMathlib/FactorPolyTests.lean); reduction \
            got stuck at{indentExpr r}"
  | .error _ =>
      throwError "{tactic}: kernel reduction of the factorizer replay \
          for{indentExpr prop}\nfailed (out of budget or a stuck \
          definition); the calling module must `import all` the executable \
          closure (see the module docstring of \
          HexBerlekampZassenhausMathlib.BangElab)"

/-- Shared degenerate-input and budget checks for the bang fallbacks. -/
meta def bangChecks (tactic : String) (fE : Expr) (f : Hex.ZPoly) :
    MetaM Unit := do
  if f.size = 0 then
    throwError "{tactic}: the zero polynomial is not irreducible"
  if Hex.ZPoly.IsUnit f then
    throwError "{tactic}: the polynomial{indentExpr fE}\
        \nis a unit (±1), not irreducible"
  checkBangBudget tactic f
  unless Hex.ZPoly.isIrreducible f do
    let φ := Hex.ZPoly.factorize f
    let count := φ.factors.foldl (fun acc entry => acc + entry.2) 0
    throwError "{tactic}: the polynomial{indentExpr fE}\
        \nis not irreducible over ℤ: factor_poly finds {count} irreducible \
        factors (with multiplicity), scalar {φ.scalar}"

/-- The `irreducibility!` fallback for `Hex.ZPoly` inputs: free-layer
conclusion via one kernel factorizer replay. -/
meta def bangZPolyIrred (tactic : String) (fE : Expr) : MetaM Expr := do
  let f ← evalZPoly tactic fE
  discard <| checkTransparent tactic f fE
  bangChecks tactic fE f
  kernelDecideTrue tactic (mkApp (mkConst ``Hex.ZPoly.Irreducible) fE)
  return mkApp2 (mkConst ``Hex.ZPoly.irreducible_of_decide)
    fE Hex.CertReify.reflTrue

/-- The `irreducibility!` fallback for `Polynomial ℤ` inputs: parse with
proof, then transport the kernel replay through the bridge equation. -/
meta def bangIntIrred (tactic : String) (e : Expr) : MetaM Expr := do
  let (f, fLit, hP) ← parseInput tactic e
  bangChecks tactic e f
  kernelDecideTrue tactic (mkApp (mkConst ``Hex.ZPoly.Irreducible) fLit)
  return mkApp4 (mkConst ``HexBerlekampZassenhausMathlib.irreducible_ofZ_decide)
    e fLit Hex.CertReify.reflTrue hP

/-- The membership-bounded irreducibility proposition
`∀ q ∈ factorsE, Hex.ZPoly.Irreducible q` as an expression. -/
meta def forallIrredProp (factorsE : Expr) : MetaM Expr :=
  withLocalDeclD `q zpolyTy fun q => do
    mkForallFVars #[q] (← mkArrow (← mkAppM ``Membership.mem #[factorsE, q])
      (mkApp (mkConst ``Hex.ZPoly.Irreducible) q))

/-- The `factor_poly!` fallback machinery shared by both input types:
factorize, self-check, reify, and kernel-precheck the per-factor replay.
Returns the scalar and factor-list expressions. -/
meta def bangFactorCommon (tactic : String) (f : Hex.ZPoly) :
    MetaM (Expr × Expr) := do
  checkBangBudget tactic f
  let (scalar, factors) ← factorSearch tactic f
  unless factors.all Hex.ZPoly.isIrreducible do
    throwError "{tactic}: internal error: a factorization entry fails \
        isIrreducible; please report this"
  let factorsE := Hex.FactorTactic.listLit zpolyTy
    (← factors.mapM fun q => Hex.CertReify.reifyZPoly q)
  kernelDecideTrue tactic (← forallIrredProp factorsE)
  return (toExpr scalar, factorsE)

/-- The `factor_poly!` fallback for `Hex.ZPoly` inputs. -/
meta def bangZPolyFactor (fE : Expr) : MetaM Expr := do
  let f ← evalZPoly "factor_poly!" fE
  discard <| checkTransparent "factor_poly!" f fE
  let (scalarE, factorsE) ← bangFactorCommon "factor_poly!" f
  let intE := mkConst ``Int
  let zeroE ← synthInstance (← mkAppM ``Zero #[intE])
  let decE ← synthInstance (← mkAppM ``DecidableEq #[intE])
  let lhsE ← mkAppM ``HMul.hMul
    #[← mkAppM ``Hex.DensePoly.C #[scalarE], ← mkAppM ``List.prod #[factorsE]]
  let hmulE := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
    intE zeroE decE lhsE fE Hex.CertReify.reflTrue
  let hirredE := mkApp2 (mkConst ``Hex.ZPoly.forall_irreducible_of_decide)
    factorsE Hex.CertReify.reflTrue
  return mkApp5 (mkConst ``Hex.ZPoly.Factored.mk)
    fE scalarE factorsE hmulE hirredE

/-- The `factor_poly!` fallback for `Polynomial ℤ` inputs. -/
meta def bangIntFactor (e : Expr) : MetaM Expr := do
  let (f, fLit, hP) ← parseInput "factor_poly!" e
  let (scalarE, factorsE) ← bangFactorCommon "factor_poly!" f
  return mkAppN (mkConst ``Hex.FactoredPoly.ofZDecide)
    #[e, fLit, scalarE, factorsE, Hex.CertReify.reflTrue,
      Hex.CertReify.reflTrue, hP]

/-- Elaborate a bang-fallback argument and dispatch on its type. -/
meta def elabBangArg (tactic : String) (t : Syntax)
    (onZPoly : Expr → MetaM Expr) (onInt : Expr → MetaM Expr) :
    Term.TermElabM Expr := do
  let pE ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let pE ← instantiateMVars pE
  Hex.FactorTactic.checkClosed tactic pE
  let ty ← inferType pE
  match ← Hex.FactorTactic.classify ty with
  | .zpoly _ _ _ => onZPoly pE
  | .fp _ _ _ _ _ _ =>
      throwError "{tactic}: the kernel decide fallback covers Hex.ZPoly and \
          Polynomial ℤ inputs; FpPoly inputs are fully served by the plain \
          form"
  | .other =>
      if ← intPolyInput? ty then onInt pE
      else
        throwError "{tactic}: unsupported polynomial type{indentExpr ty}\
            \nThe kernel decide fallback covers Hex.ZPoly and Polynomial ℤ"

/-- `irreducibility! f` behaves as `irreducibility f`, then falls back to the
kernel factorizer replay when the certificate pipeline declines (see the
module docstring for the `import all` closure and cost caveats). -/
syntax (name := irreducibilityBangTerm) "irreducibility!" term:max : term

@[term_elab irreducibilityBangTerm] meta def elabIrreducibilityBang :
    Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(irreducibility! $t) => do
      let e ←
        try
          Hex.FactorTactic.elabIrreducibilityCore stx t expectedType?
        catch _ =>
          elabBangArg "irreducibility!" t
            (bangZPolyIrred "irreducibility!") (bangIntIrred "irreducibility!")
      Term.ensureHasType expectedType? e
  | _ => Elab.throwUnsupportedSyntax

/-- The bang goal-mode fallback: close `Hex.ZPoly.Irreducible e`,
`Irreducible (toPolynomial f)`, or `Irreducible P` for parseable
`P : Polynomial ℤ` by the kernel factorizer replay. -/
meta def bangGoalProof (tgt : Expr) : MetaM Expr := do
  if tgt.getAppFn.isConstOf ``Hex.ZPoly.Irreducible &&
      tgt.getAppNumArgs == 1 then
    let fE := tgt.appArg!
    Hex.FactorTactic.checkClosed "irreducibility!" fE
    bangZPolyIrred "irreducibility!" fE
  else
    let tgtW ← whnfR tgt
    let_expr Irreducible M _inst arg := tgtW
      | throwError "irreducibility!: the goal{indentExpr tgt}\
          \nis not of the form `Hex.ZPoly.Irreducible f` or `Irreducible P` \
          for `P : Polynomial ℤ`"
    unless ← intPolyInput? M do
      throwError "irreducibility!: the kernel decide fallback covers \
          Hex.ZPoly and Polynomial ℤ goals, but the goal is{indentExpr tgt}"
    Hex.FactorTactic.checkClosed "irreducibility!" arg
    match ← matchToPolynomial? arg with
    | some fE =>
        let f ← evalZPoly "irreducibility!" fE
        discard <| checkTransparent "irreducibility!" f fE
        bangChecks "irreducibility!" fE f
        let fLit ← Hex.CertReify.reifyZPoly f
        let intE := mkConst ``Int
        let zeroE ← synthInstance (← mkAppM ``Zero #[intE])
        let decE ← synthInstance (← mkAppM ``DecidableEq #[intE])
        let hroot := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
          intE zeroE decE fLit fE Hex.CertReify.reflTrue
        let hP ← mkCongrArg tomlFn hroot
        kernelDecideTrue "irreducibility!" (mkApp (mkConst ``Hex.ZPoly.Irreducible) fLit)
        return mkApp4 (mkConst ``HexBerlekampZassenhausMathlib.irreducible_ofZ_decide)
          (mkApp tomlFn fE) fLit Hex.CertReify.reflTrue hP
    | none => bangIntIrred "irreducibility!" arg

/-- Tactic forms of `irreducibility!`, mirroring `irreducibility`: bare form
closes an irreducibility goal, `irreducibility! f` adds `this`, and
`irreducibility! h : f` names it `h`, each falling back to the kernel
factorizer replay when the certificate pipeline declines. -/
syntax (name := irreducibilityBangTac)
  "irreducibility!" (atomic(ident " : "))? (term:max)? : tactic

@[tactic irreducibilityBangTac] meta def evalIrreducibilityBangTac :
    Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| irreducibility!) => do
      try
        Tactic.evalTactic (← `(tactic| irreducibility))
      catch _ =>
        let goal ← Tactic.getMainGoal
        goal.withContext do
          let tgt ← instantiateMVars (← goal.getType)
          let proof ← bangGoalProof tgt
          unless ← isDefEq (← inferType proof) tgt do
            throwError "irreducibility!: the certified statement\
                {indentExpr (← inferType proof)}\
                \nis not definitionally equal to the goal{indentExpr tgt}"
          goal.assign proof
        Tactic.replaceMainGoal []
  | `(tactic| irreducibility! $t:term) => do
      let proof ← Tactic.withMainContext do
        try
          Hex.FactorTactic.elabIrreducibilityCore stx t none
        catch _ =>
          elabBangArg "irreducibility!" t
            (bangZPolyIrred "irreducibility!") (bangIntIrred "irreducibility!")
      Tactic.liftMetaTactic fun g => do
        let ty ← inferType proof
        let (_, g) ← (← g.assert `this ty proof).intro1P
        return [g]
  | `(tactic| irreducibility! $h:ident : $t:term) => do
      let proof ← Tactic.withMainContext do
        try
          Hex.FactorTactic.elabIrreducibilityCore stx t none
        catch _ =>
          elabBangArg "irreducibility!" t
            (bangZPolyIrred "irreducibility!") (bangIntIrred "irreducibility!")
      Tactic.liftMetaTactic fun g => do
        let ty ← inferType proof
        let (_, g) ← (← g.assert h.getId ty proof).intro1P
        return [g]
  | _ => Elab.throwUnsupportedSyntax

/-- Shared plain-then-bang elaboration for `factor_poly!`. -/
meta def elabFactorBangCore (stx : Syntax) (t : Syntax)
    (expectedType? : Option Expr) : Term.TermElabM Expr := do
  try
    Hex.FactorTactic.elabFactorPolyCore stx t expectedType?
  catch _ =>
    elabBangArg "factor_poly!" t bangZPolyFactor bangIntFactor

/-- `factor_poly! f` behaves as `factor_poly f`, then falls back to per-factor
kernel factorizer replays when the certificate pipeline declines (see the
module docstring for the `import all` closure and cost caveats). -/
syntax (name := factorPolyBangTerm) "factor_poly!" term:max : term

@[term_elab factorPolyBangTerm] meta def elabFactorPolyBang : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(factor_poly! $t) => do
        let e ← elabFactorBangCore stx t expectedType?
        Term.ensureHasType expectedType? e
    | _ => Elab.throwUnsupportedSyntax

/-- The tactic form of `factor_poly!`: as the `factor_poly` tactic
(`scalar`/`factors` bindings plus `factors_mul`/`factors_irred`), with the
kernel-replay fallback. -/
syntax (name := factorPolyBangTac) "factor_poly!" term:max : tactic

@[tactic factorPolyBangTac] meta def evalFactorPolyBangTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| factor_poly! $t) => do
        let e ← Tactic.withMainContext do
          elabFactorBangCore stx t none
        Hex.FactorTactic.introFactored e
    | _ => Elab.throwUnsupportedSyntax

end HexBerlekampZassenhausMathlib.FactorTactic
