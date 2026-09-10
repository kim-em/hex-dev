/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPrimality.Search
public import HexPrimality.Search
public import Lean

public section

/-!
The `primality` term elaborator and tactic.

`primality n` elaborates to a proof of `Hex.Nat.Prime n` for a literal `n`:
the compiled certificate search runs at elaboration time as untrusted code,
and the emitted term applies `prime_of_checkPrimeAt` to the reified
certificate with an `Eq.refl true` slot, so the kernel replays only
`checkPrime` — `O(K log n)` modular and bounded ordinary multiplications,
plus `O(K)` factor-subject comparisons, on the certificate data, never the
search.

Tactic forms: bare `primality` closes a `Hex.Nat.Prime e` goal for a
numeral `e`; `primality n` adds `this : Hex.Nat.Prime n`;
`primality h : n` names it `h`.

For reproducible syntax with no seed argument, the elaborator uses
`Rand.ofSeed n` and `primalityFuel n`, the measured policy cap over
`defaultPrimeFuel n`; the lower `primeCert?` API remains explicitly seeded,
and diagnostics report the seed and fuel if certificate search exhausts its
budget. The companion library may register an
additional `@[tactic primalityTac]` handler for `Nat.Prime` goal shapes;
handlers registered later run first and defer here by throwing
`unsupportedSyntax`.
-/

namespace Hex.PrimalityTactic

open Lean Meta Elab

/-- ABI version of the downstream factor-search registration boundary. -/
meta def searchExtensionVersion : Nat := 1

/-- One downstream partial-factor producer available to elaboration-time
certificate search. The version is checked before the function is used. -/
meta structure SearchExtension where
  /-- Version of the extension ABI implemented by this registration. -/
  version : Nat
  /-- Fully qualified name of the registered partial-factor producer. -/
  factorName : Name

/-- Well-known search-extension constants, checked in deterministic order.
Adding or reordering an entry requires a HexPrimality release. -/
meta def searchExtensionNames : List Name :=
  [`HexIntFactor.PrimalityTactic.extension]

private meta unsafe def evalSearchExtensionUnsafe (n : Name) :
    MetaM SearchExtension :=
  evalConst SearchExtension n

@[implemented_by evalSearchExtensionUnsafe]
private meta opaque evalSearchExtensionCore (n : Name) : MetaM SearchExtension

private meta unsafe def evalFactorSearchUnsafe (n : Name) :
    MetaM Hex.Nat.FactorSearch :=
  evalConst Hex.Nat.FactorSearch n

@[implemented_by evalFactorSearchUnsafe]
private meta opaque evalFactorSearchCore (n : Name) :
    MetaM Hex.Nat.FactorSearch

/-- Registered factor-search extensions present in the environment. Each
declaration's type and ABI version are checked before deterministic dispatch. -/
meta def searchExtensions : MetaM (List SearchExtension) := do
  let env ← getEnv
  let mut found := []
  for n in searchExtensionNames do
    if let some info := env.find? n then
      unless info.type.isConstOf ``SearchExtension do
        throwError "primality: search extension {n} has unexpected type\
            {indentExpr info.type}"
      let ext ← evalSearchExtensionCore n
      unless ext.version = searchExtensionVersion do
        throwError "primality: search extension {n} uses ABI version \
            {ext.version}; expected {searchExtensionVersion}"
      let some factorInfo := env.find? ext.factorName
        | throwError "primality: search extension {n} names missing factor \
            declaration {ext.factorName}"
      unless ← isDefEq factorInfo.type (mkConst ``Hex.Nat.FactorSearch) do
        throwError "primality: factor declaration {ext.factorName} from \
            extension {n} has unexpected type{indentExpr factorInfo.type}"
      found := found ++ [ext]
  return found

/-- `Eq.refl true` as a raw proof slot: the kernel verifies the reified
Bool equation by reduction alone. -/
meta def reflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [.one]) (mkConst ``Bool) (mkConst ``Bool.true)

private meta def certTy : Expr := mkConst ``Hex.Nat.PrimeCert

private meta def natTy : Expr := mkConst ``Nat

private meta def pairTy : Expr :=
  mkApp2 (mkConst ``Prod [.zero, .zero]) natTy certTy

private meta def tripleTy : Expr :=
  mkApp2 (mkConst ``Prod [.zero, .zero]) natTy pairTy

mutual

/-- Reify a certificate as constructor applications over `Nat` literals.
Pure data with no proof slots, so the reifier is total and the kernel
obligations all live in the one `Eq.refl true` slot of the wrapper. -/
meta def reifyPrimeCert : Hex.Nat.PrimeCert → Expr
  | .small n => mkApp (mkConst ``Hex.Nat.PrimeCert.small) (mkNatLit n)
  | .pock n factors =>
      mkApp2 (mkConst ``Hex.Nat.PrimeCert.pock) (mkNatLit n)
        (reifyFactors factors)
  | .pock3 n r s w factors =>
      mkApp5 (mkConst ``Hex.Nat.PrimeCert.pock3) (mkNatLit n) (mkNatLit r)
        (mkNatLit s) (mkNatLit w) (reifyFactors factors)

/-- Reify a factor list. -/
meta def reifyFactors : List (Nat × Nat × Hex.Nat.PrimeCert) → Expr
  | [] => mkApp (mkConst ``List.nil [.zero]) tripleTy
  | (a, e, c) :: rest =>
      mkApp3 (mkConst ``List.cons [.zero]) tripleTy
        (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) natTy pairTy
          (mkNatLit a)
          (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) natTy certTy
            (mkNatLit e) (reifyPrimeCert c)))
        (reifyFactors rest)

end

/-- Reject open terms: the search and the kernel replay both need a closed
numeral. -/
meta def checkClosed (tactic : String) (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasExprMVar then
    throwError "{tactic}: the argument{indentExpr e}\
        \nmust not contain free or meta variables"

/-- Supported bit-length ceiling for every elaboration-time certificate route.
The 512-bit boundary is the largest measured fresh-module rung; changing it
requires new end-to-end search, reification, and kernel-replay evidence. -/
meta def primalityBitBudget : Nat := 512

/-- Maximum recursive fuel passed to elaboration-time certificate search.
The settled default is one unit per input bit, so this is deliberately the same
quantity as the supported input ceiling. Keeping the definitions linked prevents
one policy boundary from changing without the other. -/
meta def primalityFuelBudget : Nat := primalityBitBudget

/-- Maximum Brent restarts at one partial-factor worklist entry on every
elaboration-time certificate route. -/
meta def primalityRhoRestartBudget : Nat := 2

/-- Maximum Brent cycle steps per restart on every elaboration-time
certificate route. -/
meta def primalityRhoStepBudget : Nat := 1 <<< 15

/-- The explicit rho allocation shared by every elaboration-time route. -/
meta def primalitySearchBudget : Hex.Nat.PrimeCertBudget :=
  ⟨primalityRhoRestartBudget, primalityRhoStepBudget⟩

/-- The fuel selected by every elaboration-time certificate route. -/
meta def primalityFuel (n : Nat) : Nat :=
  min (Hex.Nat.defaultPrimeFuel n) primalityFuelBudget

/-- Whether an input is admitted by the common elaboration policy. -/
meta def withinPrimalityBudget (n : Nat) : Bool :=
  decide (n.log2 + 1 ≤ primalityBitBudget)

/-- Enforce the common input-size policy before any certificate search. -/
meta def checkPrimalityPolicy (tactic : String) (n : Nat) : MetaM Unit := do
  let bits := n.log2 + 1
  unless withinPrimalityBudget n do
    throwError "{tactic}: input has {bits} bits; the enforced policy supports \
        at most {primalityBitBudget} bits; raising the ceiling requires new \
        end-to-end benchmark evidence"

/-- Report bounded-search exhaustion without inviting an unbounded fallback. -/
meta def throwPrimalityExhausted {α : Type} (tactic : String) (n attempts fuel : Nat) :
    MetaM α :=
  throwError "{tactic}: certificate search for {n} exhausted after {attempts} \
      attempts (seed {n}, recursive fuel {fuel}, root factor fuel \
      {2 * n.log2 + 8}; policy maximum \
      {primalityFuelBudget} fuel at {primalityBitBudget} bits, \
      {primalityRhoRestartBudget} rho restarts with \
      {primalityRhoStepBudget} steps each); no total primality decision was \
      attempted"

/-- Run the certificate search and emit the checked proof term with `head`
applied to the subject, the reified certificate, and the `Eq.refl true`
slot: `prime_of_checkPrimeAt` here, the companion's `Nat.Prime`-flavoured
wrapper there. The search result is self-checked with the same compiled
`checkPrime` the kernel will replay before anything is emitted. -/
meta def provePrimeWith (head : Name) (tactic : String) (n : Nat)
    (nE : Expr) : MetaM Expr := do
  unless ← isDefEq (mkNatLit n) nE do
    throwError "{tactic}: the argument{indentExpr nE}\
        \nevaluates to {n} but is not definitionally transparent to the \
        elaborator (an imported definition without `@[expose]`?); the kernel \
        could not check the emitted certificate against it"
  checkPrimalityPolicy tactic n
  let fuel := primalityFuel n
  let emit (success : Hex.Nat.Internal.PrimeCertSuccess n) : MetaM Expr := do
    let c := success.cert
    -- Untrusted-search self-check before emitting anything.
    unless c.raw.subject == n && Hex.Nat.checkPrime c.raw do
      throwError "{tactic}: internal error: the found certificate fails \
          its own check; please report this"
    return mkApp3 (mkConst head) nE (reifyPrimeCert c.raw) reflTrue
  let composite : MetaM Expr := do
    match Hex.Nat.defaultBases.find?
        (fun a => !(Hex.Nat.millerRabin n a)) with
    | some a =>
        throwError "{tactic}: {n} is not prime \
            (Miller-Rabin witness {a})"
    | none =>
        throwError "{tactic}: {n} is not prime"
  match Hex.Nat.Internal.primeCertCountedWith? primalitySearchBudget n
      (Hex.Rand.ofSeed n) fuel with
  | .error f =>
      match f.stop with
      | .composite => composite
      | .exhausted =>
          let mut attempts := f.attempts
          let mut r := f.rand
          for ext in (← searchExtensions) do
            let factor ← evalFactorSearchCore ext.factorName
            match Hex.Nat.Internal.primeCertCountedUsing? factor
                primalitySearchBudget n r fuel with
            | .ok success => return ← emit success
            | .error f =>
                attempts := attempts + f.attempts
                r := f.rand
                -- A producer cannot issue this verdict directly; retain this
                -- branch defensively for composites found while recursively
                -- certifying the factors it supplied.
                if f.stop = .composite then
                  return ← composite
          throwPrimalityExhausted tactic n attempts fuel
  | .ok success => emit success

/-- `provePrimeWith` at the Mathlib-free wrapper: the proof term for
`Hex.Nat.Prime n`. -/
meta def provePrime (tactic : String) (n : Nat) (nE : Expr) : MetaM Expr :=
  provePrimeWith ``Hex.Nat.prime_of_checkPrimeAt tactic n nE

/-- Elaborate a `primality` argument to its numeral and proof. -/
meta def elabPrimalityArgument (t : Syntax) : Term.TermElabM Expr := do
  let nE ← Term.elabTerm t (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  let nE ← instantiateMVars nE
  checkClosed "primality" nE
  let some n ← getNatValue? nE
    | throwError "primality: the argument{indentExpr nE}\
        \nis not a natural-number numeral"
  provePrime "primality" n nE

/-- `primality n` elaborates to a proof of `Hex.Nat.Prime n` for a literal
`n`. -/
syntax (name := primalityTerm) "primality" term:max : term

/-- Elaborator for the Mathlib-free `primality n` term syntax. -/
@[term_elab primalityTerm] meta def elabPrimality : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(primality $t) => do
        let e ← elabPrimalityArgument t
        Term.ensureHasType expectedType? e
    | _ => Elab.throwUnsupportedSyntax

/-- Try to close a goal of the form `Hex.Nat.Prime e`; return `false` when
the goal has a different shape. -/
meta def goalPrime (goal : MVarId) : Tactic.TacticM Bool := do
  goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    unless tgt.getAppFn.isConstOf ``Hex.Nat.Prime && tgt.getAppNumArgs == 1 do
      return false
    let nE := tgt.appArg!
    checkClosed "primality" nE
    let some n ← getNatValue? nE
      | throwError "primality: the goal{indentExpr tgt}\
          \nis not about a natural-number numeral"
    let proof ← provePrime "primality" n nE
    goal.assign proof
    Tactic.replaceMainGoal []
    return true

/-- Tactic forms of `primality`: bare `primality` closes a
`Hex.Nat.Prime e` goal; `primality n` adds the proof as `this`;
`primality h : n` names it `h`. -/
syntax (name := primalityTac)
  "primality" (atomic(ident " : "))? (term:max)? : tactic

/-- Evaluator for the Mathlib-free `primality` tactic forms. -/
@[tactic primalityTac] meta def evalPrimalityTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| primality) => do
        let goal ← Tactic.getMainGoal
        if ← goalPrime goal then
          return
        -- Defer `Nat.Prime` goal shapes to the companion's handler on the
        -- same syntax kind rather than erroring here.
        let tgt ← instantiateMVars (← goal.getType)
        if tgt.getAppFn.isConstOf `Nat.Prime then
          Elab.throwUnsupportedSyntax
        throwError "primality: expected a goal of the form \
            `Hex.Nat.Prime n` for a numeral `n` (the companion library \
            extends this to `Nat.Prime`)"
    | `(tactic| primality $t:term) => do
        let proof ← Tactic.withMainContext do
          elabPrimalityArgument t
        Tactic.liftMetaTactic fun g => do
          let ty ← inferType proof
          let (_, g) ← (← g.assert `this ty proof).intro1P
          return [g]
    | `(tactic| primality $_h:ident :) =>
        throwError "primality: expected a natural-number term after the colon"
    | `(tactic| primality $h:ident : $t:term) => do
        let proof ← Tactic.withMainContext do
          elabPrimalityArgument t
        Tactic.liftMetaTactic fun g => do
          let ty ← inferType proof
          let (_, g) ← (← g.assert h.getId ty proof).intro1P
          return [g]
    | _ => Elab.throwUnsupportedSyntax

end Hex.PrimalityTactic
