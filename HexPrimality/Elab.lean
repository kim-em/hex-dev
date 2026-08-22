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
`checkPrime` — `O(K log n)` modular multiplications on the certificate data,
never the search.

Tactic forms: bare `primality` closes a `Hex.Nat.Prime e` goal for a
numeral `e`; `primality n` adds `this : Hex.Nat.Prime n`;
`primality h : n` names it `h`.

For reproducible syntax with no seed argument, the elaborator uses
`Rand.ofSeed n` and `defaultPrimeFuel n`; the lower `primeCert?` API remains
explicitly seeded, and diagnostics report the seed and fuel if certificate
search exhausts its budget. The companion library may register an
additional `@[tactic primalityTac]` handler for `Nat.Prime` goal shapes;
handlers registered later run first and defer here by throwing
`unsupportedSyntax`.
-/

namespace Hex.PrimalityTactic

open Lean Meta Elab

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

/-- Bit-length ceiling on tactic inputs: the kernel replay is `O(K log n)`
modular multiplications, and beyond this size certificate search itself is
the bottleneck to fix first. -/
meta def primalityBitBudget : Nat := 8192

/-- Run the certificate search and emit the checked proof term for
`Hex.Nat.Prime n`. The search result is self-checked with the same compiled
`checkPrime` the kernel will replay before anything is emitted. -/
meta def provePrime (tactic : String) (n : Nat) (nE : Expr) : MetaM Expr := do
  unless ← isDefEq (mkNatLit n) nE do
    throwError "{tactic}: the argument{indentExpr nE}\
        \nevaluates to {n} but is not definitionally transparent to the \
        elaborator (an imported definition without `@[expose]`?); the kernel \
        could not check the emitted certificate against it"
  if n.log2 > primalityBitBudget then
    throwError "{tactic}: {n} has more than {primalityBitBudget} bits; \
        raising `primalityBitBudget` is a separate, benchmarked change"
  match Hex.Nat.primeCert? n (Hex.Rand.ofSeed n) (Hex.Nat.defaultPrimeFuel n) with
  | .error f =>
      match f.stop with
      | .composite =>
          match Hex.Nat.defaultBases.find?
              (fun a => !(Hex.Nat.millerRabin n a)) with
          | some a =>
              throwError "{tactic}: {n} is not prime \
                  (Miller-Rabin witness {a})"
          | none =>
              throwError "{tactic}: {n} is not prime"
      | .exhausted =>
          throwError "{tactic}: certificate search for {n} exhausted its \
              budget after {f.attempts} attempts (seed {n}, fuel \
              {Hex.Nat.defaultPrimeFuel n}); the factorization of n - 1 may \
              be out of reach"
  | .ok (c, _) =>
      -- Untrusted-search self-check before emitting anything.
      unless c.raw.subject == n && Hex.Nat.checkPrime c.raw do
        throwError "{tactic}: internal error: the found certificate fails \
            its own check; please report this"
      return mkApp3 (mkConst ``Hex.Nat.prime_of_checkPrimeAt) nE
        (reifyPrimeCert c.raw) reflTrue

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

@[tactic primalityTac] meta def evalPrimalityTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| primality) => do
        let goal ← Tactic.getMainGoal
        if ← goalPrime goal then
          return
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
    | `(tactic| primality $h:ident : $t:term) => do
        let proof ← Tactic.withMainContext do
          elabPrimalityArgument t
        Tactic.liftMetaTactic fun g => do
          let ty ← inferType proof
          let (_, g) ← (← g.assert h.getId ty proof).intro1P
          return [g]
    | _ => Elab.throwUnsupportedSyntax

end Hex.PrimalityTactic

/-! Elaboration tests: every syntax form across the table, trial, and
certificate tiers, and the two failure messages. -/

example : Hex.Nat.Prime 97 := primality 97
example : Hex.Nat.Prime 9973 := primality 9973
example : Hex.Nat.Prime 10007 := primality 10007
example : Hex.Nat.Prime 2147483647 := primality 2147483647
example : Hex.Nat.Prime 101 := by primality
example : Hex.Nat.Prime 2147483647 := by primality
example : True := by
  primality 65537
  primality fermat : 257
  exact trivial

/-- error: primality: 561 is not prime (Miller-Rabin witness 2) -/
#guard_msgs in
example : Hex.Nat.Prime 561 := primality 561

/--
error: primality: the goal
  Hex.Nat.Prime (2 + 2)
is not about a natural-number numeral
-/
#guard_msgs in
example : Hex.Nat.Prime (2 + 2) := by primality
