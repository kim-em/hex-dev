/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.Prime
import HexPrimality.Elab
import Mathlib.Tactic.NormNum.Prime

/-!
The `Nat.Prime` reach of the `primality` tactic, and the `norm_num`
extension for numerals beyond trial division.

The `norm_num` extension fails on numerals below
`natPrimeCertThreshold`, deferring them to Mathlib's trial-division
extension; above it, a positive verdict emits the reified Pocklington
certificate through `natPrime_of_checkPrimeAt` (the kernel replays only
the checker) and a negative verdict emits a dynamically validated proper
factor through Mathlib's `deriveNotPrime`. A hard semiprime whose factor
the bounded rho search misses makes the extension fail silently rather
than fall into an unbounded computation. The threshold is a placeholder
until the bench measures the crossover.

**Dispatch caveat.** `norm_num` consults extensions in registration
order, and Mathlib's trial-division extension registers at import time,
ahead of this one; on a large numeral it succeeds at elaboration with a
minFac chain whose proof the kernel cannot check past roughly 25 bits,
so this extension is never consulted. Extension erasure does not persist
across imports, so the division cannot be fixed here once and for all: a
file that wants certificate-backed `norm_num` on large numerals opts in
with `attribute [-norm_num] Mathlib.Meta.NormNum.evalNatPrime`, and the
re-registered `evalNatPrimeTrial` alias keeps small numerals working
there (see `NormNumTests.lean` for the pattern in action). The
`primality` tactic has no such caveat and is the primary vehicle for
large numerals.

The tactic handler registers on the same `primality` syntax kind as the
Mathlib-free elaborator; registration order makes this handler run first,
and it defers every non-`Nat.Prime` goal shape back.
-/

namespace Hex.PrimalityTactic

open Lean Meta Elab Qq Mathlib.Meta.NormNum

/-- Numerals below this stay with Mathlib's trial-division `norm_num`
extension; a placeholder until the bench measures the crossover. -/
def natPrimeCertThreshold : Nat := 1000000

theorem isNat_prime_of_hex : {n n' : ℕ} → IsNat n n' →
    _root_.Nat.Prime n' → _root_.Nat.Prime n
  | _, _, ⟨rfl⟩, hp => by simpa using hp

/-- The `norm_num` extension: certificate-backed `Nat.Prime` verdicts for
numerals beyond trial division. -/
@[norm_num _root_.Nat.Prime _] def evalNatPrimeCert : NormNumExt where
  eval {_ _} e := do
    let .app (.const `Nat.Prime _) (n : Q(ℕ)) ← whnfR e | failure
    let ⟨nn, pn⟩ ← deriveNat n _
    let n' := nn.natLit!
    if n' < natPrimeCertThreshold then failure
    match Hex.Nat.primeCert? n' (Hex.Rand.ofSeed n')
        (Hex.Nat.defaultPrimeFuel n') with
    | .ok (c, _) =>
        -- Untrusted-search self-check before emitting anything.
        unless c.raw.subject == n' && Hex.Nat.checkPrime c.raw do failure
        let prf : Q(_root_.Nat.Prime $nn) :=
          mkApp3 (mkConst ``Hex.Nat.natPrime_of_checkPrimeAt) nn
            (reifyPrimeCert c.raw) reflTrue
        return .isTrue q(isNat_prime_of_hex $pn $prf)
    | .error f =>
        match f.stop with
        | .exhausted => failure
        | .composite =>
            match Hex.Nat.rhoFactor? n' (Hex.Rand.ofSeed n') 16 with
            | .ok (d, _) =>
                let prf : Q(¬ _root_.Nat.Prime $nn) := deriveNotPrime n' d nn
                return .isFalse q(isNat_not_prime $pn $prf)
            | .error _ => failure

/-- The `Nat.Prime` goal handler for bare `primality`: same search, same
reified certificate, emitted through the `Nat.Prime`-flavoured wrapper. -/
@[tactic primalityTac] def evalPrimalityTacNat : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| primality) => do
        let goal ← Tactic.getMainGoal
        goal.withContext do
          let tgt ← instantiateMVars (← goal.getType)
          unless tgt.getAppFn.isConstOf `Nat.Prime &&
              tgt.getAppNumArgs == 1 do
            Elab.throwUnsupportedSyntax
          let nE := tgt.appArg!
          checkClosed "primality" nE
          let some n ← getNatValue? nE | Elab.throwUnsupportedSyntax
          let proof ← provePrimeWith ``Hex.Nat.natPrime_of_checkPrimeAt
            "primality" n nE
          goal.assign proof
          Tactic.replaceMainGoal []
    | _ => Elab.throwUnsupportedSyntax

end Hex.PrimalityTactic

/-- Mathlib's trial-division extension, re-registered behind the
certificate extension so that a file opting in with
`attribute [-norm_num] Mathlib.Meta.NormNum.evalNatPrime` keeps its small
numerals working (an attribute cannot be re-applied to an imported
declaration, so this is an alias with its own name). -/
@[norm_num _root_.Nat.Prime _] def Hex.PrimalityTactic.evalNatPrimeTrial :
    Mathlib.Meta.NormNum.NormNumExt :=
  { Mathlib.Meta.NormNum.evalNatPrime with
    name := `Hex.PrimalityTactic.evalNatPrimeTrial }

/-! Elaboration tests for the tactic on both predicates; the `norm_num`
tests live in `NormNumTests.lean`, downstream of the registrations. -/

example : Nat.Prime 2147483647 := by primality
example : Hex.Nat.Prime 2147483647 := by primality
example : Nat.Prime 65537 := by primality
