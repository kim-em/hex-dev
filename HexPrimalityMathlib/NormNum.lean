/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.Prime
import HexPrimality.Elab
import Mathlib.Tactic.NormNum.Prime

/-!
The `Nat.Prime` reach of the `primality` tactic and an explicitly opted-in
certificate-backed `norm_num` policy.

By default this module does not alter which extension handles
`Nat.Prime`: pinned Mathlib's trial-division extension was registered first
and remains first. A module opts into Hex's policy with the command
`use_hex_primality_norm_num`. The command locally erases Mathlib's original
registration, exposing the two extensions registered here: trial division
below `natPrimeCertThreshold`, then certificate search at and above it.
The erasure does not survive an import, so every importing module makes its
own choice.

The threshold is `2^24`. Fresh one-goal modules under the pinned toolchain
showed trial division ahead at six digits, mixed input-dependent results
through seven digits, and the certificate route ahead at the 25-bit edge;
Mathlib's generated trial proof exceeds the default kernel recursion depth
on the 31-bit Mersenne prime. The power-of-two policy keeps all inputs with
at most 24 bits on trial division and sends every larger input to the
bounded certificate route.

Above the threshold, a positive verdict emits a reified Pocklington
certificate through `natPrime_of_checkPrimeAt`; the kernel replays only the
checker. A negative verdict emits a dynamically validated proper factor
through Mathlib's `deriveNotPrime`. If bounded certificate or factor search
is exhausted, both Hex extensions decline, rather than falling through to
unbounded trial division.

The tactic handler registers on the same `primality` syntax kind as the
Mathlib-free elaborator; registration order makes this handler run first,
and it defers every non-`Nat.Prime` goal shape back.
-/

namespace Hex.PrimalityTactic

open Lean Meta Elab Qq Mathlib.Meta.NormNum

/-- The measured opt-in `norm_num` crossover. Numerals below `2^24` use
trial division; 25-bit and larger numerals use bounded certificate search. -/
def natPrimeCertThreshold : Nat := 16777216

theorem isNat_prime_of_hex : {n n' : ℕ} → IsNat n n' →
    _root_.Nat.Prime n' → _root_.Nat.Prime n
  | _, _, ⟨rfl⟩, hp => by simpa using hp

/-- The opt-in `norm_num` extension for certificate-backed `Nat.Prime`
verdicts at and above `natPrimeCertThreshold`. -/
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
                unless 1 < d && d < n' && n' % d == 0 do failure
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
          let some n ← getNatValue? nE
            | throwError "primality: the goal{indentExpr tgt}\
                \nis not about a natural-number numeral"
          let proof ← provePrimeWith ``Hex.Nat.natPrime_of_checkPrimeAt
            "primality" n nE
          goal.assign proof
          Tactic.replaceMainGoal []
    | _ => Elab.throwUnsupportedSyntax

end Hex.PrimalityTactic

open Lean Meta Qq Mathlib.Meta.NormNum

/-- A threshold-guarded alias of Mathlib's trial-division extension. It keeps
small numerals working under `use_hex_primality_norm_num` but declines at the
certificate tier, so exhaustion there cannot start a large trial search. -/
@[norm_num _root_.Nat.Prime _] def Hex.PrimalityTactic.evalNatPrimeTrial :
    Mathlib.Meta.NormNum.NormNumExt where
  eval {_ _} e := do
    let .app (.const `Nat.Prime _) (n : Q(ℕ)) ← whnfR e | failure
    let some n' ← getNatValue? n | failure
    if n' < natPrimeCertThreshold then
      Mathlib.Meta.NormNum.evalNatPrime.eval e
    else
      failure

/-- Opt the current module into Hex's thresholded `Nat.Prime` `norm_num`
policy. The choice must be repeated by importers. -/
syntax (name := useHexPrimalityNormNum) "use_hex_primality_norm_num" : command

macro_rules
  | `(use_hex_primality_norm_num) =>
      `(attribute [-norm_num] Mathlib.Meta.NormNum.evalNatPrime)
