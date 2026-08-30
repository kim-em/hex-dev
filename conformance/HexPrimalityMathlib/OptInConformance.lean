/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-!
Fresh-module checks for the explicit Hex `Nat.Prime` `norm_num` policy.
The canonical `Conformance` module imports this one and checks that the
opt-in attribute erasure does not cross that import boundary.
-/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : natPrimeCertThreshold = 16777216 := rfl
example : natPrimeRhoRestartBudget = 1 := rfl
example : natPrimeRhoStepBudget = 65536 := rfl

-- The documented seed deterministically finds the same proper factor on the
-- first certificate-tier composite. Parity consumes no restart, while the
-- balanced ceiling semiprime consumes exactly the work budget and exhausts.
#guard (match Hex.Nat.Internal.primeCertCountedWith? primalitySearchBudget
    16777217 (Hex.Rand.ofSeed 16777217) (primalityFuel 16777217) with
  | .error failure =>
      failure.stop == .composite && failure.attempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 16777217
  | .ok _ => false)
#guard (match Hex.Nat.Internal.rhoFactorCountedWith? 16777217
    (Hex.Rand.ofSeed 16777217) natPrimeRhoRestartBudget
    natPrimeRhoStepBudget with
  | .ok success =>
      success.factor == 97 && success.attempts == natPrimeRhoRestartBudget
  | .error _ => false)
#guard (match Hex.Nat.Internal.rhoFactorCountedWith? 18446744073709551616
    (Hex.Rand.ofSeed 18446744073709551616) natPrimeRhoRestartBudget
    natPrimeRhoStepBudget with
  | .ok success => success.factor == 2 && success.attempts == 0
  | .error _ => false)
#guard (match Hex.Nat.Internal.rhoFactorCountedWith?
    13407807926820848549984871491119855788235523322740973763876191939595871090961335127125233828880698995298214970593191507050244061726229325180256249012290513
    (Hex.Rand.ofSeed
      13407807926820848549984871491119855788235523322740973763876191939595871090961335127125233828880698995298214970593191507050244061726229325180256249012290513)
    natPrimeRhoRestartBudget natPrimeRhoStepBudget with
  | .error failure =>
      failure.stop == .exhausted &&
        failure.attempts == natPrimeRhoRestartBudget
  | .ok _ => false)
#guard (match Hex.Nat.Internal.rhoFactorCountedWith?
    10160604446909624364520940818952867768480456910917673106556136406570399304040109818357670366579606503796352267531946460412610364318428260037531749637423201
    (Hex.Rand.ofSeed
      10160604446909624364520940818952867768480456910917673106556136406570399304040109818357670366579606503796352267531946460412610364318428260037531749637423201)
    natPrimeRhoRestartBudget natPrimeRhoStepBudget with
  | .ok success =>
      1 < success.factor &&
        success.factor <
          10160604446909624364520940818952867768480456910917673106556136406570399304040109818357670366579606503796352267531946460412610364318428260037531749637423201 &&
        10160604446909624364520940818952867768480456910917673106556136406570399304040109818357670366579606503796352267531946460412610364318428260037531749637423201 %
          success.factor == 0 &&
        success.attempts == natPrimeRhoRestartBudget
  | .error _ => false)

example : Nat.Prime 16777121 := by norm_num       -- last tested prime below the threshold
example : Nat.Prime 16777259 := by norm_num       -- first prime above the threshold
example : ¬ Nat.Prime 16777216 := by norm_num     -- the threshold itself
example : ¬ Nat.Prime 16777217 := by norm_num     -- one seeded rho restart, factor 97
example : Nat.Prime 2147483647 := by norm_num     -- certificate-backed positive proof
example : Nat.Prime 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177 := by
  norm_num                                          -- exact 512-bit ceiling
example : ¬ Nat.Prime 2147483649 := by norm_num   -- validated factor proof
example : ¬ Nat.Prime 3215031751 := by norm_num   -- strong pseudoprime to bases 2, 3, 5, 7
example : ¬ Nat.Prime 18446744073709551617 := by norm_num -- 65-bit odd factor search
example : ¬ Nat.Prime 0 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num

-- Bounded certificate production exhausts on this adversarial input. The
-- guarded trial alias must decline too: no large trial proof is attempted
-- after bounded Hex search is exhausted.
/--
error: unsolved goals
⊢ Nat.Prime
    11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123
-/
#guard_msgs in
example : Nat.Prime 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 := by
  norm_num

/--
error: unsolved goals
⊢ Nat.Prime
    13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
-/
#guard_msgs in
example : Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  norm_num

-- The input ceiling applies to negative goals too; the opt-in extension does
-- not silently recover Mathlib's unbounded trial decision above the ceiling.
/--
error: unsolved goals
⊢ ¬Nat.Prime
      13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
-/
#guard_msgs in
example : ¬ Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  norm_num
