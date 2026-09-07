/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.Irreducibility
public import HexPolyFp.ModCompose

public section

namespace Hex.Conway

variable {p : Nat} [ZMod64.Bounds p]

/-- Kernel-replayable modular composition using structural Horner evaluation. -/
@[expose] def compose (f g modulus : FpPoly p) (hm : DensePoly.Monic modulus) : FpPoly p :=
  FpPoly.composeModMonicList g modulus hm f.toArray.toList

/-- Structural composition agrees with the compiled packed dispatcher. -/
theorem compose_eq (f g modulus : FpPoly p) (hm : DensePoly.Monic modulus) :
    compose f g modulus hm = FpPoly.composeModMonicImpl f g modulus hm :=
  FpPoly.composeModMonic_eq_composeModMonicImpl f g modulus hm

/-- Preserve the optimized implementation in compiled clients. -/
@[csimp] theorem compose_eq_impl : @compose = @FpPoly.composeModMonicImpl := by
  funext p _ f g modulus hm
  exact compose_eq f g modulus hm

/-- Structural square-and-multiply. Fuel bounds the number of steps; the
exponent is halved at each step. No well-founded recursion is replayed. -/
@[expose] def powAux (f : FpPoly p) (hm : DensePoly.Monic f) :
    Nat → Nat → FpPoly p → FpPoly p → FpPoly p
  | 0, _, _, acc => acc
  | _ + 1, 0, _, acc => acc
  | fuel + 1, n + 1, base, acc =>
      powAux f hm fuel ((n + 1) / 2)
        (FpPoly.modByMonic f (base * base) hm)
        (if (n + 1) % 2 = 0 then acc else FpPoly.modByMonic f (acc * base) hm)

/-- With sufficient fuel, structural replay agrees with executable modular power. -/
theorem powAux_eq (f : FpPoly p) (hm : DensePoly.Monic f) (fuel n : Nat)
    (base acc : FpPoly p) (h : n ≤ fuel) :
    powAux f hm fuel n base acc = FpPoly.powModMonicAux f hm n base acc := by
  induction fuel generalizing n base acc with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rw [powAux, FpPoly.powModMonicAux.eq_def]
  | succ fuel ih =>
      cases n with
      | zero => rw [powAux, FpPoly.powModMonicAux.eq_def]
      | succ n =>
          rw [powAux, FpPoly.powModMonicAux.eq_def]
          apply ih
          have := Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)
          omega

/-- Kernel-replayable binary modular power. The exponent itself is a
conservative fuel bound; only logarithmically many steps are evaluated. -/
@[expose] def powMod (base f : FpPoly p) (hm : DensePoly.Monic f) (n : Nat) : FpPoly p :=
  powAux f hm n n (FpPoly.modByMonic f base hm) 1

/-- Structural binary power computes the same residue as linear power. -/
theorem powMod_eq [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hm : DensePoly.Monic f) (n : Nat) :
    powMod base f hm n = FpPoly.powModMonicLinear base f hm n := by
  rw [FpPoly.powModMonicLinear_eq_powModMonic]
  exact powAux_eq f hm n n _ _ (Nat.le_refl n)

/-- One Frobenius step checked by structural binary exponentiation. -/
@[expose] def checkStep (f : FpPoly p) (hm : DensePoly.Monic f)
    (cert : Berlekamp.SamePrimeIrreducibilityCertificate p) (k : Nat) : Bool :=
  match cert.powChain[k]?, cert.powChain[k+1]? with
  | some prev, some next => next == powMod prev f hm p
  | _, _ => false

/-- Binary replay of the committed Frobenius chain. -/
@[expose] def checkChain (f : FpPoly p) (hm : DensePoly.Monic f)
    (cert : Berlekamp.SamePrimeIrreducibilityCertificate p) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (cert.powChain[0]? == some (FpPoly.modByMonic f FpPoly.X hm)) &&
    (List.range cert.n).all fun k => checkStep f hm cert k

/-- Rabin certificate replay using binary modular powers. The certificate
shape and every check other than the power implementation are unchanged. -/
@[expose] def checkRabin (f : FpPoly p) (hm : DensePoly.Monic f)
    (cert : Berlekamp.IrreducibilityCertificate) : Bool :=
  match cert.toAmbient? p with
  | none => false
  | some c =>
      decide (0 < c.n) && decide (c.n = Berlekamp.basisSize f) &&
        checkChain f hm c &&
        (c.powChain[c.n]? == some (FpPoly.modByMonic f FpPoly.X hm)) &&
        Berlekamp.checkRabinBezoutWitnesses f hm c

/-- Binary replay preserves the existing Rabin checker exactly. -/
theorem checkRabin_eq [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hm : DensePoly.Monic f) (cert : Berlekamp.IrreducibilityCertificate) :
    checkRabin f hm cert = Berlekamp.checkIrreducibilityCertificateLinearIncremental f hm cert := by
  simp only [checkRabin, Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    checkChain, Berlekamp.checkPowChainLinearIncremental, checkStep,
    Berlekamp.checkPowChainLinearIncrementalStep, powMod_eq]
  cases cert.toAmbient? p <;> rfl

end Hex.Conway
