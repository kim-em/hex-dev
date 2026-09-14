/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflectMathlib.Carrier
public import HexModArithMathlib.Ring
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.MvPolynomial.Basic
public meta import HexReflect.Provider
public meta import HexArith.Nat.Prime

public section

namespace HexReflectMathlib

open Hex.Reflect
open scoped HexModArithMathlib.ZMod64

/-- Interpret machine residues in any ring of the same characteristic. -/
def residueHom (p : Nat) [Hex.ZMod64.Bounds p] (F : Type u) [CommRing F] [CharP F p] :
    Hex.ZMod64 p →+* F :=
  (ZMod.castHom (dvd_refl p) F).comp HexModArithMathlib.ZMod64.equiv.toRingHom

/-- The characteristic assumption makes the coefficient interpretation injective,
including when the field is an extension of its prime field. -/
theorem residueHom_injective (p : Nat) [Hex.ZMod64.Bounds p]
    (F : Type u) [CommRing F] [CharP F p] : Function.Injective (residueHom p F) :=
  (ZMod.castHom_injective F (n := p)).comp HexModArithMathlib.ZMod64.equiv.injective

/-- Residue interpretation commutes with ring homomorphisms. -/
theorem residueHom_comp (p : Nat) [Hex.ZMod64.Bounds p]
    {D : Type u} {F : Type v} [CommRing D] [CommRing F] [CharP D p] [CharP F p]
    (f : D →+* F) : f.comp (residueHom p D) = residueHom p F := by
  unfold residueHom
  rw [← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

/-- In a multivariate polynomial ring, residues are constant polynomials. -/
theorem residueHom_mvPolynomial (p : Nat) [Hex.ZMod64.Bounds p]
    (σ : Type v) (D : Type u) [CommRing D] [CharP D p] :
    residueHom p (MvPolynomial σ D) = MvPolynomial.C.comp (residueHom p D) :=
  (residueHom_comp p MvPolynomial.C).symm

/-- In a univariate polynomial ring, residues are constant polynomials. -/
theorem residueHom_polynomial (p : Nat) [Hex.ZMod64.Bounds p]
    (D : Type u) [CommRing D] [CharP D p] :
    residueHom p (Polynomial D) = Polynomial.C.comp (residueHom p D) :=
  (residueHom_comp p Polynomial.C).symm

/-- Residue coefficients satisfy reflection's laws by the ring homomorphism laws. -/
theorem residueCoeffLaws (p : Nat) [Hex.ZMod64.Bounds p]
    (F : Type u) [CommRing F] [CharP F p] :
    CoeffLaws (C := Hex.ZMod64 p) (α := F) Int.cast (residueHom p F) :=
  coeffLaws_ofRingHom (residueHom p F) Int.cast (fun k => map_intCast _ k)

/-- A nonzero domain characteristic supplies the prime-modulus evidence needed
by executable coefficient algorithms, without replaying a primality search. -/
theorem residuePrime (p : Nat) (F : Type u) [CommRing F] [IsDomain F] [CharP F p] (hp : 0 < p) :
    Hex.ZMod64.PrimeModulus p := by
  have prime := (CharP.char_is_prime_or_zero F p).resolve_right (Nat.ne_of_gt hp)
  exact ⟨⟨prime.two_le, fun _ h => (Nat.dvd_prime prime).mp h⟩⟩

meta section

open Lean Meta

/-- Stable identity of the positive-characteristic coefficient registration. -/
def residueCoefficientsId : ProviderId := { name := `HexReflectMathlib.residueCoefficients }

/-- Recognize a known positive characteristic and quote the residue coefficient
provider against the classified carrier's exact ring instance. -/
def residueCoeffProvider (p : Nat) (ring : CarrierRequest) :
    Sym.SymM (ProviderOutcome CoeffProvider) := withNewMCtxDepth do
  let decline (reason : String) : ProviderOutcome CoeffProvider :=
    .declined (.providerCondition residueCoefficientsId reason) Budget.zero
  let bound := Nat.pow 2 31
  if p ≥ bound then
    return decline "residue coefficients require characteristic p < 2^31"
  if !Hex.Nat.isPrimeTrial p then
    return decline "residue coefficients require prime characteristic"
  let pE := mkNatLit p
  -- Canonicalization unfolds a concrete `ZMod p` to `Fin p`. Try the
  -- corresponding Mathlib carrier as well, but require definitional equality
  -- of the type and interpretation operations before accepting its evidence.
  let mut carrier := ring.type
  let mut commRingInst? ← Sym.synthInstance? (mkApp (mkConst ``CommRing [ring.u]) carrier)
  if commRingInst?.isNone then
    let zmod := mkApp (mkConst ``ZMod) pE
    if ← isDefEq ring.type zmod then
      carrier := zmod
      commRingInst? ← Sym.synthInstance? (mkApp (mkConst ``CommRing [ring.u]) carrier)
  let some commRingInst := commRingInst?
    | return decline "residue coefficients require Mathlib CommRing evidence"
  let mathlibRingInst ← mkAppOptM ``CommRing.toRing #[carrier, commRingInst]
  let mathlibSemiring ← mkAppOptM ``Ring.toSemiring #[carrier, mathlibRingInst]
  let domainType ← mkAppOptM ``IsDomain #[carrier, mathlibSemiring]
  let some domainInst ← Sym.synthInstance? domainType
    | return decline "residue coefficients require Mathlib IsDomain evidence"
  let mathlibRing ← mkAppOptM ``Ring.toGrindRing #[carrier, mathlibRingInst]
  let addGroup ← mkAppOptM ``Ring.toAddGroupWithOne #[carrier, mathlibRingInst]
  let castInst ← mkAppOptM ``AddGroupWithOne.toAddMonoidWithOne #[carrier, addGroup]
  let charType ← mkAppOptM ``CharP #[carrier, castInst, pE]
  let some charInst ← Sym.synthInstance? charType
    | return decline "residue coefficients require Mathlib CharP evidence"
  let pos ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, pE])
  let bounds ← mkAppM ``Hex.ZMod64.Bounds.mk #[pos,
    ← mkDecideProof (← mkAppM ``LT.lt #[pE, mkNatLit bound])]
  let coeffType := mkApp2 (mkConst ``Hex.ZMod64) pE bounds
  let zeroInst ← mkAppOptM ``Hex.ZMod64.instZero #[pE, bounds]
  let addInst ← mkAppOptM ``Hex.ZMod64.instAdd #[pE, bounds]
  let decEq ← mkAppOptM ``Hex.ZMod64.instDecidableEq #[pE, bounds]
  let beqInst ← mkAppOptM ``instBEqOfDecidableEq #[coeffType, decEq]
  let lawfulBEqInst ← mkAppOptM ``instLawfulBEq #[coeffType, decEq]
  let intCast ← mkAppOptM ``Hex.ZMod64.instIntCast #[pE, bounds]
  let ofInt ← mkAppOptM ``Int.cast #[coeffType, intCast]
  let hom ← mkAppOptM ``residueHom #[pE, bounds, carrier, commRingInst, charInst]
  let interp ← mkAppM ``DFunLike.coe #[hom]
  let laws ← mkAppOptM ``residueCoeffLaws #[pE, bounds, carrier, commRingInst, charInst]
  let bridge := mkAppN (mkConst ``CoeffLaws.changeRing [ring.u])
    #[coeffType, ring.type, zeroInst, addInst, mathlibRing, ring.ringInst, ofInt, interp, laws]
  let laws? ← forallTelescopeReducing (← inferType bridge) fun hs _ => do
    let mut proofs := #[]
    for h in hs do
      let some (_, lhs, rhs) := (← inferType h).eq? | return none
      unless ← isDefEq lhs rhs do return none
      proofs := proofs.push (← mkEqRefl lhs)
    return some (mkAppN bridge proofs)
  let some laws := laws?
    | return decline "the classified ring operations do not agree with the Mathlib ring"
  let prime ← mkAppOptM ``residuePrime #[pE, carrier, commRingInst, domainInst, charInst, pos]
  let coeffRing ← mkAppOptM ``HexModArithMathlib.ZMod64.commRing #[pE, bounds]
  return .success {
    id := residueCoefficientsId
    coeffType, zeroInst, addInst, beqInst, lawfulBEqInst, ofInt, interp, laws
    auxInstances := #[bounds, prime, coeffRing]
  } Budget.zero

/-- Prefer residue coefficients to universal integers for a classified positive
characteristic. Unknown characteristic and characteristic zero keep integers. -/
@[hex_reflect_provider]
def residueCoefficients : Registration where
  id := residueCoefficientsId
  capability := .commRingNormalize
  priority := 5
  recognize ring := do
    let some (_, p) := ring.charInst? | return .notApplicable
    if p == 0 then return .notApplicable
    return (← residueCoeffProvider p ring).map Evidence.coefficients

end
end HexReflectMathlib
