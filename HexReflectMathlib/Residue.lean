/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflectMathlib.Carrier
public import HexModArithMathlib.Ring
public import Mathlib.Algebra.Field.Defs
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

/-- Residue coefficients satisfy reflection's laws by the ring homomorphism laws. -/
theorem residueCoeffLaws (p : Nat) [Hex.ZMod64.Bounds p]
    (F : Type u) [CommRing F] [CharP F p] :
    CoeffLaws (C := Hex.ZMod64 p) (α := F) Int.cast (residueHom p F) :=
  coeffLaws_ofRingHom (residueHom p F) Int.cast (fun k => map_intCast _ k)

meta section

open Lean Meta

/-- Stable identity of the positive-characteristic coefficient registration. -/
def residueCoefficientsId : ProviderId := { name := `HexReflectMathlib.residueCoefficients }

/-- Recognize a known positive characteristic and quote the residue coefficient
provider against the classified carrier's exact ring instance. -/
def residueCoeffProvider (p : Nat) (ring : CarrierRequest) :
    Sym.SymM (ProviderOutcome CoeffProvider) := do
  let decline (reason : String) : ProviderOutcome CoeffProvider :=
    .declined (.providerCondition residueCoefficientsId reason) Budget.zero
  if p ≥ 2147483648 then
    return decline "residue coefficients require characteristic p < 2^31"
  if !Hex.Nat.isPrimeTrial p then
    return decline "residue coefficients require prime characteristic"
  let pE := mkNatLit p
  -- Canonicalization unfolds a concrete `ZMod p` to `Fin p`. Try the
  -- corresponding Mathlib carrier as well, but require definitional equality
  -- of the type and interpretation operations before accepting its evidence.
  let mut carrier := ring.type
  let mut fieldInst? ← Sym.synthInstance? (mkApp (mkConst ``Field [ring.u]) carrier)
  if fieldInst?.isNone then
    let zmod := mkApp (mkConst ``ZMod) pE
    if ← isDefEq ring.type zmod then
      carrier := zmod
      fieldInst? ← Sym.synthInstance? (mkApp (mkConst ``Field [ring.u]) carrier)
  let some fieldInst := fieldInst?
    | return decline "residue coefficients require a Mathlib Field instance"
  let commRingInst ← mkAppOptM ``Field.toCommRing #[carrier, fieldInst]
  let mathlibRingInst ← mkAppOptM ``CommRing.toRing #[carrier, commRingInst]
  let mathlibRing ← mkAppOptM ``Ring.toGrindRing #[carrier, mathlibRingInst]
  let addGroup ← mkAppOptM ``Ring.toAddGroupWithOne #[carrier, mathlibRingInst]
  let castInst ← mkAppOptM ``AddGroupWithOne.toAddMonoidWithOne #[carrier, addGroup]
  let charType ← mkAppOptM ``CharP #[carrier, castInst, pE]
  let some charInst ← Sym.synthInstance? charType
    | return decline "residue coefficients require Mathlib CharP evidence"
  let bounds ← mkAppM ``Hex.ZMod64.Bounds.mk #[
    ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, pE]),
    ← mkDecideProof (← mkAppM ``LT.lt #[pE, mkNatLit 2147483648])]
  let prime ← mkAppM ``Hex.ZMod64.primeModulusOfPrime #[
    ← mkDecideProof (mkApp (mkConst ``Hex.Nat.Prime) pE)]
  let coeffRing ← mkAppOptM ``HexModArithMathlib.ZMod64.commRing #[pE, bounds]
  let coeffType := mkApp2 (mkConst ``Hex.ZMod64) pE bounds
  let zeroInst ← Sym.synthInstance (mkApp (mkConst ``Zero [.zero]) coeffType)
  let addInst ← Sym.synthInstance (mkApp (mkConst ``Add [.zero]) coeffType)
  let beqInst ← Sym.synthInstance (mkApp (mkConst ``BEq [.zero]) coeffType)
  let lawfulBEqInst ← Sym.synthInstance
    (mkApp2 (mkConst ``LawfulBEq [.zero]) coeffType beqInst)
  let ofInt ← mkAppOptM ``Int.cast #[coeffType, none]
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
    | return decline "the classified ring operations do not agree with the Mathlib field"
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
