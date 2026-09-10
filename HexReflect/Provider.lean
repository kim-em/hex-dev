/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Result
public import HexReflect.Convert
public import Lean
public meta import Lean
public meta import HexReflect.Convert
public meta import HexReflect.Result

public section

/-!
The provider protocol.

A provider supplies executable operations together with the theorems needed
to interpret them. There are two levels: theorem-level records, used by
Mathlib-free computations, and Meta registrations, which recognize a carrier
with its exact instances, quote values, and select the theorem-level record.
Registration is separate from `Lean.Meta.Sym.Arith` recognition: it can change
which verified computation handles a request, but never the source grammar or
atom allocation.
-/

namespace Hex.Reflect

open Lean

attribute [local instance] Lean.Grind.Ring.intCast

/-- The laws a coefficient interpretation must satisfy for
`Hex.MvPoly.eval₂` to agree with the Grind denotation: the map from reflected
integer coefficients agrees with the integer cast, and the interpretation is
additive and fixes zero. -/
structure CoeffLaws {C : Type} {α : Type u} [Zero C] [Add C] [Lean.Grind.Ring α]
    (ofInt : Int → C) (interp : C → α) : Prop where
  /-- The coefficient map followed by the interpretation is the integer
  cast. -/
  interp_ofInt : ∀ k : Int, interp (ofInt k) = (k : α)
  /-- The interpretation fixes zero. -/
  interp_zero : interp 0 = 0
  /-- The interpretation is additive. -/
  interp_add : ∀ a b : C, interp (a + b) = interp a + interp b

/-- Integer coefficients interpreted by the integer cast satisfy the laws in
every ring. -/
theorem CoeffLaws.int {α : Type u} [Lean.Grind.Ring α] :
    CoeffLaws (C := Int) (α := α) id Int.cast where
  interp_ofInt _ := rfl
  interp_zero := Lean.Grind.Ring.intCast_zero
  interp_add := Lean.Grind.Ring.intCast_add

/-- A coefficient provider selected for one carrier: the quoted coefficient
type, its instances, the coefficient map, the interpretation into the
carrier, and the proof of `CoeffLaws`. The executable conversion keeps the
integer coefficients produced by normalization; the quoted polynomial maps
them through `ofInt`. -/
structure CoeffProvider where
  id : ProviderId
  /-- The quoted coefficient type `C : Type`. -/
  coeffType : Expr
  zeroInst : Expr
  addInst : Expr
  beqInst : Expr
  lawfulBEqInst : Expr
  /-- The quoted coefficient map `Int → C`. -/
  ofInt : Expr
  /-- The quoted interpretation `C → α`. -/
  interp : Expr
  /-- A proof of `CoeffLaws ofInt interp` for the carrier's exact instances. -/
  laws : Expr

/-- Evidence returned by a recognizing registration. -/
inductive Evidence where
  /-- A coefficient provider for commutative-ring normalization. -/
  | coefficients (provider : CoeffProvider)
  /-- A quoted theorem-level record for a capability without an executable
  form in this library. -/
  | record (declName : Name) (value : Expr)

/-- The carrier data a registration recognizes: the classified commutative
ring with its exact instances. -/
abbrev CarrierRequest := Lean.Meta.Sym.Arith.CommRing

/-- A Meta registration. `recognize` inspects the canonical carrier and its
exact instances and reports one of the four provider outcomes:
`notApplicable` when the provider does not recognize the request, `declined`
when it recognizes the request but cannot satisfy a stated condition,
`success` with evidence, or `failure` when its own data is malformed. -/
structure Registration where
  /-- Stable provider identity for diagnostics and condition provenance. -/
  id : ProviderId
  /-- The capability this registration supplies. -/
  capability : Capability
  /-- Higher priorities are consulted first. -/
  priority : Nat := 0
  /-- Recognize the classified carrier with its exact instances. -/
  recognize : CarrierRequest → Lean.Meta.Sym.SymM (ProviderOutcome Evidence)

/-! # The universal integer coefficient provider -/

meta section

/-- Identity of the integer coefficient provider. -/
def intCoefficientsId : ProviderId := { name := `Hex.Reflect.intCoefficients }

/-- Quote `CoeffLaws.int` at the carrier, synthesizing the integer instances
in the current `SymM`. -/
def intCoeffProvider (ring : CarrierRequest) : Lean.Meta.Sym.SymM CoeffProvider := do
  let intType := mkConst ``Int
  let zeroInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``Zero [.zero]) intType)
  let addInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``Add [.zero]) intType)
  let beqInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``BEq [.zero]) intType)
  let lawfulBEqInst ← Lean.Meta.Sym.synthInstance
    (mkApp2 (mkConst ``LawfulBEq [.zero]) intType beqInst)
  return {
    id := intCoefficientsId
    coeffType := intType
    zeroInst, addInst, beqInst, lawfulBEqInst
    ofInt := mkApp (mkConst ``id [.succ .zero]) intType
    interp := mkApp2 (mkConst ``Int.cast [ring.u]) ring.type
      (mkApp2 (mkConst ``Lean.Grind.Ring.intCast [ring.u]) ring.type ring.ringInst)
    laws := mkApp2 (mkConst ``CoeffLaws.int [ring.u]) ring.type ring.ringInst }

/-- Integer coefficients apply to every classified commutative ring. The
registration attribute is attached where the attribute is available, in
`HexReflect.Session`. -/
def intCoefficients : Registration where
  id := intCoefficientsId
  capability := .commRingNormalize
  recognize ring := return .success (.coefficients (← intCoeffProvider ring)) Budget.zero

/-! # Registry -/

/-- Registered provider declarations, in registration order. -/
initialize providerExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss => nss.flatten
    addEntryFn := fun s n => s.push n
  }

initialize registerBuiltinAttribute {
  name := `hex_reflect_provider
  descr := "register a `Hex.Reflect.Registration` for provider lookup"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `hex_reflect_provider kind
    let declType := (← getConstInfo decl).type
    unless declType.isConstOf ``Registration do
      throwAttrDeclNotOfExpectedType `hex_reflect_provider decl declType
        (mkConst ``Registration)
    modifyEnv fun env => providerExt.addEntry env decl
}

private unsafe def evalRegistrationUnsafe (n : Name) : MetaM Registration :=
  evalConst Registration n

@[implemented_by evalRegistrationUnsafe]
private opaque evalRegistrationCore (n : Name) : MetaM Registration

/-- Every registration in the current environment, in registration order. -/
def registrations : MetaM (Array Registration) := do
  let names := providerExt.getState (← getEnv)
  names.mapM evalRegistrationCore

end

end Hex.Reflect
