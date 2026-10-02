/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext
import all HexRealClosure.BaseJson
import all HexRealClosure.AlgebraicCodec
import all HexRealClosure.TowerContext

public section

namespace Hex.RealClosure.Tower
open SignDet

variable {registry : BaseContext.Registry}

/-- Context frames already use the certificate JSON type. Conversion to a
frame is the identity, so the optional format-failure branch is unreachable. -/
theorem Context.adjoin_isSome (context : Context registry)
    (descriptor : Descriptor context.Value Signature context.sign context.signature) :
    (context.adjoin? descriptor).isSome = true := by
  cases context with
  | pack chain => rfl

/-- Total native extension from an already validated descriptor. All frame
data and the actual embedding/generator are the existing checked operations. -/
def Context.adjoin (context : Context registry)
    (descriptor : Descriptor context.Value Signature context.sign context.signature) :
    Extension context descriptor :=
  (context.adjoin? descriptor).get (context.adjoin_isSome descriptor)

theorem Context.adjoin_some (context : Context registry)
    (descriptor : Descriptor context.Value Signature context.sign context.signature) :
    context.adjoin? descriptor = some (context.adjoin descriptor) :=
  (Option.some_get (context.adjoin_isSome descriptor)).symm

section
variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}

/-- The total facade returns exactly the existing native child and maps. -/
theorem Context.adjoin_native (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding) :
    let extension := Context.adjoin (.pack chain) descriptor
    extension.context = .pack (.root chain descriptor extension.frame extension.encoded) ∧
      HEq extension.embed (Algebraic.Element.ofCoeff
        (context := Algebraic.Context.adjoin descriptor clean)) ∧
      HEq extension.generator (Algebraic.Element.ofPoly
        (context := Algebraic.Context.adjoin descriptor clean) (DensePoly.ofCoeffs #[0, 1])) :=
  Context.adjoin_spec chain descriptor _ (Context.adjoin_some (.pack chain) descriptor)

/-- The total facade retains the same native packing closure. -/
theorem Context.adjoin_pack (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding) :
    HEq (Context.adjoin (.pack chain) descriptor).pack (Algebraic.Element.ofPoly
      (context := Algebraic.Context.adjoin descriptor clean)) :=
  Context.pack_spec chain descriptor _ (Context.adjoin_some (.pack chain) descriptor)

end

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.adjoin_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.adjoin_isSome
