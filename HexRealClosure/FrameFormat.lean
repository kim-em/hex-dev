/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.CodecSupport
public import HexRealClosure.TowerContext
import all HexRealClosure.BaseJson
import all HexRealClosure.AlgebraicCodec
import all HexRealClosure.TowerContext

public section

namespace Hex.RealClosure.Tower
open Lean SignDet

theorem Literal.Supported.base_value {registry : BaseContext.Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : BaseContext.Context registry K sign) (a : BaseContext.Element context) :
    Supported ((BaseContext.Element.codec context).encode a) :=
  Literal.supported_toJson _

section
variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {binding : Signature}
variable {context : Algebraic.Context E Signature sign binding}

theorem Literal.Supported.algebraic_value (value : ValueCodec E)
    (h : ∀ a, Supported (value.encode a)) (a : Algebraic.Element context) :
    Supported ((Algebraic.Element.codec value).encode a) := by
  simp only [Algebraic.Element.codec]
  cases hs : a.stored with
  | none => simp [Supported.arr_iff]
  | some p => simp [Supported.arr_iff, Supported.poly value h]

theorem Literal.Supported.reference (parent binding : Signature) :
    Supported ((contextCodec parent).encode binding) := by
  by_cases he : binding = parent <;>
    simp [contextCodec, he, Supported.arr_iff, Literal.supported_toJson, Supported.num]

omit [Neg E] [Inv E] [Div E] in
theorem Literal.Supported.rootData (value : ValueCodec E)
    (h : ∀ a, Supported (value.encode a))
    (descriptor : Descriptor E Signature sign binding) : Supported (rootData value descriptor) := by
  simp only [Hex.RealClosure.Tower.rootData]
  simp [Supported.arr_iff, Supported.reference, Supported.poly value h,
    Supported.endpoint value h, Supported.graph value h _ (Supported.reference binding)]

variable {registry : BaseContext.Registry} {clean : E → Bool} {codec : ValueCodec E}

/-- Native staged coefficient encoders always emit supported structured data.
This is derived from the actual chain, not supplied as a constructor law. -/
theorem Chain.codec_supported (chain : Chain registry E sign clean codec binding) :
    ∀ a, Literal.Supported (codec.encode a) := by
  induction chain with
  | base context => exact Literal.Supported.base_value context
  | root parent descriptor frame encoded ih =>
    exact Literal.Supported.algebraic_value _ ih

end

variable {registry : BaseContext.Registry}

theorem Context.codec_supported (context : Context registry) :
    ∀ a, Literal.Supported (context.codec.encode a) := by
  cases context with
  | pack chain => exact chain.codec_supported

/-- Every validated descriptor over a native context has a supported frame;
the optional facade's format-failure branch is unreachable. -/
theorem Context.adjoin_isSome (context : Context registry)
    (descriptor : Descriptor context.Value Signature context.sign context.signature) :
    (context.adjoin? descriptor).isSome = true := by
  cases context with
  | pack chain =>
    obtain ⟨frame, hf⟩ := (Literal.Supported.rootData _ chain.codec_supported descriptor).read
    simp only [Context.adjoin?]
    split
    · rename_i he
      have hn : (none : Option Literal) = some frame := he.symm.trans hf
      cases hn
    · rfl

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

/-- info: 'Hex.RealClosure.Tower.Literal.Supported.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Literal.Supported.read
