/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.AlgebraicCodec
public import HexRealClosure.BaseJson
public import HexSignDet.Codec
public import HexSignDet.DagEncode

public section

namespace Hex.RealClosure.Tower
open Lean SignDet

/-- Complete ordered context identity within one immutable registry. Every
algebraic frame retains the literal selected-root descriptor and replay graph;
short names and hashes never replace these fields. -/
structure Signature where
  base : BaseContext.Signature
  roots : List Literal
  deriving DecidableEq, Repr

@[expose] def Signature.literal (signature : Signature) : Literal :=
  .array (.cons (.array (Literals.ofList (signature.base.constants.map fun key =>
    .array (.cons (.string key.name) (.cons (.number key.version 0) .nil)))))
    (.cons (.number signature.base.infinitesimals 0)
      (.cons (.array (Literals.ofList signature.roots)) .nil)))

@[expose] def Signature.extend (signature : Signature) (frame : Literal) : Signature :=
  { signature with roots := signature.roots ++ [frame] }

/-- A node's reference to the exact enclosing predecessor is encoded once by
that enclosing signature. Other literal contexts are retained in full. This
avoids copying the entire predecessor into every node of its replay graph. -/
private def contextCodec (parent : Signature) : ValueCodec Signature where
  encode context := if context = parent then .arr #[toJson (0 : Nat)]
    else .arr #[toJson (1 : Nat), context.literal.toJson]
  decode _ := .error "encoding-only context codec"

section

variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {binding : Signature}

/-- Serialize the actual finite replay graph, with sharing determined by exact
node equality. Hashing only indexes that equality search. The descriptor's
head, bounds and ordered Thom slots are retained separately from the replay. -/
def rootData (value : ValueCodec E) (root : Descriptor E Signature sign binding) : Json :=
  letI : Hashable E := ⟨fun a => match Literal.ofJson (value.encode a) with
    | some literal => hash literal
    | none => 0⟩
  letI : Hashable Signature := ⟨fun context => hash
    (context.base.constants.map (fun key => (key.name, key.version)),
      context.base.infinitesimals, context.roots)⟩
  let ctx := contextCodec binding
  .arr #[ctx.encode root.raw.context, Codec.poly value root.raw.head,
    Codec.endpoint value root.raw.lower, Codec.endpoint value root.raw.upper,
    toJson root.raw.indices, toJson root.raw.signs,
    Codec.graph value ctx (Dag.encode root.evidence)]

/-- Finite staged tower. All coefficient operations are the ordinary native
operations selected by these constructors. The base is completed before the
first algebraic root; every subsequent root uses the whole previous carrier.
The only extra erased premise records exact structured serialization. -/
inductive Chain (registry : BaseContext.Registry) :
    (E : Type) → [Zero E] → [DecidableEq E] → [One E] → [Add E] → [Neg E] →
    [Sub E] → [Mul E] → [Inv E] → [Div E] → [NatCast E] →
    (E → Int) → (E → Bool) → ValueCodec E → Signature → Type 1
  | base {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
      (context : BaseContext.Context registry K sign) :
      Chain registry (BaseContext.Element context)
        BaseContext.Element.sign BaseContext.Element.isClean
        (BaseContext.Element.codec context) ⟨context.signature, []⟩
  | root {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Neg E]
      [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
      {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}
      (parent : Chain registry E sign clean codec binding)
      (descriptor : Descriptor E Signature sign binding) (frame : Literal)
      (encoded : Literal.ofJson (rootData codec descriptor) = some frame) :
      Chain registry (Algebraic.Element (Algebraic.Context.adjoin descriptor clean))
        Algebraic.Element.sign Algebraic.Element.isClean (Algebraic.Element.codec codec)
        (binding.extend frame)

variable {registry : BaseContext.Registry} {clean : E → Bool} {codec : ValueCodec E}

/-- Every tower's actual recursive coefficient reader restores literal forms.
No ring or field instance on algebraic representatives is needed. -/
theorem Chain.codec_lawful (chain : Chain registry E sign clean codec binding) :
    codec.Lawful := by
  induction chain with
  | base context => exact BaseContext.Element.codec_lawful context
  | root parent descriptor frame encoded ih => exact Algebraic.Element.codec_lawful _ ih

/-- The checked frame retains the entire structured descriptor and replay. -/
theorem Chain.frame_data (descriptor : Descriptor E Signature sign binding) (frame : Literal)
    (h : Literal.ofJson (rootData codec descriptor) = some frame) :
    frame.toJson = rootData codec descriptor := Literal.toJson_ofJson _ _ h

/-- Attach the actual descriptor to the whole predecessor and retain its
complete checked frame. Format failure is separate from descriptor validity. -/
def Chain.adjoin? (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding) :
    Option (Σ frame : Literal,
      Chain registry (Algebraic.Element (Algebraic.Context.adjoin descriptor clean))
        Algebraic.Element.sign Algebraic.Element.isClean (Algebraic.Element.codec codec)
        (binding.extend frame)) :=
  match he : Literal.ofJson (rootData codec descriptor) with
  | none => none
  | some frame => some ⟨frame, .root chain descriptor frame he⟩

end

variable {registry : BaseContext.Registry}

/-- A dynamically reconstructed context still owns its complete native tower.
The existential operation instances come only from the staged constructors. -/
inductive Context (registry : BaseContext.Registry) : Type 1
  | pack {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Neg E]
      [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
      {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}
      (chain : Chain registry E sign clean codec binding)

@[expose, reducible] def Context.Value (context : Context registry) : Type := by
  cases context with
  | @pack E => exact E

@[instance_reducible] instance (context : Context registry) : Zero context.Value := by
  cases context with
  | @pack E => change Zero E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : DecidableEq context.Value := by
  cases context with
  | @pack E => change DecidableEq E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : One context.Value := by
  cases context with
  | @pack E => change One E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : Add context.Value := by
  cases context with
  | @pack E => change Add E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : Neg context.Value := by
  cases context with
  | @pack E => change Neg E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : Sub context.Value := by
  cases context with
  | @pack E => change Sub E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : Mul context.Value := by
  cases context with
  | @pack E => change Mul E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : Inv context.Value := by
  cases context with
  | @pack E => change Inv E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : Div context.Value := by
  cases context with
  | @pack E => change Div E; exact inferInstance
@[instance_reducible] instance (context : Context registry) : NatCast context.Value := by
  cases context with
  | @pack E => change NatCast E; exact inferInstance

@[expose] def Context.signature (context : Context registry) : Signature := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ _ _ _ binding => exact binding

@[expose] def Context.sign (context : Context registry) : context.Value → Int := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ sign => exact sign

@[expose] def Context.isClean (context : Context registry) : context.Value → Bool := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ _ clean => exact clean

@[expose] def Context.codec (context : Context registry) : ValueCodec context.Value := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ _ _ codec => exact codec

theorem Context.codec_lawful (context : Context registry) : context.codec.Lawful := by
  cases context with
  | pack chain => exact chain.codec_lawful

/-- No real or infinitesimal extension can be added after this base is packed.
Those stages are assembled through the native base-context constructors. -/
def Context.base {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : BaseContext.Context registry K sign) : Context registry := .pack (.base context)

private theorem Context.base_signature_proof {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (context : BaseContext.Context registry K sign) :
    (Context.base context).signature = ⟨context.signature, []⟩ := rfl

theorem Context.base_signature {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (context : BaseContext.Context registry K sign) :
    (Context.base context).signature = ⟨context.signature, []⟩ :=
  Context.base_signature_proof context

/-- One persistent root extension with explicit predecessor inclusion and a
selected generator. The old context and its values retain their ownership. -/
structure Extension (parent : Context registry) : Type 1 where
  private mk ::
  context : Context registry
  embed : parent.Value → context.Value
  generator : context.Value

/-- The descriptor uses this context's exact value type, sign and signature.
The returned embedding is the actual constant-polynomial packing operation. -/
def Context.adjoin? (context : Context registry)
    (descriptor : Descriptor context.Value Signature context.sign context.signature) :
    Option (Extension context) := by
  cases context with
  | @pack E _ _ _ _ _ _ _ _ _ _ sign clean codec binding chain =>
    dsimp only [Context.Value, Context.sign, Context.signature,
      instZeroValue, instDecidableEqValue, instOneValue, instAddValue,
      instSubValue, instMulValue, instNatCastValue] at descriptor
    exact (chain.adjoin? descriptor).map fun child =>
      let handle : Context registry := .pack child.2
      ⟨handle, Algebraic.Element.ofCoeff,
        Algebraic.Element.ofPoly (DensePoly.ofCoeffs #[0, 1])⟩

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Chain.codec_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Chain.codec_lawful
