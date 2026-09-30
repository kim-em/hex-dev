/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.AlgebraicCodec
public import HexRealClosure.BaseJson
public import HexRealClosure.BaseCatalog
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

attribute [-instance] instDecidableEqSignature

/-- Exact equality, with core's sound pointer shortcut for the immutable
signature shared by every node in one query. -/
instance (priority := high) : DecidableEq Signature := fun a b =>
  withPtrEqDecEq a b (fun _ => instDecidableEqSignature a b)

@[expose] def Signature.literal (signature : Signature) : Literal :=
  .array (.cons (.array (Literals.ofList (signature.base.constants.map fun key =>
    .array (.cons (.string key.name) (.cons (.number key.version 0) .nil)))))
    (.cons (.number signature.base.infinitesimals 0)
      (.cons (.array (Literals.ofList signature.roots)) .nil)))

@[expose] def Signature.extend (signature : Signature) (frame : Literal) : Signature :=
  { signature with roots := signature.roots ++ [frame] }

private def readKeys : Literals → Option (List BaseContext.ConstantKey)
  | .nil => some []
  | .cons (.array (.cons (.string name) (.cons (.number version 0) .nil))) xs =>
    if 0 ≤ version then (fun keys => ⟨name, version.toNat⟩ :: keys) <$> readKeys xs
    else none
  | _ => none

/-- Read the full structured identity. Reading an identity supplies no root
validation; the catalog must still find its validated native prefix. -/
def Signature.ofLiteral : Literal → Option Signature
  | .array (.cons (.array keys) (.cons (.number count 0) (.cons (.array roots) .nil))) =>
    if 0 ≤ count then (fun constants => ⟨⟨constants, count.toNat⟩, roots.toList⟩) <$>
      readKeys keys else none
  | _ => none

private theorem readKeys_write (keys : List BaseContext.ConstantKey) :
    readKeys (Literals.ofList (keys.map fun key =>
      Literal.array (.cons (.string key.name) (.cons (.number key.version 0) .nil)))) =
      some keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih => cases key; simp [Literals.ofList, readKeys, ih]

theorem Signature.ofLiteral_literal (signature : Signature) :
    Signature.ofLiteral signature.literal = some signature := by
  cases signature with
  | mk base roots =>
    cases base
    simp [Signature.literal, Signature.ofLiteral, readKeys_write, Literals.toList_ofList]

private def require {A : Type} (message : String) : Option A → Except String A
  | none => .error message
  | some a => .ok a

/-- A structured signature codec; validation remains the catalog's task. -/
def Signature.codec : ValueCodec Signature where
  encode signature := signature.literal.toJson
  decode j := match Literal.ofJson j with
    | none => .error "unsupported signature literal"
    | some literal => require "invalid full signature" (Signature.ofLiteral literal)

theorem Signature.codec_lawful : Signature.codec.Lawful := by
  intro signature
  simp [Signature.codec, Literal.ofJson_toJson, Signature.ofLiteral_literal, require]

/-- A node's reference to the exact enclosing predecessor is encoded once by
that enclosing signature. Other literal contexts are retained in full. This
avoids copying the entire predecessor into every node of its replay graph. -/
def contextCodec (parent : Signature) : ValueCodec Signature where
  encode context := if context = parent then .arr #[.num ⟨0, 0⟩]
    else .arr #[.num ⟨1, 0⟩, context.literal.toJson]
  decode j := match Literal.ofJson j with
    | some (.array (.cons (.number 0 0) .nil)) => .ok parent
    | some (.array (.cons (.number 1 0) (.cons literal .nil))) =>
      match Signature.ofLiteral literal with
      | none => .error "invalid context reference"
      | some context =>
        if context = parent then .error "noncanonical context reference" else .ok context
    | _ => .error "invalid relative context reference"

theorem contextCodec_lawful (parent : Signature) : (contextCodec parent).Lawful := by
  intro context
  by_cases h : context = parent
  · subst context; simp [contextCodec, Literal.ofJson, Literals.ofList, require]
  · simp [contextCodec, h, Literal.ofJson, Literals.ofList,
      Literal.ofJson_toJson, Signature.ofLiteral_literal, require]

section

variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {binding : Signature}

/-- Serialize the actual finite replay graph, with sharing determined by exact
node equality. Hashing only indexes that equality search. The descriptor's
head, bounds and ordered Thom slots are retained separately from the replay. -/
@[expose] def rootData (value : ValueCodec E) (root : Descriptor E Signature sign binding) : Json :=
  letI : Hashable E := ⟨fun a => match Literal.ofJson (value.encode a) with
    | some literal => hash literal
    | none => 0⟩
  -- Accepted nodes have one predecessor; hashing it adds no discrimination.
  -- Exact node equality still checks every context, including malformed data.
  letI : Hashable Signature := ⟨fun _ => 0⟩
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

omit [Neg E] [Inv E] [Div E] in
/-- The checked frame retains the entire structured descriptor and replay. -/
theorem Chain.frame_data (descriptor : Descriptor E Signature sign binding) (frame : Literal)
    (h : Literal.ofJson (rootData codec descriptor) = some frame) :
    frame.toJson = rootData codec descriptor := Literal.toJson_ofJson _ _ h

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

@[expose, reducible] def Context.signature (context : Context registry) : Signature := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ _ _ _ binding => exact binding

@[expose, reducible] def Context.sign (context : Context registry) : context.Value → Int := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ sign => exact sign

@[expose, reducible] def Context.isClean (context : Context registry) : context.Value → Bool := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ _ clean => exact clean

@[expose, reducible] def Context.codec (context : Context registry) : ValueCodec context.Value := by
  cases context with
  | @pack _ _ _ _ _ _ _ _ _ _ _ _ _ codec => exact codec

theorem Context.codec_lawful (context : Context registry) : context.codec.Lawful := by
  cases context with
  | pack chain => exact chain.codec_lawful

/-- No real or infinitesimal extension can be added after this base is packed.
Those stages are assembled through the native base-context constructors. -/
@[expose] def Context.base {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
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
structure Extension (parent : Context registry)
    (descriptor : Descriptor parent.Value Signature parent.sign parent.signature) : Type 1 where
  private mk ::
  frame : Literal
  encoded : Literal.ofJson (rootData parent.codec descriptor) = some frame
  context : Context registry
  binding : context.signature = parent.signature.extend frame
  embed : parent.Value → context.Value
  generator : context.Value
  pack : DensePoly parent.Value → context.Value

/-- The descriptor uses this context's exact value type, sign and signature.
The returned embedding is the actual constant-polynomial packing operation. -/
def Context.adjoin? (context : Context registry)
    (descriptor : Descriptor context.Value Signature context.sign context.signature) :
    Option (Extension context descriptor) := by
  cases context with
  | @pack E _ _ _ _ _ _ _ _ _ _ sign clean codec binding chain =>
    dsimp only [Context.Value, Context.sign, Context.signature,
      instZeroValue, instDecidableEqValue, instOneValue, instAddValue,
      instSubValue, instMulValue, instNatCastValue] at descriptor
    exact match he : Literal.ofJson (rootData codec descriptor) with
      | none => none
      | some frame =>
        let native := Algebraic.Context.adjoin descriptor clean
        let handle : Context registry := .pack (.root chain descriptor frame he)
        some ⟨frame, he, handle, rfl, Algebraic.Element.ofCoeff (context := native),
          Algebraic.Element.ofPoly (context := native) (DensePoly.ofCoeffs #[0, 1]),
          Algebraic.Element.ofPoly (context := native)⟩

section
variable {E : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable {sign : E → Int} {clean : E → Bool} {codec : ValueCodec E} {binding : Signature}

private theorem Context.adjoin_spec_proof
    (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding)
    (extension : Extension (.pack chain) descriptor)
    (h : Context.adjoin? (.pack chain) descriptor = some extension) :
    extension.context = .pack (.root chain descriptor extension.frame extension.encoded) ∧
      HEq extension.embed (Algebraic.Element.ofCoeff
        (context := Algebraic.Context.adjoin descriptor clean)) ∧
      HEq extension.generator (Algebraic.Element.ofPoly
        (context := Algebraic.Context.adjoin descriptor clean) (DensePoly.ofCoeffs #[0, 1])) := by
  simp only [Context.adjoin?] at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- Characterize the returned native context and both maps without unfolding
its private constructor. Rewriting the context equation restores the concrete
value type for subsequent transport or interpretation proofs. -/
theorem Context.adjoin_spec (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding)
    (extension : Extension (.pack chain) descriptor)
    (h : Context.adjoin? (.pack chain) descriptor = some extension) :
    extension.context = .pack (.root chain descriptor extension.frame extension.encoded) ∧
      HEq extension.embed (Algebraic.Element.ofCoeff
        (context := Algebraic.Context.adjoin descriptor clean)) ∧
      HEq extension.generator (Algebraic.Element.ofPoly
        (context := Algebraic.Context.adjoin descriptor clean) (DensePoly.ofCoeffs #[0, 1])) :=
  Context.adjoin_spec_proof chain descriptor extension h

private theorem Context.pack_spec_proof (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding)
    (extension : Extension (.pack chain) descriptor)
    (h : Context.adjoin? (.pack chain) descriptor = some extension) :
    HEq extension.pack (Algebraic.Element.ofPoly
      (context := Algebraic.Context.adjoin descriptor clean)) := by
  simp only [Context.adjoin?] at h
  split at h
  · contradiction
  · cases h
    exact HEq.rfl

/-- The packing closure captures the actual native child context. -/
theorem Context.pack_spec (chain : Chain registry E sign clean codec binding)
    (descriptor : Descriptor E Signature sign binding)
    (extension : Extension (.pack chain) descriptor)
    (h : Context.adjoin? (.pack chain) descriptor = some extension) :
    HEq extension.pack (Algebraic.Element.ofPoly
      (context := Algebraic.Context.adjoin descriptor clean)) :=
  Context.pack_spec_proof chain descriptor extension h

end

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Chain.codec_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Chain.codec_lawful
