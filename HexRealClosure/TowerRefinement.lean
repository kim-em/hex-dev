/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerPolynomial
public import HexSignDet.Reencode
public import HexRealRoots.Map

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} (parent : Context registry)
variable {source : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
variable {head : DensePoly parent.Value} {a b : Endpoint parent.Value}

/-- A checked persistent change of the final root over an unchanged predecessor.
The old context stays valid; the new context owns its own literal root frame. -/
structure Refinement (encoding : SignDet.Reencoding source head a b) : Type 1 where
  private mk ::
  extension : Extension parent encoding.target
  canonical : extension = parent.adjoin encoding.target
  transport : (parent.adjoin source).context.Value → extension.context.Value
  repacked : ∀ value, HEq (transport value)
    (parent.ofPoly encoding.target (parent.polynomial source value))

/-- Repack every old polynomial representative at the checked same root of
the new definition. No semantic law record is an executable argument. -/
def Context.refine (encoding : SignDet.Reencoding source head a b) :
    Refinement parent encoding :=
  let extension := parent.adjoin encoding.target
  let pack := extension.pack
  let polynomial := parent.polynomial source
  ⟨extension, rfl, fun value => pack (polynomial value), fun _ => HEq.rfl⟩

private theorem Context.refine_transport_proof
    (encoding : SignDet.Reencoding source head a b)
    (value : (parent.adjoin source).context.Value) :
    HEq ((parent.refine encoding).transport value)
      (parent.ofPoly encoding.target (parent.polynomial source value)) := HEq.rfl

/-- The native conversion repacks exactly the old stored polynomial. -/
theorem Context.refine_transport (encoding : SignDet.Reencoding source head a b)
    (value : (parent.adjoin source).context.Value) :
    HEq ((parent.refine encoding).transport value)
      (parent.ofPoly encoding.target (parent.polynomial source value)) :=
  Context.refine_transport_proof parent encoding value

variable {parent}
variable {encoding : SignDet.Reencoding source head a b}

/-- Transport every coefficient and normalize only trailing target zeros. -/
@[expose, reducible] def Refinement.mapPoly (refinement : Refinement parent encoding)
    (p : DensePoly (parent.adjoin source).context.Value) : DensePoly refinement.extension.context.Value :=
  DensePoly.ofCoeffs (p.toArray.map refinement.transport)

/-- Read the actual representative stored in the new native context. -/
@[expose] def Refinement.polynomial (refinement : Refinement parent encoding)
    (value : refinement.extension.context.Value) : DensePoly parent.Value :=
  parent.polynomial encoding.target
    (_root_.cast (congrArg Context.Value (congrArg Extension.context refinement.canonical)) value)

/-- Move a validated later descriptor's operands to the new predecessor.
Its selection slots stay fixed; its replay must be rebuilt in the new context. -/
@[expose] def Refinement.mapRaw (refinement : Refinement parent encoding)
    (descriptor : SignDet.Descriptor (parent.adjoin source).context.Value Signature
      (parent.adjoin source).context.sign (parent.adjoin source).context.signature) :
    SignDet.RawDescriptor refinement.extension.context.Value Signature :=
  (parent.adjoin source).context.mapDescriptor refinement.extension.context
    refinement.transport descriptor

/-- Revalidate the converted later selection with fresh context-bound evidence. -/
@[expose] def Refinement.mapDescriptor? (refinement : Refinement parent encoding)
    (descriptor : SignDet.Descriptor (parent.adjoin source).context.Value Signature
      (parent.adjoin source).context.sign (parent.adjoin source).context.signature) :
    Option (SignDet.Descriptor refinement.extension.context.Value Signature
      refinement.extension.context.sign refinement.extension.context.signature) :=
  SignDet.Descriptor.validate refinement.extension.context.sign
    refinement.extension.context.signature (refinement.mapRaw descriptor)

/-- One checked later-root conversion. Its private constructor binds the
selected descriptor, cached extension and actual transport together. -/
structure Later (refinement : Refinement parent encoding)
    (original : SignDet.Descriptor (parent.adjoin source).context.Value Signature
      (parent.adjoin source).context.sign (parent.adjoin source).context.signature) : Type 1 where
  private mk ::
  descriptor : SignDet.Descriptor refinement.extension.context.Value Signature
    refinement.extension.context.sign refinement.extension.context.signature
  checked : refinement.mapDescriptor? original = some descriptor
  extension : Extension refinement.extension.context descriptor
  canonical : extension = refinement.extension.context.adjoin descriptor
  transport : ((parent.adjoin source).context.adjoin original).context.Value → extension.context.Value
  repacked : ∀ value, HEq (transport value)
    (refinement.extension.context.ofPoly descriptor
      (refinement.mapPoly ((parent.adjoin source).context.polynomial original value)))

/-- Revalidate and prepare a later conversion once. Every transported value
then uses the captured old predecessor and new packing closure. -/
def Refinement.later? (refinement : Refinement parent encoding)
    (descriptor : SignDet.Descriptor (parent.adjoin source).context.Value Signature
      (parent.adjoin source).context.sign (parent.adjoin source).context.signature) :
    Option (Later refinement descriptor) :=
  match h : refinement.mapDescriptor? descriptor with
  | none => none
  | some converted =>
    let old := parent.adjoin source
    let extension := refinement.extension.context.adjoin converted
    let pack := extension.pack
    let polynomial := old.context.polynomial descriptor
    some ⟨converted, h, extension, rfl,
      fun value => pack (refinement.mapPoly (polynomial value)), fun _ => HEq.rfl⟩

private theorem Refinement.later_exists_proof (refinement : Refinement parent encoding)
    (descriptor : SignDet.Descriptor (parent.adjoin source).context.Value Signature
      (parent.adjoin source).context.sign (parent.adjoin source).context.signature)
    (h : ∃ converted, refinement.mapDescriptor? descriptor = some converted) :
    ∃ later, refinement.later? descriptor = some later := by
  obtain ⟨converted, h⟩ := h
  unfold Refinement.later?
  split
  · rename_i he
    have hn := he.symm.trans h
    cases hn
  · exact ⟨_, rfl⟩

/-- Preparing the bundle succeeds whenever its descriptor revalidation does. -/
theorem Refinement.later_exists (refinement : Refinement parent encoding)
    (descriptor : SignDet.Descriptor (parent.adjoin source).context.Value Signature
      (parent.adjoin source).context.sign (parent.adjoin source).context.signature)
    (h : ∃ converted, refinement.mapDescriptor? descriptor = some converted) :
    ∃ later, refinement.later? descriptor = some later :=
  Refinement.later_exists_proof refinement descriptor h

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.refine
