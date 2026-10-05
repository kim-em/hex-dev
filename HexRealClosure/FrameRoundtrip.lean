/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFrame
public import HexRealClosure.TowerEnlarge
import all HexRealClosure.RootFrame

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- The canonical printed frames of the actual validated suffix, in
predecessor order. Each frame retains its original descriptor and replay. -/
@[expose] def Suffix.frames {source : Context registry} : Suffix source → List Literal
  | .nil => []
  | .root descriptor rest => (source.adjoin descriptor).frame :: rest.frames

/-- Canonical printing retains the complete ordered context identity. -/
theorem Suffix.signature_frames {source : Context registry} (suffix : Suffix source) :
    suffix.context.signature = source.signature.append suffix.frames := by
  induction suffix with
  | @nil source => exact (Signature.append_nil source.signature).symm
  | @root source descriptor rest ih =>
    rw [Suffix.context, ih, (source.adjoin descriptor).binding, Signature.append_cons]
    rfl

/-- A suffix over an actual packed base prints precisely that base binding
and its own ordered canonical frames. -/
theorem Suffix.signature_base (base : BaseContext.PackedContext registry)
    (suffix : Suffix (Context.ofBase base)) :
    suffix.context.signature = ⟨base.signature, suffix.frames⟩ := by
  rw [suffix.signature_frames, Context.ofBase_signature]
  rfl

/-- A catalog with no installed algebraic levels reconstructs every canonical
suffix using its actual descriptor frames. The predecessor may itself have
roots; every missing child is checked by the shared replay reader. -/
theorem Catalog.readFrames_suffix (base : BaseContext.Catalog registry)
    {source : Context registry} (suffix : Suffix source) :
    ∃ result, (Catalog.ofBase base).readFrames source suffix.frames = .ok result ∧
      result.val = suffix.context := by
  induction suffix with
  | @nil source =>
    exact ⟨⟨source, (Signature.append_nil source.signature).symm⟩, rfl, rfl⟩
  | @root source descriptor rest ih =>
    change ∃ result, (Catalog.ofBase base).readFrames source
      ((source.adjoin descriptor).frame :: rest.frames) = .ok result ∧ result.val = rest.context
    obtain ⟨root, read, context⟩ := source.readFrame_context descriptor
    have missing := Catalog.lookup_ofBase base
      (source.signature.extend (source.adjoin descriptor).frame) (by simp [Signature.extend])
    have recursion : ∃ result,
        (Catalog.ofBase base).readFrames root.extension.context rest.frames = .ok result ∧
          result.val = rest.context := by
      rw [context]
      exact ih
    obtain ⟨next, checked, finish⟩ := recursion
    refine ⟨⟨next.val, ?_⟩, ?_, finish⟩
    · change next.val.signature = source.signature.append
        ((source.adjoin descriptor).frame :: rest.frames)
      rw [next.property, root.binding, Signature.append_cons]
    · change (Catalog.ofBase base).readFrames source
        ((source.adjoin descriptor).frame :: rest.frames) = _
      rw [Catalog.readFrames]
      split
      · rename_i message failed
        split at failed
        · rename_i found installed
          rw [missing] at installed
          cases installed
        · rw [read] at failed
          cases failed
      · rename_i child accepted
        split at accepted
        · rename_i found installed
          rw [missing] at installed
          cases installed
        · rw [read] at accepted
          cases accepted
          simp only [checked]

/-- Reconstruct every freshly printed tower over an available validated
base, without installing any of its algebraic prefixes. The base retains the
provider progress proofs needed for replay; no reader-success premise is
assumed for any root frame or the whole tower. -/
theorem Catalog.reconstruct_suffix (catalog : BaseContext.Catalog registry)
    (base : BaseContext.PackedContext registry)
    (available : catalog.read base.signature = some base)
    (suffix : Suffix (Context.ofBase base)) :
    ∃ result, (Catalog.ofBase catalog).reconstruct suffix.context.signature = .ok result ∧
      result.val = suffix.context := by
  cases suffix with
  | nil =>
    have known := Catalog.lookup_base catalog base available
    exact ⟨_, Catalog.reconstruct_lookup (Catalog.ofBase catalog)
      (Context.ofBase base).signature (Context.ofBase base) known, rfl⟩
  | root descriptor rest =>
    have binding := (Suffix.root descriptor rest).signature_base base
    rw [binding]
    change ∃ result, (Catalog.ofBase catalog).reconstruct
      ⟨base.signature, ((Context.ofBase base).adjoin descriptor).frame :: rest.frames⟩ = .ok result ∧
        result.val = rest.context
    have recursion := Catalog.readFrames_suffix catalog (Suffix.root descriptor rest)
    change ∃ result, (Catalog.ofBase catalog).readFrames (Context.ofBase base)
      (((Context.ofBase base).adjoin descriptor).frame :: rest.frames) = .ok result ∧
        result.val = rest.context at recursion
    obtain ⟨next, read, finish⟩ := recursion
    have missing := Catalog.lookup_ofBase catalog
      ⟨base.signature, ((Context.ofBase base).adjoin descriptor).frame :: rest.frames⟩ (by simp)
    have known : (Catalog.ofBase catalog).lookup ⟨base.signature, []⟩ =
        some (Context.ofBase base) := by
      rw [← Context.ofBase_signature base]
      exact Catalog.lookup_base catalog base available
    refine ⟨⟨next.val, ?_⟩, ?_, finish⟩
    · rw [next.property, Context.ofBase_signature]
      rfl
    · unfold Catalog.reconstruct
      split
      · rename_i found installed
        rw [missing] at installed
        cases installed
      · split
        · rename_i unknown
          rw [known] at unknown
          cases unknown
        · rename_i found installed
          have same : found = Context.ofBase base := Option.some.inj (installed.symm.trans known)
          cases same
          simp only [read]

/-- Freshly printed values roundtrip through reconstruction of every missing
algebraic prefix, provided the original validated base is available. -/
theorem Catalog.restoreElement_suffix (catalog : BaseContext.Catalog registry)
    (base : BaseContext.PackedContext registry)
    (available : catalog.read base.signature = some base)
    (suffix : Suffix (Context.ofBase base)) (a : suffix.context.Value) :
    (Catalog.ofBase catalog).restoreElement (suffix.context.write a) =
      .ok ⟨suffix.context, a⟩ := by
  obtain ⟨⟨context, binding⟩, read, same⟩ := Catalog.reconstruct_suffix catalog base available suffix
  change context = suffix.context at same
  cases same
  simp [Catalog.restoreElement, Context.write, read, suffix.context.codec_lawful a]

/-- Fresh polynomial reconstruction preserves every original coefficient
and the exact original immutable owner, without installing its root suffix. -/
theorem Catalog.restorePolynomial_suffix (catalog : BaseContext.Catalog registry)
    (base : BaseContext.PackedContext registry)
    (available : catalog.read base.signature = some base)
    (suffix : Suffix (Context.ofBase base)) (p : suffix.context.Poly) :
    (Catalog.ofBase catalog).restorePolynomial (suffix.context.writePoly p) =
      .ok ⟨suffix.context, p⟩ := by
  obtain ⟨⟨context, binding⟩, read, same⟩ := Catalog.reconstruct_suffix catalog base available suffix
  change context = suffix.context at same
  cases same
  simp [Catalog.restorePolynomial, Context.writePoly, read,
    SignDet.Codec.read_poly suffix.context.codec suffix.context.codec_lawful p]

/-- Every actual native value has an exact fresh-catalog roundtrip when its
extracted validated base is available. The stored chain supplies the suffix. -/
theorem Catalog.restoreElement_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base)
    (a : context.Value) :
    (Catalog.ofBase catalog).restoreElement (context.write a) = .ok ⟨context, a⟩ := by
  cases origin : context.origin with
  | pack base suffix same =>
    have known : catalog.read (BaseContext.PackedContext.pack base).signature =
        some (BaseContext.PackedContext.pack base) := by
      rw [origin] at available
      exact available
    cases same
    exact Catalog.restoreElement_suffix catalog (.pack base) known suffix a

/-- Fresh reconstruction preserves every polynomial of any actual stored
tower, retaining its original native owner and all coefficient syntax. -/
theorem Catalog.restorePolynomial_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base)
    (p : context.Poly) :
    (Catalog.ofBase catalog).restorePolynomial (context.writePoly p) = .ok ⟨context, p⟩ := by
  cases origin : context.origin with
  | pack base suffix same =>
    have known : catalog.read (BaseContext.PackedContext.pack base).signature =
        some (BaseContext.PackedContext.pack base) := by
      rw [origin] at available
      exact available
    cases same
    exact Catalog.restorePolynomial_suffix catalog (.pack base) known suffix p

/-- Fresh reconstruction recovers an arbitrary original context from its
canonical root frames and an available validated provider base. -/
theorem Catalog.reconstruct_origin (catalog : BaseContext.Catalog registry)
    (context : Context registry)
    (available : catalog.read context.origin.base.signature = some context.origin.base) :
    ∃ result, (Catalog.ofBase catalog).reconstruct context.signature = .ok result ∧
      result.val = context := by
  cases origin : context.origin with
  | pack base suffix same =>
    have known : catalog.read (BaseContext.PackedContext.pack base).signature =
        some (BaseContext.PackedContext.pack base) := by
      rw [origin] at available
      exact available
    cases same
    exact Catalog.reconstruct_suffix catalog (.pack base) known suffix

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Suffix.signature_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Suffix.signature_frames

/-- info: 'Hex.RealClosure.Tower.Catalog.readFrames_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.readFrames_suffix

/-- info: 'Hex.RealClosure.Tower.Catalog.reconstruct_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.reconstruct_suffix

/-- info: 'Hex.RealClosure.Tower.Catalog.restoreElement_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restoreElement_origin

/-- info: 'Hex.RealClosure.Tower.Catalog.restorePolynomial_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Catalog.restorePolynomial_origin
