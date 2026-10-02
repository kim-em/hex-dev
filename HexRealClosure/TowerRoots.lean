/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.CompleteRoots
public import HexRealClosure.TowerPolynomial

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A root represented in its immutable native context. A selected root retains
the actual child returned by adjoining its descriptor; its predecessor stays
valid and enters that child through the explicit embedding. -/
inductive Root (parent : Context registry) : Type 1 where
  | point (value : parent.Value)
  | selected
      (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
      (extension : Extension parent descriptor)
      (built : extension = parent.adjoin descriptor)

/-- The coefficient point or descriptor used to find this native root. -/
@[expose] def Root.selection {parent : Context registry} :
    Root parent → Isolation.Root parent.sign parent.signature
  | .point value => .point value
  | .selected descriptor _ _ => .selected descriptor

/-- Materialize one root, caching its actual extension and selected generator. -/
@[expose] def Root.ofSelection (parent : Context registry) :
    Isolation.Root parent.sign parent.signature → Root parent
  | .point value => .point value
  | .selected descriptor => .selected descriptor (parent.adjoin descriptor) rfl

theorem Root.selection_ofSelection (parent : Context registry)
    (root : Isolation.Root parent.sign parent.signature) :
    (Root.ofSelection parent root).selection = root := by cases root <;> rfl

/-- The context that owns the represented root value. -/
@[expose] def Root.context {parent : Context registry} : Root parent → Context registry
  | .point _ => parent
  | .selected _ extension _ => extension.context

/-- The root's native value, owned by its root context. -/
@[expose] def Root.value {parent : Context registry} (root : Root parent) : root.context.Value :=
  match root with
  | .point value => value
  | .selected _ extension _ => extension.generator

/-- Enter the root's context through the actual predecessor embedding. -/
@[expose] def Root.embed {parent : Context registry} (root : Root parent) :
    parent.Value → root.context.Value :=
  match root with
  | .point _ => id
  | .selected _ extension _ => extension.embed

/-- Embed every coefficient into the context owning this root. -/
@[expose] def Root.embedPoly {parent : Context registry} (root : Root parent)
    (p : DensePoly parent.Value) : DensePoly root.context.Value :=
  DensePoly.ofCoeffs (p.toArray.map root.embed)

/-- Polynomial sign at the native root, using ordinary arithmetic in its
actual extension context. -/
@[expose] def Root.signAt {parent : Context registry} (root : Root parent)
    (p : DensePoly parent.Value) : Int :=
  root.context.sign ((root.embedPoly p).eval root.value)

/-- The diagnostic root comparison through compatible descriptors over the
shared input context. Values in different child contexts retain ownership. -/
@[expose] def Root.compare? {parent : Context registry} (a b : Root parent) :
    Except SignDet.BuildError Ordering := a.selection.compare b.selection

/-- Ordinary total comparison of native roots. The companion excludes the
internal diagnostic fallback under the coefficient model laws. -/
@[expose] def Root.compare {parent : Context registry} (a b : Root parent) : Ordering :=
  match a.compare? b with
  | .ok order => order
  | .error error =>
    letI : Inhabited Ordering := ⟨.eq⟩
    panic! s!"Tower.Root.compare: internal error {repr error}"

/-- A native root and its positive multiplicity in the original polynomial. -/
structure RootEntry (parent : Context registry) where
  root : Root parent
  multiplicity : Nat
  positive : 0 < multiplicity

/-- Materialize the original root and retain its exact multiplicity. -/
@[expose] def RootEntry.ofEntry (parent : Context registry)
    (entry : Roots.Entry parent.sign parent.signature) : RootEntry parent :=
  ⟨Root.ofSelection parent entry.root, entry.multiplicity, entry.positive⟩

/-- Complete native roots, retaining the universal set of roots for zero.
Finite entries are strictly increasing under their common ambient interpretation. -/
inductive RootSet (parent : Context registry) : Type 1 where
  | all
  | finite (entries : List (RootEntry parent))

/-- Materialize a complete root result without changing its order or labels. -/
@[expose] def RootSet.ofOutput (parent : Context registry) :
    Roots.Output parent.sign parent.signature → RootSet parent
  | .all => .all
  | .finite entries => .finite (entries.map (RootEntry.ofEntry parent))

/-- Complete roots over a native tower. Each entry carries its actual extension
context, native root value and explicit embedding of the input coefficients. -/
@[expose] def Context.roots (parent : Context registry) (p : DensePoly parent.Value) :
    RootSet parent :=
  RootSet.ofOutput parent (Roots.roots parent.sign parent.signature p)

/-- A finite native result is the materialization of the actual generic output. -/
theorem Context.roots_finite {parent : Context registry} (p : DensePoly parent.Value)
    {out : List (RootEntry parent)} (returned : parent.roots p = .finite out) :
    ∃ entries, Roots.roots parent.sign parent.signature p = .finite entries ∧
      out = entries.map (RootEntry.ofEntry parent) := by
  cases produced : Roots.roots parent.sign parent.signature p with
  | all => simp [Context.roots, RootSet.ofOutput, produced] at returned
  | finite entries =>
    exact ⟨entries, rfl, by simpa [Context.roots, RootSet.ofOutput, produced] using returned.symm⟩

end Hex.RealClosure.Tower
