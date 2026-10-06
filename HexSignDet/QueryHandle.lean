/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.SelectedSigns

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]

/-- A prepared query domain belonging to one exact validated descriptor.
The descriptor parameter binds its context, polynomial, interval, derivative
slots and signs. The preparation equation binds the sign operation as well.
All proof fields are erased; no companion interpretation is executed. -/
structure QueryHandle {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) where
  private mk ::
  domain : Sturm.PreparedDomain E
  prepared : Sturm.prepare sign d.raw.head d.raw.lower d.raw.upper = some domain

/-- Restore the same canonical prepared domain from its original preparation
proof. The descriptor and every domain field remain exactly bound. -/
def QueryHandle.ofChecked {sign : E → Int} {context : Ctx}
    (descriptor : Descriptor E Ctx sign context) (domain : Sturm.PreparedDomain E)
    (prepared : Sturm.prepare sign descriptor.raw.head descriptor.raw.lower descriptor.raw.upper =
      some domain) : QueryHandle descriptor :=
  ⟨domain, prepared⟩

/-- Restoring a handle preserves its literal prepared domain. -/
theorem QueryHandle.ofChecked_domain {sign : E → Int} {context : Ctx}
    (descriptor : Descriptor E Ctx sign context) (domain : Sturm.PreparedDomain E)
    (prepared : Sturm.prepare sign descriptor.raw.head descriptor.raw.lower descriptor.raw.upper =
      some domain) : (ofChecked descriptor domain prepared).domain = domain := by
  unfold ofChecked
  rfl

/-- Reassembling a checked handle preserves its complete value. -/
theorem QueryHandle.ofChecked_eq {sign : E → Int} {context : Ctx}
    {descriptor : Descriptor E Ctx sign context} (handle : QueryHandle descriptor) :
    ofChecked descriptor handle.domain handle.prepared = handle := by
  unfold ofChecked
  cases handle
  rfl

/-- Changing only an equal descriptor index preserves the literal handle. -/
theorem QueryHandle.ofChecked_heq {sign : E → Int} {context : Ctx}
    (descriptor other : Descriptor E Ctx sign context) (same : other = descriptor)
    (domain : Sturm.PreparedDomain E)
    (prepared : Sturm.prepare sign descriptor.raw.head descriptor.raw.lower descriptor.raw.upper =
      some domain)
    (otherPrepared : Sturm.prepare sign other.raw.head other.raw.lower other.raw.upper =
      some domain) :
    HEq (ofChecked other domain otherPrepared) (ofChecked descriptor domain prepared) := by
  cases same
  rfl

/-- Prepare once for successive singleton or joint queries at this root.
Arbitrary coefficient operations may fail preparation; the companion proves
success for validated descriptors under the lawful interpretation. -/
def Descriptor.prepareQueries {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) : Option (QueryHandle d) :=
  match hd : Sturm.prepare sign d.raw.head d.raw.lower d.raw.upper with
  | none => none
  | some domain => some ⟨domain, hd⟩

/-- Exact preparation evidence retains the same canonical handle value. -/
theorem Descriptor.prepareQueries_eq {sign : E → Int} {context : Ctx}
    (descriptor : Descriptor E Ctx sign context) (domain : Sturm.PreparedDomain E)
    (prepared : Sturm.prepare sign descriptor.raw.head descriptor.raw.lower descriptor.raw.upper =
      some domain) :
    descriptor.prepareQueries = some (QueryHandle.ofChecked descriptor domain prepared) := by
  unfold Descriptor.prepareQueries QueryHandle.ofChecked
  split
  · rename_i failed
    rw [prepared] at failed
    contradiction
  · rename_i other same
    have equal : other = domain := Option.some.inj (same.symm.trans prepared)
    subst other
    rfl

/-- Mapping handles across an equal descriptor index preserves the optional
cache when each mapped handle preserves its value. This is only a proof about
already stored data. -/
theorem QueryHandle.map_heq {sign : E → Int} {context : Ctx}
    (descriptor other : Descriptor E Ctx sign context) (same : other = descriptor)
    (f : QueryHandle descriptor → QueryHandle other)
    (preserves : ∀ handle, HEq (f handle) handle)
    (cached : Option (QueryHandle descriptor)) : HEq (cached.map f) cached := by
  cases same
  have identity : f = id := funext fun handle => eq_of_heq (preserves handle)
  rw [identity, Option.map_id]
  rfl

/-- Equal descriptor indices give equal canonical preparation results. -/
theorem Descriptor.prepareQueries_heq {sign : E → Int} {context : Ctx}
    (descriptor other : Descriptor E Ctx sign context) (same : other = descriptor) :
    HEq other.prepareQueries descriptor.prepareQueries := by
  cases same
  rfl

/-- The cached domain has the original operation, head and endpoints. -/
theorem QueryHandle.bindings {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) :
    h.domain.sign = sign ∧ h.domain.head = d.raw.head ∧
      h.domain.lower = d.raw.lower ∧ h.domain.upper = d.raw.upper :=
  Sturm.prepare_eq_some sign d.raw.head d.raw.lower d.raw.upper h.domain h.prepared

/-- Build the same joint selected-sign evidence while retaining the prepared
squarefree chain. The joint BKR table and independent replay still run per
query list; this is domain reuse, not a cache of answers. -/
def QueryHandle.buildSigns {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d)
    (qs : List (DensePoly E)) : Except BuildError (SelectedSigns d qs) :=
  d.buildSignsPrepared h.domain qs

/-- Prepared and ordinary queries use exactly the same actual producer. -/
theorem QueryHandle.buildSigns_eq {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (qs : List (DensePoly E)) :
    h.buildSigns qs = d.buildSigns qs := by
  exact (d.buildSigns_prepared h.domain h.prepared qs).symm

/-- Replay remains bound to the handle's original descriptor. Supplied
evidence is checked by the ordinary literal selected-sign checker. -/
def QueryHandle.checkSigns {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} (_h : QueryHandle d)
    (qs : List (DensePoly E)) (values : Vector Int qs.length) (t : Replay E Ctx) : Bool :=
  d.checkSigns qs values t

/-- Total singleton sign with the same explicitly diagnostic zero fallback
as `Descriptor.signAt`. The companion excludes failure under lawful
coefficients using only the shared proved root-sum theorem. -/
@[expose] def QueryHandle.signAt {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (q : DensePoly E) : Int :=
  match h.buildSigns [q] with
  | .ok s => s.value
  | .error err => panic! s!"QueryHandle.signAt: internal error {repr err}"

/-- Reusing preparation preserves the ordinary singleton result. -/
theorem QueryHandle.signAt_eq {sign : E → Int} {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (q : DensePoly E) :
    h.signAt q = d.signAt q := by
  cases hs : d.buildSigns [q] <;>
    simp [QueryHandle.signAt, h.buildSigns_eq, Descriptor.signAt, hs]

/-- Any actual successful query proves preparation succeeds. This finite
implication supplies the companion's handle-construction guarantee. -/
theorem Descriptor.prepareQueries_ofBuild {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) {qs : List (DensePoly E)}
    (s : SelectedSigns d qs) (hs : d.buildSigns qs = .ok s) :
    ∃ h, d.prepareQueries = some h := by
  obtain ⟨domain, hd⟩ := d.buildSigns_domain s hs
  refine ⟨⟨domain, hd⟩, ?_⟩
  unfold Descriptor.prepareQueries
  split
  · rename_i hn
    simp only [hd, reduceCtorEq] at hn
  · rename_i other hother
    have he : other = domain := Option.some.inj (hother.symm.trans hd)
    subst other
    rfl

end Hex.SignDet
