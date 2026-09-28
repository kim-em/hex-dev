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

/-- Prepare once for successive singleton or joint queries at this root.
Arbitrary coefficient operations may fail preparation; the companion proves
success for validated descriptors under the lawful interpretation. -/
def Descriptor.prepareQueries {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) : Option (QueryHandle d) :=
  match hd : Sturm.prepare sign d.raw.head d.raw.lower d.raw.upper with
  | none => none
  | some domain => some ⟨domain, hd⟩

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
coefficients using only the agreed #10389 root-sum bridge. -/
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
