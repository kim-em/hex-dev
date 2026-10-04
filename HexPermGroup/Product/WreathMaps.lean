/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Wreath

public section

namespace Hex.PermGroup.WreathProduct

variable {G : Group n} {H : Group m}

@[expose] def pair (f : Fin m → Element G) (h : Element H) : Element (G.wreathProduct H) :=
  ⟨Perm.Wreath.perm (fun j => (f j).val) h.val,
    G.wreath_perm_mem H _ _ (fun j => (f j).property) h.property⟩

theorem factors (r : Element (G.wreathProduct H)) :
    ∃ (f : Fin m → Perm n) (h : Perm m), r.val = Perm.Wreath.perm f h := by
  obtain ⟨f, h, _, _, he⟩ := (G.mem_wreathProduct H r.val).mp r.property
  exact ⟨f, h, he⟩

@[expose] def top (r : Element (G.wreathProduct H)) : Element H :=
  ⟨Perm.Wreath.top r.val (factors r), by
    by_cases hn : 0 < n
    · obtain ⟨f, h, _, hh, he⟩ := (G.mem_wreathProduct H r.val).mp r.property
      simpa only [he, Perm.Wreath.top_perm hn] using hh
    · rw [Perm.Wreath.top_of_not_pos r.val (factors r) hn]
      exact .id⟩

@[expose] def base (r : Element (G.wreathProduct H)) (j : Fin m) : Element G :=
  ⟨Perm.Wreath.base r.val (factors r) j, by
    obtain ⟨f, h, hf, _, he⟩ := (G.mem_wreathProduct H r.val).mp r.property
    simpa only [he, Perm.Wreath.base_perm] using hf j⟩

/-- Empty blocks have no points, so the top projection is trivial. -/
theorem top_of_not_pos (hn : ¬0 < n) (r : Element (G.wreathProduct H)) : top r = Element.id H :=
  Subtype.ext (Perm.Wreath.top_of_not_pos r.val (factors r) hn)

@[simp] theorem top_pair (hn : 0 < n) (f : Fin m → Element G) (h : Element H) : top (pair f h) = h := by
  apply Subtype.ext
  exact Perm.Wreath.top_perm hn (fun j => (f j).val) h.val (factors (pair f h))

@[simp] theorem base_pair (f : Fin m → Element G) (h : Element H) (j : Fin m) :
    base (pair f h) j = f j := Subtype.ext (Perm.Wreath.base_perm ..)

@[simp] theorem pair_factors (r : Element (G.wreathProduct H)) :
    pair (base r) (top r) = r := Subtype.ext (Perm.Wreath.reconstruct ..)

theorem pair_injective (hn : 0 < n) {f g : Fin m → Element G} {h k : Element H}
    (he : pair f h = pair g k) : f = g ∧ h = k := by
  refine ⟨?_, ?_⟩
  · funext j
    simpa only [base_pair] using congrArg (fun r => base r j) he
  · simpa only [top_pair hn] using congrArg top he

@[simp] theorem pair_id :
    pair (G := G) (H := H) (fun _ => Element.id G) (Element.id H) = Element.id (G.wreathProduct H) :=
  Subtype.ext Perm.Wreath.perm_id

theorem pair_comp (f g : Fin m → Element G) (h k : Element H) :
    (pair f h).comp (pair g k) =
      pair (fun j => (f j).comp (g (h.val.inv.get j))) (h.comp k) :=
  Subtype.ext (Perm.Wreath.perm_comp ..)

theorem top_comp (r s : Element (G.wreathProduct H)) :
    top (r.comp s) = (top r).comp (top s) := by
  by_cases hn : 0 < n
  · have he := congrArg top (pair_comp (base r) (base s) (top r) (top s))
    simpa only [pair_factors, top_pair hn] using he
  · simp only [top_of_not_pos hn, Element.id_comp]

theorem base_comp (r s : Element (G.wreathProduct H)) (j : Fin m) :
    base (r.comp s) j = (base r j).comp (base s ((top r).val.inv.get j)) := by
  have he := congrArg (fun p => base p j) (pair_comp (base r) (base s) (top r) (top s))
  simpa only [pair_factors, base_pair] using he

@[expose] def inl (H : Group m) (f : Fin m → Element G) : Element (G.wreathProduct H) :=
  pair f (Element.id H)

@[expose] def inr (G : Group n) (h : Element H) : Element (G.wreathProduct H) :=
  pair (fun _ => Element.id G) h

@[expose] def copy (H : Group m) (i : Fin m) (p : Element G) : Element (G.wreathProduct H) :=
  inl H (fun j => if j = i then p else Element.id G)

theorem inl_injective {f g : Fin m → Element G} (he : inl H f = inl H g) : f = g := by
  funext j
  simpa only [inl, base_pair] using congrArg (fun r => base r j) he

theorem inr_injective (hn : 0 < n) {h k : Element H} (he : inr G h = inr G k) : h = k :=
  (pair_injective hn he).2

theorem copy_injective (i : Fin m) {p q : Element G} (he : copy H i p = copy H i q) : p = q := by
  have hh := congrFun (inl_injective he) i
  simpa using hh

@[simp] theorem top_inl (f : Fin m → Element G) : top (inl H f) = Element.id H := by
  by_cases hn : 0 < n
  · exact top_pair hn ..
  · exact top_of_not_pos hn _

@[simp] theorem top_inr (hn : 0 < n) (h : Element H) : top (inr G h) = h := top_pair hn ..

/-- The kernel of the top projection is exactly the embedded base group. -/
theorem top_eq_id (r : Element (G.wreathProduct H)) :
    top r = Element.id H ↔ ∃ f, inl H f = r := by
  constructor
  · intro h
    exact ⟨base r, by simpa only [inl, h] using pair_factors r⟩
  · rintro ⟨f, rfl⟩
    exact top_inl f

theorem inl_comp (f g : Fin m → Element G) :
    (inl H f).comp (inl H g) = inl H (fun j => (f j).comp (g j)) := by
  simp [inl, pair_comp]

theorem inr_comp (h k : Element H) : (inr G h).comp (inr G k) = inr G (h.comp k) := by
  simp [inr, pair_comp]

theorem inr_inv (h : Element H) : (inr G h).inv = inr G h.inv :=
  Subtype.ext (Perm.Wreath.lift_inv h.val).symm

theorem copy_comp (i : Fin m) (p q : Element G) :
    (copy H i p).comp (copy H i q) = copy H i (p.comp q) := by
  rw [copy, copy, inl_comp, copy]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

/-- Conjugation by a top element permutes the base factors by its action on
blocks. This is the semidirect-product action. -/
theorem conjugate_base (h : Element H) (f : Fin m → Element G) :
    (inr G h).comp ((inl H f).comp (inr G h).inv) =
      inl H (fun j => f (h.val.inv.get j)) := by
  rw [inr_inv]
  simp [inl, inr, pair_comp]

theorem conjugate_copy (h : Element H) (i : Fin m) (p : Element G) :
    (inr G h).comp ((copy H i p).comp (inr G h).inv) = copy H (h.val.get i) p := by
  rw [copy, conjugate_base, copy]
  congr 1
  funext j
  have he : h.val.inv.get j = i ↔ j = h.val.get i := by
    constructor
    · intro hh
      simpa using congrArg h.val.get hh
    · intro hh
      simp [hh]
  simp [he]

theorem decomposition (r : Element (G.wreathProduct H)) :
    (inl H (base r)).comp (inr G (top r)) = r := by
  have he : (inl H (base r)).comp (inr G (top r)) = pair (base r) (top r) := by
    simp [inl, inr, pair_comp]
  exact he.trans (pair_factors r)

end Hex.PermGroup.WreathProduct
