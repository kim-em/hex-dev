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

@[expose] def pair (hn : 0 < n) (f : Fin m → Element G) (h : Element H) : Element (G.wreathProduct H hn) :=
  ⟨Perm.Wreath.perm hn (fun j => (f j).val) h.val,
    G.wreath_perm_mem H hn _ _ (fun j => (f j).property) h.property⟩

theorem factors (hn : 0 < n) (r : Element (G.wreathProduct H hn)) :
    ∃ (f : Fin m → Perm n) (h : Perm m), r.val = Perm.Wreath.perm hn f h := by
  obtain ⟨f, h, _, _, he⟩ := (G.mem_wreathProduct H hn r.val).mp r.property
  exact ⟨f, h, he⟩

@[expose] def top (hn : 0 < n) (r : Element (G.wreathProduct H hn)) : Element H :=
  ⟨Perm.Wreath.top hn r.val (factors hn r), by
    obtain ⟨f, h, _, hh, he⟩ := (G.mem_wreathProduct H hn r.val).mp r.property
    simpa only [he, Perm.Wreath.top_perm] using hh⟩

@[expose] def base (hn : 0 < n) (r : Element (G.wreathProduct H hn)) (j : Fin m) : Element G :=
  ⟨Perm.Wreath.base hn r.val (factors hn r) j, by
    obtain ⟨f, h, hf, _, he⟩ := (G.mem_wreathProduct H hn r.val).mp r.property
    simpa only [he, Perm.Wreath.base_perm] using hf j⟩

@[simp] theorem top_pair (hn : 0 < n) (f : Fin m → Element G) (h : Element H) : top hn (pair hn f h) = h := by
  apply Subtype.ext
  exact Perm.Wreath.top_perm hn (fun j => (f j).val) h.val (factors hn (pair hn f h))

@[simp] theorem base_pair (hn : 0 < n) (f : Fin m → Element G) (h : Element H) (j : Fin m) :
    base hn (pair hn f h) j = f j := Subtype.ext (Perm.Wreath.base_perm ..)

@[simp] theorem pair_factors (hn : 0 < n) (r : Element (G.wreathProduct H hn)) :
    pair hn (base hn r) (top hn r) = r := Subtype.ext (Perm.Wreath.reconstruct ..)

theorem pair_injective (hn : 0 < n) {f g : Fin m → Element G} {h k : Element H}
    (he : pair hn f h = pair hn g k) : f = g ∧ h = k := by
  refine ⟨?_, ?_⟩
  · funext j
    simpa only [base_pair] using congrArg (fun r => base hn r j) he
  · simpa only [top_pair] using congrArg (top hn) he

@[simp] theorem pair_id (hn : 0 < n) :
    pair (G := G) (H := H) hn (fun _ => Element.id G) (Element.id H) = Element.id (G.wreathProduct H hn) :=
  Subtype.ext (Perm.Wreath.perm_id hn)

theorem pair_comp (hn : 0 < n) (f g : Fin m → Element G) (h k : Element H) :
    (pair hn f h).comp (pair hn g k) =
      pair hn (fun j => (f j).comp (g (h.val.inv.get j))) (h.comp k) :=
  Subtype.ext (Perm.Wreath.perm_comp ..)

theorem top_comp (hn : 0 < n) (r s : Element (G.wreathProduct H hn)) :
    top hn (r.comp s) = (top hn r).comp (top hn s) := by
  have he := congrArg (top hn) (pair_comp hn (base hn r) (base hn s) (top hn r) (top hn s))
  simpa only [pair_factors, top_pair] using he

theorem base_comp (hn : 0 < n) (r s : Element (G.wreathProduct H hn)) (j : Fin m) :
    base hn (r.comp s) j = (base hn r j).comp (base hn s ((top hn r).val.inv.get j)) := by
  have he := congrArg (fun p => base hn p j) (pair_comp hn (base hn r) (base hn s) (top hn r) (top hn s))
  simpa only [pair_factors, base_pair] using he

@[expose] def inl (H : Group m) (hn : 0 < n) (f : Fin m → Element G) : Element (G.wreathProduct H hn) :=
  pair hn f (Element.id H)

@[expose] def inr (G : Group n) (hn : 0 < n) (h : Element H) : Element (G.wreathProduct H hn) :=
  pair hn (fun _ => Element.id G) h

@[expose] def copy (H : Group m) (hn : 0 < n) (i : Fin m) (p : Element G) : Element (G.wreathProduct H hn) :=
  inl H hn (fun j => if j = i then p else Element.id G)

theorem inl_injective (hn : 0 < n) {f g : Fin m → Element G} (he : inl H hn f = inl H hn g) : f = g :=
  (pair_injective hn he).1

theorem inr_injective (hn : 0 < n) {h k : Element H} (he : inr G hn h = inr G hn k) : h = k :=
  (pair_injective hn he).2

theorem copy_injective (hn : 0 < n) (i : Fin m) {p q : Element G} (he : copy H hn i p = copy H hn i q) : p = q := by
  have hh := congrFun (inl_injective hn he) i
  simpa using hh

@[simp] theorem top_inl (hn : 0 < n) (f : Fin m → Element G) : top hn (inl H hn f) = Element.id H := top_pair ..
@[simp] theorem top_inr (hn : 0 < n) (h : Element H) : top hn (inr G hn h) = h := top_pair ..

/-- The kernel of the top projection is exactly the embedded base group. -/
theorem top_eq_id (hn : 0 < n) (r : Element (G.wreathProduct H hn)) :
    top hn r = Element.id H ↔ ∃ f, inl H hn f = r := by
  constructor
  · intro h
    exact ⟨base hn r, by simpa only [inl, h] using pair_factors hn r⟩
  · rintro ⟨f, rfl⟩
    exact top_inl hn f

theorem inl_comp (hn : 0 < n) (f g : Fin m → Element G) :
    (inl H hn f).comp (inl H hn g) = inl H hn (fun j => (f j).comp (g j)) := by
  simp [inl, pair_comp]

theorem inr_comp (hn : 0 < n) (h k : Element H) : (inr G hn h).comp (inr G hn k) = inr G hn (h.comp k) := by
  simp [inr, pair_comp]

theorem inr_inv (hn : 0 < n) (h : Element H) : (inr G hn h).inv = inr G hn h.inv :=
  Subtype.ext (Perm.Wreath.lift_inv hn h.val).symm

theorem copy_comp (hn : 0 < n) (i : Fin m) (p q : Element G) :
    (copy H hn i p).comp (copy H hn i q) = copy H hn i (p.comp q) := by
  rw [copy, copy, inl_comp, copy]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

/-- Conjugation by a top element permutes the base factors by its action on
blocks. This is the semidirect-product action. -/
theorem conjugate_base (hn : 0 < n) (h : Element H) (f : Fin m → Element G) :
    (inr G hn h).comp ((inl H hn f).comp (inr G hn h).inv) =
      inl H hn (fun j => f (h.val.inv.get j)) := by
  rw [inr_inv]
  simp [inl, inr, pair_comp]

theorem conjugate_copy (hn : 0 < n) (h : Element H) (i : Fin m) (p : Element G) :
    (inr G hn h).comp ((copy H hn i p).comp (inr G hn h).inv) = copy H hn (h.val.get i) p := by
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

theorem decomposition (hn : 0 < n) (r : Element (G.wreathProduct H hn)) :
    (inl H hn (base hn r)).comp (inr G hn (top hn r)) = r := by
  have he : (inl H hn (base hn r)).comp (inr G hn (top hn r)) = pair hn (base hn r) (top hn r) := by
    simp [inl, inr, pair_comp]
  exact he.trans (pair_factors hn r)

end Hex.PermGroup.WreathProduct
