/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Direct

public section

namespace Hex.PermGroup.DirectProduct

variable {G : Group n} {H : Group m}

@[expose] def inl (H : Group m) (p : Element G) : Element (G.directProduct H) := pair p (Element.id H)
@[expose] def inr (G : Group n) (q : Element H) : Element (G.directProduct H) := pair (Element.id G) q

@[simp] theorem fst_inl (p : Element G) : fst (inl H p) = p := fst_pair ..
@[simp] theorem snd_inl (p : Element G) : snd (inl H p) = Element.id H := snd_pair ..
@[simp] theorem fst_inr (q : Element H) : fst (inr G q) = Element.id G := fst_pair ..
@[simp] theorem snd_inr (q : Element H) : snd (inr G q) = q := snd_pair ..

theorem inl_injective {p q : Element G} (h : inl H p = inl H q) : p = q :=
  by simpa only [fst_inl] using congrArg fst h

theorem inr_injective {p q : Element H} (h : inr G p = inr G q) : p = q :=
  by simpa only [snd_inr] using congrArg snd h

theorem inl_comp (p q : Element G) : inl H (p.comp q) = (inl H p).comp (inl H q) := by
  simp only [inl, ← pair_comp, Element.comp_id]

theorem inr_comp (p q : Element H) : inr G (p.comp q) = (inr G p).comp (inr G q) := by
  simp only [inr, ← pair_comp, Element.comp_id]

theorem inl_inr (p : Element G) (q : Element H) : (inl H p).comp (inr G q) = pair p q := by
  simp only [inl, inr, ← pair_comp, Element.comp_id, Element.id_comp]

theorem commute (p : Element G) (q : Element H) : (inl H p).comp (inr G q) = (inr G q).comp (inl H p) := by
  simp only [inl, inr, ← pair_comp, Element.comp_id, Element.id_comp]

/-- The two embedded factor images intersect only at the identity. -/
theorem intersection {p : Element G} {q : Element H} (h : inl H p = inr G q) :
    p = Element.id G ∧ q = Element.id H :=
  ⟨by simpa only [fst_inl, fst_inr] using congrArg fst h,
    by simpa only [snd_inl, snd_inr] using (congrArg snd h).symm⟩

theorem decomposition (r : Element (G.directProduct H)) : (inl H (fst r)).comp (inr G (snd r)) = r := by
  rw [inl_inr, pair_factors]

theorem unique {r : Element (G.directProduct H)} {p : Element G} {q : Element H}
    (h : (inl H p).comp (inr G q) = r) : p = fst r ∧ q = snd r := by
  rw [inl_inr] at h
  exact ⟨by simpa only [fst_pair] using congrArg fst h,
    by simpa only [snd_pair] using congrArg snd h⟩

end Hex.PermGroup.DirectProduct
