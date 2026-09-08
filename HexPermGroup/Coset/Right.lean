/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Coset.Build
public import HexPermGroup.Word.Compose

public section

namespace Hex.PermGroup

/-- A right transversal uses cosets `Hg`, with equality tested by `xy⁻¹ ∈ H`.
It is a distinct result type from a left transversal. -/
structure RightTransversal (G H : Group n) where
  reps : Array (Element G)
  distinct : ∀ i j : Fin reps.size,
    Generated H.generators (reps[i.val].val.comp reps[j.val].val.inv) → i = j
  covers : ∀ p : Element G, ∃ i : Fin reps.size,
    Generated H.generators (p.val.comp reps[i.val].val.inv)
  words : Vector Program reps.size
  checked : ∀ i : Fin reps.size, checkWord G.generators reps[i.val].val words[i.val] = true

/-- Inversion converts a complete left transversal to a complete right
transversal, including its programs in the original input generators. -/
@[expose] def LeftTransversal.inverse (t : LeftTransversal G H) : RightTransversal G H where
  reps := t.reps.map Element.inv
  distinct := by
    intro i j hij
    have hi : i.val < t.reps.size := by simpa using i.isLt
    have hj : j.val < t.reps.size := by simpa using j.isLt
    have he : Generated H.generators (t.reps[i.val].val.inv.comp t.reps[j.val].val) := by
      simpa using hij
    have hji := t.class_injective (i := ⟨j.val, hj⟩) (j := ⟨i.val, hi⟩)
      ((LeftCoset.eq_iff H t.reps[j.val].val t.reps[i.val].val).mpr he)
    exact Fin.ext (congrArg (fun k : Fin t.reps.size => k.val) hji.symm)
  covers := by
    intro p
    obtain ⟨i, hi⟩ := t.covers p.inv
    refine ⟨⟨i.val, by simp⟩, ?_⟩
    simpa using (LeftCoset.eq_iff H t.reps[i.val].val p.inv.val).mp hi
  words := (t.words.map Program.inv).cast (by simp)
  checked := by
    intro i
    apply decide_eq_true
    simpa using Program.eval_inv (of_decide_eq_true (t.checked ⟨i.val, by simpa using i.isLt⟩))

namespace RightTransversal

variable {G H : Group n}

theorem disjoint (t : RightTransversal G H) {i j : Fin t.reps.size} (hne : i ≠ j) (p : Perm n) :
    ¬ (Generated H.generators (p.comp t.reps[i.val].val.inv) ∧
      Generated H.generators (p.comp t.reps[j.val].val.inv)) := by
  rintro ⟨hi, hj⟩
  have he : (p.comp t.reps[i.val].val.inv).inv.comp (p.comp t.reps[j.val].val.inv) =
      t.reps[i.val].val.comp t.reps[j.val].val.inv := by
    apply Perm.ext
    intro x
    simp [Perm.inv_comp]
  exact hne (t.distinct i j (he ▸ hi.inv.comp hj))

theorem covers_product (t : RightTransversal G H) (p : Element G) :
    ∃ (i : Fin t.reps.size) (q : Element H), q.val.comp t.reps[i.val].val = p.val := by
  obtain ⟨i, hi⟩ := t.covers p
  refine ⟨i, ⟨p.val.comp t.reps[i.val].val.inv, hi⟩, ?_⟩
  simp [Perm.comp_assoc]

end RightTransversal

end Hex.PermGroup
