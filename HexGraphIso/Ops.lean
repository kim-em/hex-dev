/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Certify

public section

/-!
Public canonical-form operations: the checked-label transcription of
nauty's search, total because the certificate replay accepts its
answer on every input (`Nauty.canonicalize?_isSome`). Every theorem
stated here descends from the Lean-proved `specCanon` equivalence
through that agreement.

`canonicalize` is total. `findIso` composes the two canonical labels
into a forward transporter when the canonical forms agree.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-! # Canonical forms -/

/-- Compute the canonical form of a coloured graph together with the
label producing it: the checked-label transcription of the pinned
nauty search. Total; worst-case cost is factorial. Its answer is the
one the certificate replay validates (`canonicalize_eq_certifyCanon`),
which is how every theorem below reaches it. -/
@[expose] def canonicalize (G : Colored n k) : CanonResult n k :=
  (Nauty.canonicalize? G).get (Nauty.canonicalize?_isSome G)

/-- The canonical form of a coloured graph. -/
@[expose] def canon (G : Colored n k) : Colored n k :=
  (canonicalize G).form

/-- The label producing the canonical form. -/
@[expose] def label (G : Colored n k) : Label n :=
  (canonicalize G).label

/-- The transcription's answer is the certificate-checked one. -/
theorem canonicalize_eq_certifyCanon (G : Colored n k) :
    canonicalize G = Nauty.certifyCanon G := by
  rw [canonicalize]
  simp only [Nauty.canonicalize?_eq, Option.get_some]

/-- The canonical form is the declarative specification form. -/
theorem canon_eq_specCanon (G : Colored n k) :
    canon G = Nauty.specCanon G := by
  rw [canon, canonicalize_eq_certifyCanon]
  exact Nauty.certifyCanon_form G

/-- Relabelling by the canonical label produces the canonical form. -/
theorem relabel_label (G : Colored n k) : G.relabel (label G) = canon G := by
  rw [label, canon, canonicalize_eq_certifyCanon]
  exact Nauty.certifyCanon_relabel G

/-- The canonical form has contiguous colour cells in their original
order. -/
theorem colorSorted_canon (G : Colored n k) : ColorSorted (canon G) := by
  rw [ColorSorted]
  intro i j hij
  rw [canon_eq_specCanon]
  have hkv : ∀ (x : Fin n),
      ((Nauty.specCanon G).coloring.cells[x]).val =
        (Nauty.sortedColorSeq G)[x.val]! := by
    intro x
    rw [Nauty.specCanon]
    simp only [Nauty.formOfKey, Fin.getElem_fin,
      Hex.Vector.getElem_ofFn']
  rw [Fin.le_def, hkv i, hkv j]
  rcases Nat.eq_or_lt_of_le (Fin.le_def.mp hij) with he | hlt
  · rw [he]
    exact Nat.le_refl _
  · have hp := Nauty.pairwise_sortedColorSeq G
    rw [List.pairwise_iff_getElem] at hp
    have hlen := Nauty.length_sortedColorSeq G
    have := hp i.val j.val (by omega) (by
      have := j.isLt
      omega) hlt
    rw [getElem!_pos _ _ (by
        have := i.isLt
        omega),
      getElem!_pos _ _ (by
        have := j.isLt
        omega)]
    exact this

/-- Every coloured graph is isomorphic to its canonical form. -/
theorem canon_iso (G : Colored n k) : Isomorphic G (canon G) := by
  rw [canon_eq_specCanon]
  exact Nauty.specCanon_iso G

/-- Isomorphic coloured graphs have equal canonical forms. -/
theorem canon_invariant {G H : Colored n k} (h : Isomorphic G H) :
    canon G = canon H := by
  rw [canon_eq_specCanon, canon_eq_specCanon]
  exact Nauty.specCanon_invariant h

/-- Two coloured graphs are isomorphic exactly when their canonical forms
are equal. The biconditional compares canonical coloured graphs, not the
labels: label arrays refer to different input vertex names and generally
differ for isomorphic inputs. -/
theorem iso_iff_canon_eq (G : Colored n k) (H : Colored n k) :
    Isomorphic G H ↔ canon G = canon H := by
  rw [canon_eq_specCanon, canon_eq_specCanon]
  exact Nauty.iso_iff_specCanon_eq

/-! # Isomorphism search -/

/-- Find one isomorphism from `G` to `H` when one exists: the forward
transporter through the two canonical forms, the canonical label of `H`
composed with the inverse of the canonical label of `G` (in forward
permutation convention). -/
@[expose] def findIso (G H : Colored n k) : Option (Perm n) :=
  if canon G = canon H then
    some (((label H).toPerm.inv).comp ((label G).toPerm))
  else
    none

/-- The Boolean isomorphism decision. -/
@[expose] def isIso (G H : Colored n k) : Bool :=
  (findIso G H).isSome

/-- Soundness of the search: any permutation it returns really is an
isomorphism. This is the theorem to reach for after a successful
`findIso`; it says nothing about the `none` case, for which see
`findIso_isSome_iff`. -/
theorem findIso_sound {G H : Colored n k} {p : Perm n}
    (h : findIso G H = some p) : IsIso G H p := by
  rw [findIso] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have h1 : IsIso G (canon G) (label G).toPerm := by
      rw [← relabel_label G]
      exact isIso_relabel ..
    have h2 : IsIso H (canon G) (label H).toPerm := by
      rw [hc, ← relabel_label H]
      exact isIso_relabel ..
    exact h1.trans h2.symm
  · simp at h

/-- Completeness of the search: it returns a permutation exactly when
one exists. Together with `findIso_sound` this makes `findIso` a
decision procedure rather than a one-sided test. -/
theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true ↔ Isomorphic G H := by
  rw [findIso]
  split
  · simpa using (iso_iff_canon_eq G H).mpr (by assumption)
  · rename_i hc
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun h => hc ((iso_iff_canon_eq G H).mp h)

/-- The decision answers `true` exactly on isomorphic pairs. -/
theorem isIso_eq_true_iff (G H : Colored n k) :
    isIso G H = true ↔ Isomorphic G H :=
  findIso_isSome_iff G H

/-- The decision answers `false` exactly on non-isomorphic pairs. This
is the negative direction the `graph_iso` tactic needs, and it is a
genuine refutation rather than a failure to find a witness. -/
theorem isIso_eq_false_iff (G H : Colored n k) :
    isIso G H = false ↔ ¬Isomorphic G H := by
  rw [← isIso_eq_true_iff]
  rcases h : isIso G H <;> simp

/-- A positive answer proves isomorphism. -/
theorem isomorphic_of_isIso {G H : Colored n k}
    (h : isIso G H = true) : Isomorphic G H :=
  (isIso_eq_true_iff G H).mp h

end Hex.GraphIso
