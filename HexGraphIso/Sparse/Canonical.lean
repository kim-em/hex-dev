/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Ops
public import HexGraphIso.Nauty.Sparse.MaxResult
public import HexGraphIso.Nauty.Sparse.SpecCanon
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Sparse.Colored

public section

namespace Hex.GraphIso.Sparse

variable {n k : Nat}

/-- The total native sparse canonical form is the declarative maximum's
form, at every order. The empty graph is unique; the nonempty case reads
the literal production label from the proved exact maximum. -/
theorem canon_eq_specCanon (G : Colored n k) : canon G = Nauty.Sparse.specCanon G := by
  by_cases hz : n = 0
  · apply Colored.toDense_injective
    apply GraphIso.Colored.ext
    · intro i j
      have := i.isLt
      omega
    · intro i
      have := i.isLt
      omega
  · have hn : 0 < n := by omega
    have hb : Nauty.Sparse.State.best G.graph (Nauty.Sparse.runColored G) =
        some (Nauty.Sparse.canonSpecKey G) := Nauty.Sparse.run_max G hn
    unfold Nauty.Sparse.State.best at hb
    split at hb
    · cases hb
    · rw [label_parse G, Option.map_some] at hb
      have hg := congrArg Nauty.Sparse.Key.graph (Option.some.inj hb)
      have hgraph : (canon G).graph = (Nauty.Sparse.specCanon G).graph := by
        rw [← relabel_label]
        exact hg.trans (Nauty.Sparse.canonSpecLabel_attains G)
      apply Colored.toDense_injective
      apply GraphIso.Colored.ext
      · intro i j
        change (canon G).graph.toDense.adj i j = (Nauty.Sparse.specCanon G).graph.toDense.adj i j
        rw [hgraph]
      · intro i
        apply Fin.ext
        change ((canon G).coloring.cells[i]).val =
          ((G.relabel (Nauty.Sparse.canonSpecLabel G)).coloring.cells[i]).val
        rw [canon_colors, Nauty.Sparse.canonSpecLabel_colors]

/-- Isomorphic native sparse inputs have identical canonical forms,
including the ordered colour sequence. -/
theorem canon_invariant {G H : Colored n k} (h : Isomorphic G H) : canon G = canon H := by
  rw [canon_eq_specCanon, canon_eq_specCanon]
  exact Nauty.Sparse.specCanon_invariant h

theorem iso_iff_canon_eq (G H : Colored n k) : Isomorphic G H ↔ canon G = canon H := by
  rw [canon_eq_specCanon, canon_eq_specCanon]
  exact Nauty.Sparse.iso_iff_specCanon_eq G H

theorem canon_relabel (G : Colored n k) (l : Label n) : canon (G.relabel l) = canon G :=
  (canon_invariant (isomorphic_relabel G l)).symm

theorem canon_idempotent (G : Colored n k) : canon (canon G) = canon G :=
  (canon_invariant (canon_iso G)).symm

/-- The actual total sparse decision returns a transporter for every
isomorphic pair; no logical search limit remains in this API. -/
theorem findIso_complete {G H : Colored n k} (h : Isomorphic G H) :
    ∃ p, findIso G H = some p := by
  simp only [findIso, canon_invariant h, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem isIso_eq_true_iff (G H : Colored n k) : isIso G H = true ↔ Isomorphic G H := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    exact Isomorphic.intro p (findIso_sound hp)
  · intro h
    exact Option.isSome_iff_exists.mpr (findIso_complete h)

theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true ↔ Isomorphic G H := isIso_eq_true_iff G H

theorem isomorphic_of_isIso {G H : Colored n k} (h : isIso G H = true) : Isomorphic G H :=
  (isIso_eq_true_iff G H).mp h

theorem isIso_eq_false_iff (G H : Colored n k) : isIso G H = false ↔ ¬ Isomorphic G H := by
  rw [← isIso_eq_true_iff]
  exact Bool.eq_false_iff

theorem findIso_eq_none_iff (G H : Colored n k) : findIso G H = none ↔ ¬ Isomorphic G H := by
  rw [← isIso_eq_false_iff]
  unfold isIso
  cases findIso G H <;> simp

end Hex.GraphIso.Sparse
