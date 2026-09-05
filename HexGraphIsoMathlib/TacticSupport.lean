/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.Encode

public section

/-!
Object-language support for the `graph_iso` extension to `SimpleGraph`
goals: the one-cell colouring of an uncoloured graph, the checked
kernel-facing entry points for each supported goal shape, and the
empty-graph and cardinality special cases. The tactic emits applications
of these theorems on literal data; every decisive check is performed by
the kernel through `checkIso?` or the verified pairwise decision.
-/

namespace Hex.GraphIso.Mathlib

universe u v

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W] {k n : Nat}

/-- The enumeration equivalence induced by a literal duplicate-free
complete element list: vertex `v` maps to its list position. Both
directions are structural list operations, so ground instances
kernel-reduce; the tactic obtains the list by reducing
`Finset.univ.val` and certifies the three side conditions by `decide`. -/
@[expose] def listEquiv [DecidableEq V] (l : List V)
    (hlen : l.length = Fintype.card V) (hnodup : l.Nodup)
    (hcompl : ∀ v : V, v ∈ l) : V ≃ Fin (Fintype.card V) where
  toFun v := ⟨l.idxOf v, hlen ▸ List.idxOf_lt_length_of_mem (hcompl v)⟩
  invFun i := l[i.val]'(hlen.symm ▸ i.isLt)
  left_inv v := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hcompl v))
  right_inv _i := Fin.ext (hnodup.idxOf_getElem _ _)

/-- The one-cell colouring of an uncoloured graph over a nonempty vertex
type; the executable encoding of `G ≃g H` goals. -/
@[expose] def onecell (G : SimpleGraph V) (h : 0 < Fintype.card V) :
    Colored V 1 where
  graph := G
  color := fun _ => 0
  onto := fun c => by
    rcases Fintype.card_pos_iff.mp h with ⟨v⟩
    exact ⟨v, Subsingleton.elim _ _⟩

instance {G : SimpleGraph V} [DecidableRel G.Adj] (h : 0 < Fintype.card V) :
    DecidableRel (onecell G h).graph.Adj :=
  inferInstanceAs (DecidableRel G.Adj)

/-- One-cell colourings are isomorphic exactly when the graphs are. -/
theorem onecell_isomorphic_iff {G : SimpleGraph V} {H : SimpleGraph W}
    (hV : 0 < Fintype.card V) (hW : 0 < Fintype.card W) :
    (onecell G hV).Isomorphic (onecell H hW) ↔ Nonempty (G ≃g H) := by
  constructor
  · intro h
    rcases h.elim with ⟨h⟩
    exact ⟨h.graphIso⟩
  · rintro ⟨φ⟩
    exact Colored.Isomorphic.intro
      { graphIso := φ, map_color := fun v => Subsingleton.elim _ _ }

/-! # Positive entry points -/

/-- A kernel-checked transporter yields a coloured isomorphism. -/
def coloredIsoOfCheckIso? (eV : V ≃ Fin n) (eW : W ≃ Fin n)
    {G : Colored V k} {H : Colored W k}
    [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]
    (replay : ReplayLimits) (p : Perm n)
    (h : checkIso? replay (encode eV G) (encode eW H) p = some true) :
    Colored.Iso G H :=
  isoOfIsIso eV eW ((checkIso?_some h).mp rfl)

/-- A kernel-checked transporter yields a graph isomorphism. -/
def isoOfCheckIso? (eV : V ≃ Fin n) (eW : W ≃ Fin n)
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hV : 0 < Fintype.card V) (hW : 0 < Fintype.card W)
    (replay : ReplayLimits) (p : Perm n)
    (h : checkIso? replay (encode eV (onecell G hV))
      (encode eW (onecell H hW)) p = some true) : G ≃g H :=
  (coloredIsoOfCheckIso? eV eW replay p h).graphIso

/-- Two graphs on empty vertex types are isomorphic. -/
def isoOfCardZero (G : SimpleGraph V) (H : SimpleGraph W)
    (hV : Fintype.card V = 0) (hW : Fintype.card W = 0) : G ≃g H where
  toEquiv := @Equiv.equivOfIsEmpty V W
    (Fintype.card_eq_zero_iff.mp hV) (Fintype.card_eq_zero_iff.mp hW)
  map_rel_iff' := by
    intro a b
    exact (Fintype.card_eq_zero_iff.mp hV).elim a

/-- Two coloured graphs on empty vertex types are isomorphic. -/
def coloredIsoOfCardZero (G : Colored V k) (H : Colored W k)
    (hV : Fintype.card V = 0) (hW : Fintype.card W = 0) : Colored.Iso G H where
  graphIso := isoOfCardZero G.graph H.graph hV hW
  map_color := fun v => ((Fintype.card_eq_zero_iff.mp hV).elim v)

/-! # Negative entry points -/

/-- Non-isomorphism of the encodings refutes coloured isomorphism:
the route-agnostic form, taking whatever negative proof the tactic's
shared engine produced. -/
theorem not_isomorphic_of_not_encode_iso (eV : V ≃ Fin n) (eW : W ≃ Fin n)
    {G : Colored V k} {H : Colored W k}
    [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]
    (h : ¬ Hex.GraphIso.Isomorphic (encode eV G) (encode eW H)) :
    ¬ G.Isomorphic H :=
  fun hiso => h ((encode_iso_iff eV eW).mp hiso)

theorem isEmpty_coloredIso_of_not_encode_iso (eV : V ≃ Fin n)
    (eW : W ≃ Fin n) {G : Colored V k} {H : Colored W k}
    [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]
    (h : ¬ Hex.GraphIso.Isomorphic (encode eV G) (encode eW H)) :
    IsEmpty (Colored.Iso G H) :=
  ⟨fun hiso => not_isomorphic_of_not_encode_iso eV eW h
    (Colored.Isomorphic.intro hiso)⟩

theorem isEmpty_iso_of_not_encode_iso (eV : V ≃ Fin n) (eW : W ≃ Fin n)
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hV : 0 < Fintype.card V) (hW : 0 < Fintype.card W)
    (h : ¬ Hex.GraphIso.Isomorphic (encode eV (onecell G hV))
      (encode eW (onecell H hW))) : IsEmpty (G ≃g H) :=
  ⟨fun φ => not_isomorphic_of_not_encode_iso eV eW h
    ((onecell_isomorphic_iff hV hW).mpr ⟨φ⟩)⟩

theorem not_nonempty_iso_of_not_encode_iso (eV : V ≃ Fin n)
    (eW : W ≃ Fin n) {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hV : 0 < Fintype.card V) (hW : 0 < Fintype.card W)
    (h : ¬ Hex.GraphIso.Isomorphic (encode eV (onecell G hV))
      (encode eW (onecell H hW))) : ¬ Nonempty (G ≃g H) :=
  fun ⟨φ⟩ => (isEmpty_iso_of_not_encode_iso eV eW hV hW h).elim φ

/-- Unequal cardinalities refute nonemptiness of the isomorphism type. -/
theorem not_nonempty_iso_of_card_ne (G : SimpleGraph V) (H : SimpleGraph W)
    (h : Fintype.card V ≠ Fintype.card W) : ¬ Nonempty (G ≃g H) :=
  fun ⟨φ⟩ => (isEmpty_iso_of_card_ne G H h).elim φ

/-- Unequal cardinalities refute coloured isomorphism. -/
theorem not_isomorphic_of_card_ne (G : Colored V k) (H : Colored W k)
    (h : Fintype.card V ≠ Fintype.card W) : ¬ G.Isomorphic H := by
  intro hiso
  rcases hiso.elim with ⟨hiso⟩
  exact h (Fintype.card_congr hiso.graphIso.toEquiv)

theorem isEmpty_coloredIso_of_card_ne (G : Colored V k) (H : Colored W k)
    (h : Fintype.card V ≠ Fintype.card W) : IsEmpty (Colored.Iso G H) :=
  ⟨fun hiso => not_isomorphic_of_card_ne G H h (Colored.Isomorphic.intro hiso)⟩

end Hex.GraphIso.Mathlib
