/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.Basic

public section

/-!
The finite encoding of Mathlib coloured graphs and its correspondence
theorems.

For `e : V ≃ Fin n`, the executable graph has an edge between `e v` and
`e w` exactly when the Mathlib graph has an edge between `v` and `w`,
and the executable colour of `e v` is the original colour of `v`. The
two directions of `encode_iso_iff` explicitly conjugate the executable
permutation by the chosen equivalences; no enumeration is treated as
canonical, and a different choice changes neither the isomorphism
verdict nor `colored_iso_iff_canon_eq`.
-/

namespace Hex.GraphIso

variable {n : Nat}

/-- The equivalence of `Fin n` performed by a forward permutation. -/
@[expose] def Perm.toEquiv (p : Perm n) : Fin n ≃ Fin n where
  toFun := p.get
  invFun := p.inv.get
  left_inv := p.inv_get_get
  right_inv := p.get_inv_get

@[simp] theorem Perm.toEquiv_apply (p : Perm n) (i : Fin n) :
    p.toEquiv i = p.get i := rfl

/-- The forward permutation performing an equivalence of `Fin n`. -/
@[expose] def Perm.ofEquiv (e : Fin n ≃ Fin n) : Perm n :=
  Perm.ofFn e (fun _ _ h => e.injective h)
    (fun i => ⟨e.symm i, e.apply_symm_apply i⟩)

@[simp] theorem Perm.get_ofEquiv (e : Fin n ≃ Fin n) (i : Fin n) :
    (Perm.ofEquiv e).get i = e i :=
  Perm.get_ofFn ..

end Hex.GraphIso

namespace Hex.GraphIso.Mathlib

universe u v

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W] {k n : Nat}

/-- The executable image of a coloured Mathlib graph along a chosen
finite enumeration. -/
@[expose] def encode (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj] :
    Hex.GraphIso.Colored n k where
  graph := Hex.Graph.ofAdj
    (fun i j => decide (G.graph.Adj (e.symm i) (e.symm j)))
    (fun i j => by
      simp only [decide_eq_decide]
      exact SimpleGraph.adj_comm ..)
    (fun i => by simp)
  coloring :=
    { cells := Hex.Vector.ofFn' fun i => G.color (e.symm i)
      onto := fun c => by
        rcases G.onto c with ⟨v, hv⟩
        refine ⟨e v, ?_⟩
        rw [Hex.Vector.get_eq_getElem]
        simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn', Fin.eta,
          Equiv.symm_apply_apply]
        exact hv }

theorem encode_adj (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] (v w : V) :
    (encode e G).graph.adj (e v) (e w) = true ↔ G.graph.Adj v w := by
  rw [encode, Graph.adj_ofAdj]
  simp

/-- The general-index form of `encode_adj`. -/
theorem encode_adj' (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] (i j : Fin n) :
    (encode e G).graph.adj i j = true ↔ G.graph.Adj (e.symm i) (e.symm j) := by
  rw [encode, Graph.adj_ofAdj]
  simp

theorem encode_color (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] (v : V) :
    (encode e G).coloring.cells[e v] = G.color v := by
  show (Hex.Vector.ofFn' fun i => G.color (e.symm i))[(e v : Fin n)] = _
  simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn', Fin.eta,
    Equiv.symm_apply_apply]

/-- The general-index form of `encode_color`. -/
theorem encode_color' (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] (i : Fin n) :
    (encode e G).coloring.cells[i] = G.color (e.symm i) := by
  show (Hex.Vector.ofFn' fun j => G.color (e.symm j))[i] = _
  simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn', Fin.eta]

/-- Decode an executable forward permutation into an equivalence of the
two vertex types, conjugating by the chosen enumerations. -/
@[expose] def decodePerm (eV : V ≃ Fin n) (eW : W ≃ Fin n) (p : Hex.GraphIso.Perm n) :
    V ≃ W :=
  eV.trans (p.toEquiv.trans eW.symm)

omit [Fintype V] [Fintype W] in
@[simp] theorem decodePerm_apply (eV : V ≃ Fin n) (eW : W ≃ Fin n)
    (p : Hex.GraphIso.Perm n) (v : V) :
    decodePerm eV eW p v = eW.symm (p.get (eV v)) := rfl

variable {G : Colored V k} {H : Colored W k}
  [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]

/-- A checked executable transporter decodes to a colour-preserving
Mathlib isomorphism. -/
def isoOfIsIso (eV : V ≃ Fin n) (eW : W ≃ Fin n) {p : Hex.GraphIso.Perm n}
    (h : IsIso (encode eV G) (encode eW H) p) : Colored.Iso G H where
  graphIso :=
    { toEquiv := decodePerm eV eW p
      map_rel_iff' := by
        intro v w
        show H.graph.Adj (eW.symm (p.get (eV v))) (eW.symm (p.get (eV w))) ↔ _
        rw [← encode_adj' eW H, ← encode_adj eV G, h.adj_eq (eV v) (eV w)] }
  map_color := by
    intro v
    show H.color (eW.symm (p.get (eV v))) = G.color v
    rw [← encode_color' eW H, h.cells_eq (eV v), encode_color eV G]

/-- Every colour-preserving Mathlib isomorphism encodes to an executable
colour-preserving forward permutation. -/
theorem isIso_of_iso (eV : V ≃ Fin n) (eW : W ≃ Fin n) (h : Colored.Iso G H) :
    IsIso (encode eV G) (encode eW H)
      (Perm.ofEquiv (eV.symm.trans (h.graphIso.toEquiv.trans eW))) := by
  refine IsIso.intro ?_ ?_
  · intro i
    simp only [Perm.get_ofEquiv, Equiv.trans_apply]
    rw [encode_color' eV G, encode_color' eW H]
    simp only [Equiv.symm_apply_apply]
    exact h.map_color (eV.symm i)
  · intro i j
    simp only [Perm.get_ofEquiv, Equiv.trans_apply]
    rw [Bool.eq_iff_iff, encode_adj' eV G, encode_adj' eW H]
    simp only [Equiv.symm_apply_apply]
    exact h.graphIso.map_rel_iff

/-- The finite encoding preserves the isomorphism verdict, for any
choice of enumerations. -/
theorem encode_iso_iff (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔
      Hex.GraphIso.Isomorphic (encode eV G) (encode eW H) := by
  constructor
  · intro h
    rcases h.elim with ⟨h⟩
    exact Isomorphic.intro _ (isIso_of_iso eV eW h)
  · intro h
    rcases h.elim with ⟨p, hp⟩
    exact Colored.Isomorphic.intro (isoOfIsIso eV eW hp)

/-- The principal Mathlib-facing biconditional: two coloured graphs are
isomorphic exactly when their encodings have equal canonical forms. -/
theorem colored_iso_iff_canon_eq (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔
      canon (encode eV G) = canon (encode eW H) :=
  (encode_iso_iff eV eW).trans (iso_iff_canon_eq ..)

/-! # Automorphisms -/

/-- The automorphism generators the pinned search discovers, decoded as
colour-preserving self-isomorphisms of the Mathlib graph. Each entry is
an automorphism by `Hex.GraphIso.autos_isIso`, decoded by
`isoOfIsIso`; whether the list generates the whole automorphism group
is not proved, so this is a source of automorphisms rather than a
presentation of the group. -/
def autos (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj] :
    List (Colored.Iso G G) :=
  (Aut.gens (encode e G)).attach.map fun p =>
    isoOfIsIso e e (Aut.gens_isIso p.property)

/-- The orbit-stabilizer product the pinned search computes, which is
the order of the colour-preserving automorphism group when the recorded
orbits are the true ones. Conformance pins it against nauty's
`grpsize`; no theorem states it, because that would need the generators
to generate the whole group, and without that it is only a lower
bound. -/
def autOrder (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj] :
    Nat :=
  Aut.order (encode e G)

/-- The number of vertex orbits the pinned search reports, under the
same caveat as `autOrder`. -/
def autNumOrbits (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] : Nat :=
  Aut.numOrbits (encode e G)

/-- Vertices the reported orbit array puts together are carried onto
each other by a colour-preserving automorphism. -/
theorem sameOrbit_of_autos (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] (v w : V)
    (h : (Aut.orbits (encode e G))[(e v).val]! =
      (Aut.orbits (encode e G))[(e w).val]!) :
    ∃ f : Colored.Iso G G, f.graphIso v = w := by
  rcases (Aut.sameOrbit_of_orbits_eq (encode e G) (e v) (e w) h).elim
    with ⟨p, hp, hpv⟩
  refine ⟨isoOfIsIso e e hp, ?_⟩
  show e.symm (p.get (e v)) = w
  rw [hpv, Equiv.symm_apply_apply]

/-! # Cardinality and cell-size obstructions -/

/-- Unequal vertex cardinalities forbid any graph isomorphism. -/
theorem isEmpty_iso_of_card_ne (G : SimpleGraph V) (H : SimpleGraph W)
    (h : Fintype.card V ≠ Fintype.card W) : IsEmpty (G ≃g H) :=
  ⟨fun φ => h (Fintype.card_congr φ.toEquiv)⟩

omit [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj] in
/-- A colour-preserving isomorphism induces equal colour-class
cardinalities. -/
theorem card_color_class_eq (h : Colored.Iso G H) (c : Fin k)
    [DecidableEq (Fin k)] :
    Fintype.card {v // G.color v = c} = Fintype.card {w // H.color w = c} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv h.graphIso.toEquiv fun v => ?_)
  rw [show (h.graphIso.toEquiv v : W) = h.graphIso v from rfl, h.map_color v]

omit [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj] in
/-- Unequal ordered cell sizes forbid coloured isomorphism. -/
theorem not_isomorphic_of_card_color_ne [DecidableEq (Fin k)] {c : Fin k}
    (h : Fintype.card {v // G.color v = c} ≠
      Fintype.card {w // H.color w = c}) :
    ¬ G.Isomorphic H := by
  intro hiso
  rcases hiso.elim with ⟨hiso⟩
  exact h (card_color_class_eq hiso c)

end Hex.GraphIso.Mathlib
