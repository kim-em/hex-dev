/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Iso
public import HexGraphIso.Lex

public section

/-!
The reference canonical form.

`Reference.canonicalize` first constructs the colour-sorting label, which
lists vertices by increasing colour and then by original vertex. It
enumerates every labelling whose relabelled graph has contiguous colour
cells in their original order, relabels the graph, and selects the greatest
serialized coloured adjacency matrix under the lexicographic order of
`digits`: ordered cell sizes first, then adjacency bits.

This module proves `relabel_label`, `canon_iso`, `canon_invariant`, and
`iso_iff_canon_eq` for the reference form. It is exponentially expensive
and suitable only for exhaustive small tests and for checking later
implementations; it is not a production fallback and is not required to
return nauty's label or canonical form.
-/

namespace Hex.GraphIso

/-- A canonical form and the label producing it, kept together. -/
structure CanonResult (n k : Nat) where
  /-- The canonical coloured graph. -/
  form : Colored n k
  /-- The label producing the canonical form: `form = G.relabel label`. -/
  label : Label n
deriving DecidableEq

/-- A coloured graph whose colour classes are contiguous in vertex order:
the first cell occupies the least vertices, and so on. Every canonical form
satisfies this. -/
def ColorSorted (K : Colored n k) : Prop :=
  ∀ i j : Fin n, i ≤ j → K.coloring.cells[i] ≤ K.coloring.cells[j]

instance (K : Colored n k) : Decidable (ColorSorted K) :=
  inferInstanceAs (Decidable
    (∀ i j : Fin n, i ≤ j → K.coloring.cells[i] ≤ K.coloring.cells[j]))

namespace Reference

variable {n k : Nat}

/-! # Enumeration of labellings -/

/-- Every list over `Fin n` of length `m`. -/
def allLists (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | m + 1 => (List.finRange n).flatMap fun x => (allLists n m).map (x :: ·)

theorem mem_allLists {n m : Nat} (l : List (Fin n)) (h : l.length = m) :
    l ∈ allLists n m := by
  induction l generalizing m with
  | nil =>
    subst h
    simp [allLists]
  | cons x t ih =>
    subst h
    show x :: t ∈ (List.finRange n).flatMap fun y => (allLists n t.length).map (y :: ·)
    rw [List.mem_flatMap]
    exact ⟨x, List.mem_finRange x, List.mem_map.mpr ⟨t, ih rfl, rfl⟩⟩

/-- Every labelling of `n` vertices. -/
def allLabels (n : Nat) : List (Label n) :=
  (allLists n n).filterMap fun l =>
    if h : l.length = n then
      Label.ofVector? ⟨l.toArray, by simp [h]⟩
    else
      none

theorem mem_allLabels (lab : Label n) : lab ∈ allLabels n := by
  rw [allLabels, List.mem_filterMap]
  refine ⟨lab.perm.vec.toList, mem_allLists _ (by simp), ?_⟩
  rw [dite_eq_left (by simp)]
  have hv : (⟨lab.perm.vec.toList.toArray, by simp⟩ : Vector (Fin n) n) = lab.perm.vec := by
    rw [← Vector.toArray_inj]
    exact Array.toArray_toList
  rw [hv, Label.ofVector?, Perm.ofVector?,
    dite_eq_left ⟨lab.perm.nodup, lab.perm.complete⟩]
  show some (Label.mk _) = some lab
  cases lab with
  | mk p =>
    cases p
    rfl

/-! # The colour-sorting label -/

/-- Vertex order by increasing colour and then by original vertex. -/
@[expose] def sortLe (G : Colored n k) (i j : Fin n) : Bool :=
  decide (G.coloring.cells[i] < G.coloring.cells[j]) ||
    (G.coloring.cells[i] == G.coloring.cells[j] && decide (i.val ≤ j.val))

theorem sortLe_trans (G : Colored n k) (a b c : Fin n)
    (h1 : sortLe G a b) (h2 : sortLe G b c) : sortLe G a c := by
  simp only [sortLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Fin.lt_def, Fin.ext_iff] at h1 h2 ⊢
  omega

theorem sortLe_total (G : Colored n k) (a b : Fin n) :
    sortLe G a b || sortLe G b a := by
  simp only [sortLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Fin.lt_def, Fin.ext_iff]
  omega

theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
  simp only [List.getElem_finRange, ne_eq, Fin.ext_iff, Fin.val_cast]
  omega

/-- The colour-sorting label: vertices by increasing colour, ties by
original vertex. -/
@[expose] def sortLabel (G : Colored n k) : Label n :=
  let l := (List.finRange n).mergeSort (sortLe G)
  have hperm : List.Perm l (List.finRange n) := List.mergeSort_perm _ _
  { perm :=
    { vec := ⟨l.toArray, by simp [hperm.length_eq]⟩
      nodup := by
        have := hperm.nodup_iff.mpr (nodup_finRange n)
        simpa using this
      complete := fun i => by
        have : i ∈ l := hperm.mem_iff.mpr (List.mem_finRange i)
        simpa using this } }

theorem get_sortLabel (G : Colored n k) (i : Fin n) :
    (sortLabel G).get i = ((List.finRange n).mergeSort (sortLe G))[i.val]'
      (by simp [(List.mergeSort_perm _ _).length_eq]) := by
  simp [sortLabel, Label.get, Perm.get]

theorem colorSorted_relabel_sortLabel (G : Colored n k) :
    ColorSorted (G.relabel (sortLabel G)) := by
  intro i j hij
  have hpair := List.pairwise_mergeSort (le := sortLe G)
    (sortLe_trans G) (sortLe_total G) (List.finRange n)
  rcases Nat.lt_or_eq_of_le (Fin.le_def.mp hij) with hlt | heq
  · have hle := List.pairwise_iff_getElem.mp hpair i.val j.val
      (by simp [(List.mergeSort_perm _ _).length_eq])
      (by simp [(List.mergeSort_perm _ _).length_eq]) hlt
    rw [← get_sortLabel, ← get_sortLabel] at hle
    simp only [Fin.getElem_fin, Colored.cells_relabel, Fin.eta]
    simp only [sortLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, Fin.lt_def] at hle
    rcases hle with h | ⟨h, _⟩
    · exact Fin.le_def.mpr (Nat.le_of_lt h)
    · exact Fin.le_def.mpr (Nat.le_of_eq (congrArg Fin.val h))
  · have : i = j := Fin.ext heq
    subst this
    exact Fin.le_refl _

/-! # Serialization -/

theorem div_lt {n p : Nat} (h : p < n * n) : p / n < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp at h
  · exact Nat.div_lt_of_lt_mul h

theorem mod_lt {n p : Nat} (h : p < n * n) : p % n < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp at h
  · exact Nat.mod_lt _ h0

/-- The comparison serialization of a coloured graph: ordered cell sizes,
then the colour of each vertex, then the row-major adjacency matrix bits.

The SPEC order compares cell sizes and then upper-triangle bits. On the
candidates compared by `canonicalize` — mutually isomorphic coloured graphs
with contiguous cells — the colour component is determined by the cell
sizes, and full-matrix row-major comparison of symmetric loopless matrices
meets its first difference at an upper-triangle position, in exactly the
row-major upper-triangle order. The serialization below therefore induces
the SPEC order on every candidate set while keeping the digit list
injective on all coloured graphs. -/
@[expose] def digits (K : Colored n k) : List Nat :=
  K.coloring.cellSizes.toList
    ++ (List.finRange n).map (fun i => (K.coloring.cells[i]).val)
    ++ (List.finRange (n * n)).map fun p =>
        if K.graph.adj ⟨p.val / n, div_lt p.isLt⟩ ⟨p.val % n, mod_lt p.isLt⟩ then 1 else 0

theorem digits_inj {K K' : Colored n k} (h : digits K = digits K') : K = K' := by
  rw [digits, digits] at h
  rcases List.append_inj' h (by simp) with ⟨h12, hadj⟩
  rcases List.append_inj' h12 (by simp) with ⟨-, hcells⟩
  rw [List.map_inj_left] at hcells hadj
  refine Colored.ext (fun i j => ?_) (fun i => ?_)
  · have hp : i.val * n + j.val < n * n := by
      calc i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := (Nat.succ_mul _ _).symm
        _ ≤ n * n := Nat.mul_le_mul_right _ i.isLt
    have hdiv : (i.val * n + j.val) / n = i.val := by
      have hn : 0 < n := i.pos
      rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    have hmod : (i.val * n + j.val) % n = j.val := by
      rw [Nat.mul_comm i.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
    have := hadj ⟨i.val * n + j.val, hp⟩ (List.mem_finRange _)
    have e1 : (⟨(i.val * n + j.val) / n, div_lt hp⟩ : Fin n) = i := Fin.ext hdiv
    have e2 : (⟨(i.val * n + j.val) % n, mod_lt hp⟩ : Fin n) = j := Fin.ext hmod
    rw [e1, e2] at this
    rcases hK : K.graph.adj i j <;> rcases hK' : K'.graph.adj i j <;>
      simp [hK, hK'] at this <;> rfl
  · exact Fin.ext (hcells i (List.mem_finRange i))

/-! # Candidate enumeration and selection -/

/-- Every labelling whose relabelled graph has contiguous colour cells,
paired with that relabelled graph. -/
def candPairs (G : Colored n k) : List (Label n × Colored n k) :=
  (allLabels n).filterMap fun l =>
    if ColorSorted (G.relabel l) then some (l, G.relabel l) else none

theorem of_mem_candPairs {G : Colored n k} {pr : Label n × Colored n k}
    (h : pr ∈ candPairs G) : G.relabel pr.1 = pr.2 ∧ ColorSorted pr.2 := by
  rw [candPairs, List.mem_filterMap] at h
  rcases h with ⟨l, -, hl⟩
  split at hl
  · injection hl with hl
    subst hl
    exact ⟨rfl, by assumption⟩
  · simp at hl

theorem mem_candPairs {G : Colored n k} {l : Label n}
    (h : ColorSorted (G.relabel l)) : (l, G.relabel l) ∈ candPairs G := by
  rw [candPairs, List.mem_filterMap]
  exact ⟨l, mem_allLabels l, by rw [ite_eq_left h]⟩

/-- The reference canonical form and its label. -/
@[expose] def canonicalize (G : Colored n k) : CanonResult n k :=
  let seed := (sortLabel G, G.relabel (sortLabel G))
  let best := pick (fun pr => digits pr.2) seed (candPairs G)
  { form := best.2, label := best.1 }

/-- The reference canonical form. -/
@[expose] def canon (G : Colored n k) : Colored n k :=
  (canonicalize G).form

/-- The label producing the reference canonical form. -/
@[expose] def label (G : Colored n k) : Label n :=
  (canonicalize G).label

/-! # API theorems -/

private theorem best_spec (G : Colored n k) :
    G.relabel (label G) = canon G ∧ ColorSorted (canon G) := by
  rw [label, canon, canonicalize]
  rcases pick_mem (fun pr : Label n × Colored n k => digits pr.2)
      (sortLabel G, G.relabel (sortLabel G)) (candPairs G) with h | h
  · rw [h]
    exact ⟨rfl, colorSorted_relabel_sortLabel G⟩
  · exact of_mem_candPairs h

/-- Relabelling by the canonical label produces the canonical form. -/
theorem relabel_label (G : Colored n k) : G.relabel (label G) = canon G :=
  (best_spec G).1

/-- The canonical form has contiguous colour cells in their original
order. -/
theorem colorSorted_canon (G : Colored n k) : ColorSorted (canon G) :=
  (best_spec G).2

/-- Every coloured graph is isomorphic to its canonical form. -/
theorem canon_iso (G : Colored n k) : Isomorphic G (canon G) := by
  rw [← relabel_label]
  exact isomorphic_relabel ..

/-- The canonical form is the `digits`-greatest colour-sorted graph in the
isomorphism class. -/
theorem le_digits_canon {G K : Colored n k} (hiso : Isomorphic G K)
    (hsorted : ColorSorted K) : lexLe (digits K) (digits (canon G)) := by
  rcases isomorphic_iff_exists_relabel.mp hiso with ⟨l, rfl⟩
  have hmem := mem_candPairs hsorted
  have := le_pick (fun pr : Label n × Colored n k => digits pr.2)
    (sortLabel G, G.relabel (sortLabel G)) (candPairs G)
    (l, G.relabel l) (List.mem_cons_of_mem _ hmem)
  rw [canon, canonicalize]
  exact this

/-- Isomorphic coloured graphs have equal canonical forms. -/
theorem canon_invariant {G H : Colored n k} (h : Isomorphic G H) :
    canon G = canon H := by
  have hGB : Isomorphic G (canon H) := h.trans (canon_iso H)
  have hHA : Isomorphic H (canon G) := h.symm.trans (canon_iso G)
  have h1 : lexLe (digits (canon H)) (digits (canon G)) :=
    le_digits_canon hGB (colorSorted_canon H)
  have h2 : lexLe (digits (canon G)) (digits (canon H)) :=
    le_digits_canon hHA (colorSorted_canon G)
  exact digits_inj (lexLe_antisymm h2 h1)

/-- Two coloured graphs are isomorphic exactly when their canonical forms
are equal. -/
theorem iso_iff_canon_eq (G H : Colored n k) :
    Isomorphic G H ↔ canon G = canon H := by
  constructor
  · exact canon_invariant
  · intro h
    exact (canon_iso G).trans (h ▸ (canon_iso H).symm)

end Reference

end Hex.GraphIso
