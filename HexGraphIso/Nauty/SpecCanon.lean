/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CanonForm

public section

/-!
The nauty-semantic canonical form as a total function of the spec key:
adjacency is read off the key's rows, and the colouring lists each
colour class contiguously in colour order. Checked certificate results
coincide with this form, which anchors the stage-4 public switch.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # The sorted colour sequence -/

/-- The colour of each position when classes are laid out
contiguously in colour order. -/
@[expose] def sortedColorSeq (G : Colored n k) : List Nat :=
  (List.range k).flatMap fun c =>
    List.replicate (colorClass G c).length c

theorem length_sortedColorSeq (G : Colored n k) :
    (sortedColorSeq G).length = n := by
  rw [sortedColorSeq, List.length_flatMap]
  have h1 : List.map (fun c => (List.replicate
      (colorClass G c).length c).length) (List.range k) =
      List.map List.length ((List.range k).map (colorClass G)) := by
    rw [List.map_map]
    exact List.map_congr_left fun c _ => by
      rw [List.length_replicate]
      rfl
  rw [h1]
  exact totalOf_classes G

theorem mem_sortedColorSeq_lt (G : Colored n k) {c : Nat}
    (h : c ∈ sortedColorSeq G) : c < k := by
  rw [sortedColorSeq] at h
  rcases List.mem_flatMap.mp h with ⟨c', hc', hm⟩
  rw [List.eq_of_mem_replicate hm]
  exact List.mem_range.mp hc'

theorem pairwise_sortedColorSeq (G : Colored n k) :
    (sortedColorSeq G).Pairwise (· ≤ ·) := by
  rw [sortedColorSeq]
  have hgen : ∀ (m : Nat), (((List.range m).flatMap fun c =>
      List.replicate (colorClass G c).length c)).Pairwise
      (· ≤ ·) := by
    intro m
    induction m with
    | zero => exact List.Pairwise.nil
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [List.pairwise_append]
      refine ⟨ih, List.pairwise_replicate.mpr
        (Or.inr (Nat.le_refl m)), ?_⟩
      intro x hx y hy
      rcases List.mem_flatMap.mp hx with ⟨c', hc', hm⟩
      rw [List.eq_of_mem_replicate hm]
      rw [List.eq_of_mem_replicate hy]
      exact Nat.le_of_lt (List.mem_range.mp hc')
  exact hgen k

theorem count_sortedColorSeq (G : Colored n k) {c : Nat}
    (hc : c < k) :
    (sortedColorSeq G).count c = (colorClass G c).length := by
  rw [sortedColorSeq]
  have hgen : ∀ (m : Nat), (((List.range m).flatMap fun c' =>
      List.replicate (colorClass G c').length c')).count c =
      if c < m then (colorClass G c).length else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.count_append, ih,
        List.count_replicate]
      rcases Nat.lt_trichotomy c m with h | rfl | h
      · have hb : (m == c) = false := by
          simp
          omega
        rw [hb, ite_eq_left h, ite_eq_left (by omega : c < m + 1)]
        simp
      · have hb : (c == c) = true := by simp
        rw [hb, ite_eq_right (by omega : ¬c < c),
          ite_eq_left (by omega : c < c + 1)]
        simp
      · have hb : (m == c) = false := by
          simp
          omega
        rw [hb, ite_eq_right (by omega : ¬c < m),
          ite_eq_right (by omega : ¬c < m + 1)]
        simp
  rw [hgen k, ite_eq_left hc]

/-! # The form determined by a key -/

/-- The coloured graph whose adjacency is a key's rows and whose
colours list `G`'s classes contiguously. Arbitrary row bits are
normalized into a simple graph: an edge needs the bit in both
directions and the diagonal is dropped; on genuine keys, whose rows
are symmetric and loopless, this is the identity. -/
@[expose] def formOfKey (G : Colored n k) (rows : List (VSet n)) :
    Colored n k where
  graph := Hex.Graph.ofAdj
    (fun i j => rows[i.val]!.mem j.val &&
      rows[j.val]!.mem i.val && i.val != j.val)
    (fun i j => by
      have hb : (i.val != j.val) = (j.val != i.val) := by
        rcases Decidable.em (i.val = j.val) with he | he
        · rw [he]
        · have h1 : (i.val != j.val) = true := by simpa using he
          have h2 : (j.val != i.val) = true := by
            simpa using Ne.symm he
          rw [h1, h2]
      rw [hb]
      rcases h1 : rows[i.val]!.mem j.val with _ | _ <;>
        rcases h2 : rows[j.val]!.mem i.val with _ | _ <;>
        simp [*])
    (fun i => by simp)
  coloring :=
    { cells := Hex.Vector.ofFn' fun i =>
        ⟨(sortedColorSeq G)[i.val]!,
          mem_sortedColorSeq_lt G (by
            rw [getElem!_pos _ _ (by
              rw [length_sortedColorSeq]
              exact i.isLt)]
            exact List.getElem_mem _)⟩
      onto := fun c => by
        have hne : (colorClass G c.val).length ≠ 0 := by
          intro hz
          obtain ⟨v, hv⟩ := G.coloring.onto c
          have hm : v.val ∈ colorClass G c.val :=
            mem_colorClass.mpr ⟨v.isLt, c.isLt, by
              show G.coloring.cells[v] = (⟨c.val, c.isLt⟩ : Fin k)
              have hv' := hv
              rw [Hex.Vector.get_eq_getElem] at hv'
              exact hv'⟩
          rw [List.length_eq_zero_iff] at hz
          rw [hz] at hm
          cases hm
        have hcm : c.val ∈ sortedColorSeq G := by
          have := count_sortedColorSeq G c.isLt
          rcases Decidable.em (c.val ∈ sortedColorSeq G) with h | h
          · exact h
          · rw [List.count_eq_zero_of_not_mem h] at this
            omega
        obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.mp hcm
        rw [length_sortedColorSeq] at hidx
        refine ⟨⟨idx, hidx⟩, ?_⟩
        rw [Hex.Vector.get_eq_getElem]
        simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn']
        refine Fin.eq_of_val_eq ?_
        show (sortedColorSeq G)[idx]! = c.val
        rw [getElem!_pos _ _ (by
          rw [length_sortedColorSeq]
          exact hidx)]
        exact hval }

/-- The total nauty-semantic canonical form. -/
@[expose] def specCanon (G : Colored n k) : Colored n k :=
  formOfKey G (canonSpecKey G).rows

theorem colorList_formOfKey (G : Colored n k) (rows : List (VSet n)) :
    colorList (formOfKey G rows) = sortedColorSeq G := by
  rw [colorList]
  have hlen := length_sortedColorSeq G
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  rw [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, keyOf, dite_eq_left h1]
  show ((formOfKey G rows).coloring.cells[(⟨i, h1⟩ : Fin n)]).val =
    (sortedColorSeq G)[i]
  rw [formOfKey]
  simp only [Fin.getElem_fin, Hex.Vector.getElem_ofFn']
  show (sortedColorSeq G)[i]! = (sortedColorSeq G)[i]
  exact getElem!_pos _ _ (by omega)

/-- A checked canonical form is the form of its key. -/
theorem checkCanon_form_eq_formOfKey {G : Colored n k}
    {cert : CertNode} {B : Key n} {lab : Array Nat}
    {res : CanonResult n k}
    (h : checkCanon G cert B lab = some res) :
    res.form = formOfKey G B.rows := by
  refine Colored.ext ?_ ?_
  · intro i j
    have hadjL : res.form.graph.adj i j =
        (B.rows[i.val]!).mem j.val := by
      have h1 : res.form.graph.adj i j =
          ((rowsOf res.form)[i.val]!).mem j.val := by
        rw [getElem!_rowsOf _ i.isLt, mem_rowOf_lt _ i.isLt
          j.isLt]
      rw [h1, checkCanon_rows h, List.getElem!_toArray]
    have hadjLs : res.form.graph.adj j i =
        (B.rows[j.val]!).mem i.val := by
      have h1 : res.form.graph.adj j i =
          ((rowsOf res.form)[j.val]!).mem i.val := by
        rw [getElem!_rowsOf _ j.isLt, mem_rowOf_lt _ j.isLt
          i.isLt]
      rw [h1, checkCanon_rows h, List.getElem!_toArray]
    have hsym : (B.rows[j.val]!).mem i.val =
        (B.rows[i.val]!).mem j.val := by
      rw [← hadjL, ← hadjLs]
      exact (Hex.Graph.adj_symm _ i j).symm
    have hR : (formOfKey G B.rows).graph.adj i j =
        ((B.rows[i.val]!).mem j.val &&
          (B.rows[j.val]!).mem i.val && i.val != j.val) := by
      simp only [formOfKey, Hex.Graph.adj_ofAdj]
    rw [hadjL, hR, hsym]
    rcases Decidable.em (i.val = j.val) with he | he
    · have hii : i = j := Fin.eq_of_val_eq he
      subst hii
      have hL : res.form.graph.adj i i = false :=
        Hex.Graph.adj_self _ i
      rw [← hadjL, hL]
      simp
    · have hne : (i.val != j.val) = true := by simpa using he
      rw [hne]
      rcases hb : (B.rows[i.val]!).mem j.val with _ | _ <;> simp
  · intro i
    have hcl : colorList res.form = colorList (formOfKey G B.rows) := by
      rw [colorList_formOfKey]
      refine List.Perm.eq_of_pairwise
        (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) ?_
        (pairwise_sortedColorSeq G) ?_
      · refine pairwise_le_of_adjacent fun i hi => ?_
        have hs := checkCanon_sorted h i hi
        have hkv : ∀ (K : Colored n k) (j : Nat) (hj : j < n),
            keyOf K j = (K.coloring.cells[j]'(by omega)).val := by
          intro K j hj
          rw [keyOf, dite_eq_left hj]
          rfl
        rw [hkv _ i (by omega), hkv _ (i + 1) (by omega)]
        exact hs
      · rw [List.perm_iff_count]
        intro c
        rcases Nat.lt_or_ge c k with hc | hc
        · rw [count_colorList _ hc, count_sortedColorSeq G hc]
          obtain ⟨p1, hp1⟩ := ((checkCanon_sound h).2.2.1).elim
          rw [length_colorClass_eq hp1 c]
        · rw [count_colorList_ge _ hc]
          have hmem : c ∉ sortedColorSeq G := fun hm =>
            absurd (mem_sortedColorSeq_lt G hm) (by omega)
          rw [List.count_eq_zero_of_not_mem hmem]
    have h1 := congrArg (fun l : List Nat => l[i.val]!) hcl
    simp only [colorList] at h1
    have hget : ∀ (K : Colored n k),
        ((List.range n).map (keyOf K))[i.val]! = keyOf K i.val := by
      intro K
      rw [getElem!_pos _ _ (by simp [i.isLt]), List.getElem_map,
        List.getElem_range]
    rw [hget, hget] at h1
    have hkv : ∀ (K : Colored n k),
        keyOf K i.val = (K.coloring.cells[i.val]'(by
          have := i.isLt
          omega)).val := by
      intro K
      rw [keyOf, dite_eq_left i.isLt]
      rfl
    rw [hkv, hkv] at h1
    exact Fin.eq_of_val_eq h1

/-- A checked canonical form is the total spec form. -/
theorem checkCanon_form {G : Colored n k} {cert : CertNode} {B : Key n}
    {lab : Array Nat} {res : CanonResult n k}
    (h : checkCanon G cert B lab = some res) :
    res.form = specCanon G := by
  rw [checkCanon_form_eq_formOfKey h, specCanon,
    (checkCanon_sound h).1]

/-- The spec form is an isomorphism invariant. -/
theorem specCanon_invariant {G H : Colored n k}
    (hiso : Isomorphic G H) : specCanon G = specCanon H := by
  rw [specCanon, specCanon, canonSpecKey_eq_of_isomorphic hiso]
  have hseq : sortedColorSeq G = sortedColorSeq H := by
    rw [sortedColorSeq, sortedColorSeq]
    refine flatMap_congr_mem _ fun c _ => ?_
    obtain ⟨p, hp⟩ := hiso.elim
    rw [length_colorClass_eq hp c]
  refine Colored.ext ?_ ?_
  · intro i j
    simp only [formOfKey, Hex.Graph.adj_ofAdj]
  · intro i
    have h1 := congrArg (fun l : List Nat => l[i.val]!) hseq
    refine Fin.eq_of_val_eq ?_
    simp only [formOfKey, Fin.getElem_fin, Hex.Vector.getElem_ofFn']
    exact h1

end Hex.GraphIso.Nauty
