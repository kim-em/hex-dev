/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CanonSpec

public section

/-!
The graph-level invariance of the nauty-semantic canonical key:
isomorphic coloured graphs have equal `canonSpecKey`.

The proof composes the two node-level theorems. A vertex renaming
extracted from the isomorphism turns one graph's rows into the other's
(`specNode_map`), and the renamed initial labelling lists each colour
class with the same contents as the other graph's own initial labelling
(`specNode_perm` at the root).
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Adjacency-row characterization -/

theorem testBit_foldl_step (f : Nat → Bool) (step : Nat → Nat → Nat)
    (hstep : ∀ row j, step row j =
      if f j then insert row j else row) :
    ∀ (l : List Nat) (row0 t : Nat),
      (l.foldl step row0).testBit t =
        (row0.testBit t || (l.contains t && f t))
  | [], row0, t => by simp
  | j :: rest, row0, t => by
    rw [List.foldl_cons, testBit_foldl_step f step hstep rest,
      List.contains_cons, hstep]
    rcases Decidable.em (j = t) with rfl | hne
    · rcases hPt : f j with _ | _
      · simp [hPt]
      · simp [hPt, testBit_insert]
    · have hjt : (j == t) = false := by simp [hne]
      have htj : (t == j) = false := by simp [Ne.symm hne]
      rcases hPj : f j with _ | _
      · simp [hPj, hjt, htj]
      · simp [hPj, testBit_insert, hjt, htj]

/-- The Boolean adjacency test underlying `rowOf`. -/
@[expose] def adjBit (G : Colored n k) (i j : Nat) : Bool :=
  if h : i < n ∧ j < n then G.graph.adj ⟨i, h.1⟩ ⟨j, h.2⟩ else false

theorem testBit_rowOf (G : Colored n k) (i t : Nat) :
    (rowOf G i).testBit t = ((List.range n).contains t && adjBit G i t) := by
  rw [rowOf, testBit_foldl_step (adjBit G i) _ (fun row j => by
    rw [adjBit]
    rcases Decidable.em (i < n ∧ j < n) with h | h
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      simp)]
  simp

theorem testBit_rowOf_lt (G : Colored n k) {i t : Nat} (hi : i < n)
    (ht : t < n) :
    (rowOf G i).testBit t = G.graph.adj ⟨i, hi⟩ ⟨t, ht⟩ := by
  rw [testBit_rowOf, adjBit, dif_pos ⟨hi, ht⟩]
  simp [List.contains_iff_mem, List.mem_range, ht]

theorem rowOf_lt (G : Colored n k) (i : Nat) : rowOf G i < 2 ^ n := by
  refine lt_two_pow_of_bits fun t ht => ?_
  rw [testBit_rowOf]
  have : (List.range n).contains t = false := by
    simp [List.contains_iff_mem, List.mem_range]
    omega
  rw [this]
  simp

theorem size_rowsOf (G : Colored n k) : (rowsOf G).size = n := by
  rw [rowsOf]
  simp

theorem getElem!_rowsOf (G : Colored n k) {i : Nat} (hi : i < n) :
    (rowsOf G)[i]! = rowOf G i := by
  rw [rowsOf, List.getElem!_toArray,
    getElem!_pos _ _ (by simp [hi]), List.getElem_map,
    List.getElem_range]

/-! # The renaming underlying a permutation -/

/-- The vertex renaming of a permutation: `p.get` below `n`, the
identity above. -/
@[expose] def renamingOf (p : Perm n) : Renaming n where
  toFun v := if h : v < n then (p.get ⟨v, h⟩).val else v
  inj a b hab := by
    rcases Decidable.em (a < n) with ha | ha <;>
      rcases Decidable.em (b < n) with hb | hb
    · rw [dif_pos ha, dif_pos hb] at hab
      have := p.get_inj (Fin.eq_of_val_eq hab)
      exact congrArg Fin.val this
    · rw [dif_pos ha, dif_neg hb] at hab
      exact absurd ((p.get ⟨a, ha⟩).isLt) (by omega)
    · rw [dif_neg ha, dif_pos hb] at hab
      exact absurd ((p.get ⟨b, hb⟩).isLt) (by omega)
    · rw [dif_neg ha, dif_neg hb] at hab
      exact hab
  maps v := by
    rcases Decidable.em (v < n) with h | h
    · rw [dif_pos h]
      exact ⟨fun _ => (p.get ⟨v, h⟩).isLt, fun _ => h⟩
    · rw [dif_neg h]

theorem renamingOf_lt (p : Perm n) {v : Nat} (hv : v < n) :
    renamingOf p v = (p.get ⟨v, hv⟩).val := by
  show (if h : v < n then (p.get ⟨v, h⟩).val else v) = _
  rw [dif_pos hv]

theorem rowsMap_of_isIso {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) :
    RowsMap (renamingOf p) (rowsOf G) (rowsOf H) := by
  refine ⟨size_rowsOf G, size_rowsOf H, fun v hv => ?_⟩
  have hσv : renamingOf p v < n := ((renamingOf p).maps v).mp hv
  rw [getElem!_rowsOf H hσv, getElem!_rowsOf G hv]
  refine Nat.eq_of_testBit_eq fun t => ?_
  rcases Nat.lt_or_ge t n with ht | ht
  · obtain ⟨w, hw⟩ := p.get_surj ⟨t, ht⟩
    have hσw : renamingOf p w.val = t := by
      rw [renamingOf_lt p w.isLt]
      show (p.get w).val = t
      rw [hw]
    rw [← hσw, testBit_image_apply (renamingOf p) _ w.isLt,
      testBit_rowOf_lt H hσv (hσw ▸ ht), testBit_rowOf_lt G hv w.isLt]
    have hfv : (⟨renamingOf p v, hσv⟩ : Fin n) = p.get ⟨v, hv⟩ :=
      Fin.eq_of_val_eq (renamingOf_lt p hv)
    have hfw : (⟨renamingOf p w.val, hσw ▸ ht⟩ : Fin n) = p.get w := by
      refine Fin.eq_of_val_eq ?_
      show renamingOf p w.val = (p.get w).val
      rw [renamingOf_lt p w.isLt]
    rw [hfv, hfw]
    exact h.adj_eq ⟨v, hv⟩ w
  · rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (rowOf_lt H _)
        (Nat.pow_le_pow_right (by omega) ht)),
      Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (image_lt (renamingOf p) _)
        (Nat.pow_le_pow_right (by omega) ht))]

/-! # Colour classes -/

theorem nodup_map_of_inj {f : Nat → Nat}
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List Nat}, l.Nodup → (l.map f).Nodup := by
  intro l hl
  rw [List.nodup_iff_pairwise_ne] at hl ⊢
  rw [List.pairwise_map]
  exact hl.imp fun hab he => hab (hf _ _ he)

theorem mem_colorClass {G : Colored n k} {c v : Nat} :
    v ∈ colorClass G c ↔
      ∃ (hv : v < n) (hc : c < k),
        G.coloring.cells[(⟨v, hv⟩ : Fin n)] = ⟨c, hc⟩ := by
  rw [colorClass, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hv, hcond⟩
    rcases Decidable.em (v < n ∧ c < k) with h | h
    · rw [dif_pos h] at hcond
      exact ⟨h.1, h.2, by simpa using hcond⟩
    · rw [dif_neg h] at hcond
      cases hcond
  · rintro ⟨hv, hc, he⟩
    refine ⟨hv, ?_⟩
    rw [dif_pos ⟨hv, hc⟩]
    exact beq_iff_eq.mpr he

theorem nodup_colorClass (G : Colored n k) (c : Nat) :
    (colorClass G c).Nodup :=
  List.filter_sublist.nodup List.nodup_range

theorem colorClass_perm {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) (c : Nat) :
    (colorClass H c).Perm ((colorClass G c).map (renamingOf p)) := by
  refine (List.perm_ext_iff_of_nodup (nodup_colorClass H c)
    (nodup_map_of_inj (renamingOf p).inj
      (nodup_colorClass G c))).mpr fun w => ?_
  constructor
  · intro hw
    rcases mem_colorClass.mp hw with ⟨hwn, hc, he⟩
    refine List.mem_map.mpr ⟨(p.inv.get ⟨w, hwn⟩).val, ?_, ?_⟩
    · refine mem_colorClass.mpr
        ⟨(p.inv.get ⟨w, hwn⟩).isLt, hc, ?_⟩
      have hcells := h.cells_eq (p.inv.get ⟨w, hwn⟩)
      simp only [Perm.get_inv_get] at hcells
      show G.coloring.cells[p.inv.get ⟨w, hwn⟩] = ⟨c, hc⟩
      rw [← hcells]
      exact he
    · rw [renamingOf_lt p (p.inv.get ⟨w, hwn⟩).isLt]
      show (p.get (p.inv.get ⟨w, hwn⟩)).val = w
      rw [Perm.get_inv_get]
  · intro hw
    rcases List.mem_map.mp hw with ⟨v, hvm, rfl⟩
    rcases mem_colorClass.mp hvm with ⟨hvn, hc, he⟩
    have hσ : renamingOf p v = (p.get ⟨v, hvn⟩).val :=
      renamingOf_lt p hvn
    rw [hσ]
    refine mem_colorClass.mpr ⟨(p.get ⟨v, hvn⟩).isLt, hc, ?_⟩
    show H.coloring.cells[p.get ⟨v, hvn⟩] = ⟨c, hc⟩
    rw [h.cells_eq ⟨v, hvn⟩]
    exact he

theorem length_colorClass_eq {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) (c : Nat) :
    (colorClass H c).length = (colorClass G c).length := by
  rw [(colorClass_perm h c).length_eq, List.length_map]

/-! # The flattened classes list all vertices -/

theorem flatMap_filter_key_perm (key : Nat → Nat) :
    ∀ (K : Nat) (l : List Nat), (∀ v ∈ l, key v < K) →
      (((List.range K).map fun c =>
        l.filter fun v => key v == c).flatMap id).Perm l
  | 0, l, hK => by
    rcases l with _ | ⟨v, l⟩
    · simp
    · exact absurd (hK v (by simp)) (by omega)
  | K + 1, l, hK => by
    rw [List.range_succ, List.map_append, List.flatMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, id]
    have hmap : (List.range K).map
        (fun c => l.filter fun v => key v == c) =
        (List.range K).map (fun c =>
          (l.filter fun v => key v != K).filter fun v =>
            key v == c) := by
      refine List.map_congr_left fun c hc => ?_
      have hcK := List.mem_range.mp hc
      rw [List.filter_filter]
      refine (List.filter_congr fun v _ => ?_).symm
      rcases hkc : key v == c with _ | _
      · simp
      · have : key v = c := by simpa using hkc
        simp [this, Nat.ne_of_lt hcK]
    rw [hmap]
    have hIH := flatMap_filter_key_perm key K
      (l.filter fun v => key v != K) (fun v hv => by
        rcases List.mem_filter.mp hv with ⟨hvl, hne⟩
        have h1 := hK v hvl
        have hne' : key v ≠ K := by simpa using hne
        omega)
    refine (hIH.append_right _).trans ?_
    have hnot : (l.filter fun v => !(key v != K)) =
        l.filter fun v => key v == K :=
      List.filter_congr fun v _ => by simp [bne]
    have hap := List.filter_append_perm (fun v => key v != K) l
    rw [hnot] at hap
    exact hap

/-- The colour of a vertex, as a plain `Nat`. -/
@[expose] def keyOf (G : Colored n k) (v : Nat) : Nat :=
  if h : v < n then (G.coloring.cells[(⟨v, h⟩ : Fin n)]).val else 0

theorem colorClass_eq_key {G : Colored n k} {c : Nat} (hc : c < k) :
    colorClass G c = (List.range n).filter fun v => keyOf G v == c := by
  rw [colorClass]
  refine List.filter_congr fun v hv => ?_
  have hvn := List.mem_range.mp hv
  rw [dif_pos ⟨hvn, hc⟩, keyOf, dif_pos hvn]
  rcases Decidable.em ((G.coloring.cells[(⟨v, hvn⟩ : Fin n)]).val = c)
    with he | hne
  · rw [beq_iff_eq.mpr (Fin.eq_of_val_eq he), beq_iff_eq.mpr he]
  · have h1 : (G.coloring.cells[(⟨v, hvn⟩ : Fin n)] ==
        (⟨c, hc⟩ : Fin k)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      exact hne (congrArg Fin.val he)
    have h2 : ((G.coloring.cells[(⟨v, hvn⟩ : Fin n)]).val == c) =
        false := by
      simpa using hne
    rw [h1, h2]

theorem flatten_classes_perm (G : Colored n k) :
    (((List.range k).map (colorClass G)).flatMap id).Perm
      (List.range n) := by
  have hmap : (List.range k).map (colorClass G) =
      (List.range k).map fun c =>
        (List.range n).filter fun v => keyOf G v == c :=
    List.map_congr_left fun c hc =>
      colorClass_eq_key (List.mem_range.mp hc)
  rw [hmap]
  refine flatMap_filter_key_perm (keyOf G) k (List.range n)
    fun v hv => ?_
  rw [keyOf, dif_pos (List.mem_range.mp hv)]
  exact (G.coloring.cells[(⟨v, List.mem_range.mp hv⟩ : Fin n)]).isLt

/-! # The initial partition -/

theorem initialPartition_fst (G : Colored n k) :
    (initialPartition G).1 =
      (((List.range k).map (colorClass G)).flatMap id).toArray := rfl

theorem size_initialPartition (G : Colored n k) :
    (initialPartition G).1.size = n := by
  rw [initialPartition_fst]
  simpa using (flatten_classes_perm G).length_eq

theorem labOk_initialPartition (G : Colored n k) :
    LabOk (initialPartition G).1 n := by
  intro i hi
  rw [initialPartition_fst] at hi ⊢
  rw [List.getElem!_toArray,
    getElem!_pos _ _ (by simpa using hi)]
  have hm := List.getElem_mem (l := ((List.range k).map
    (colorClass G)).flatMap id) (by simpa using hi)
  exact List.mem_range.mp ((flatten_classes_perm G).mem_iff.mp hm)

theorem foldl_ends_congr :
    ∀ (cls cls' : List (List Nat)) (acc : List Nat × Nat),
      cls.map List.length = cls'.map List.length →
      cls.foldl
        (fun (acc : List Nat × Nat) cl =>
          if cl.isEmpty then acc
          else ((acc.2 + cl.length - 1) :: acc.1, acc.2 + cl.length))
        acc =
      cls'.foldl
        (fun (acc : List Nat × Nat) cl =>
          if cl.isEmpty then acc
          else ((acc.2 + cl.length - 1) :: acc.1, acc.2 + cl.length))
        acc
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | cl :: cls, cl' :: cls', acc, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [List.foldl_cons, List.foldl_cons]
    rcases cl with _ | ⟨x, xs⟩ <;> rcases cl' with _ | ⟨y, ys⟩
    · exact foldl_ends_congr _ _ _ h.2
    · simp at h
    · simp at h
    · simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
      rw [h.1]
      exact foldl_ends_congr _ _ _ h.2

theorem initialPartition_snd (G : Colored n k) :
    (initialPartition G).2 =
      ((((List.range k).map (colorClass G)).foldl
        (fun (acc : List Nat × Nat) cl =>
          if cl.isEmpty then acc
          else ((acc.2 + cl.length - 1) :: acc.1, acc.2 + cl.length))
        ([], 0)).1).reverse := rfl

theorem cellEnds_eq {G H : Colored n k} {p : Perm n}
    (h : IsIso G H p) :
    (initialPartition H).2 = (initialPartition G).2 := by
  rw [initialPartition_snd, initialPartition_snd,
    foldl_ends_congr ((List.range k).map (colorClass H))
      ((List.range k).map (colorClass G)) ([], 0) ?_]
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun c _ => length_colorClass_eq h c

/-! # Cell end positions -/

/-- Total number of vertices across a list of classes. -/
@[expose] def totalOf (cls : List (List Nat)) : Nat :=
  (cls.map List.length).sum

theorem totalOf_nil : totalOf [] = 0 := rfl

theorem totalOf_cons (cl : List Nat) (cls : List (List Nat)) :
    totalOf (cl :: cls) = cl.length + totalOf cls := by
  rw [totalOf, totalOf, List.map_cons, List.sum_cons]

/-- The recorded cell end positions of a list of classes laid out from
offset `s`: one entry per nonempty class. -/
@[expose] def endsOf : List (List Nat) → Nat → List Nat
  | [], _ => []
  | cl :: cls, s =>
    if cl.isEmpty then endsOf cls s
    else (s + cl.length - 1) :: endsOf cls (s + cl.length)

theorem foldl_ends_eq :
    ∀ (cls : List (List Nat)) (acc : List Nat) (s : Nat),
      cls.foldl
        (fun (acc : List Nat × Nat) cl =>
          if cl.isEmpty then acc
          else ((acc.2 + cl.length - 1) :: acc.1, acc.2 + cl.length))
        (acc, s) =
      ((endsOf cls s).reverse ++ acc, s + totalOf cls)
  | [], acc, s => by
    rw [List.foldl_nil, endsOf, totalOf_nil]
    simp
  | cl :: cls, acc, s => by
    rw [List.foldl_cons, endsOf, totalOf_cons]
    rcases hcl : cl.isEmpty with _ | _
    · simp only [Bool.false_eq_true, if_false]
      rw [foldl_ends_eq cls]
      simp [List.reverse_cons, List.append_assoc, Nat.add_assoc]
    · have hnil : cl = [] := by
        rcases cl with _ | _
        · rfl
        · simp at hcl
      subst hnil
      simp only [if_true]
      rw [foldl_ends_eq cls]
      simp

theorem initialPartition_snd_eq (G : Colored n k) :
    (initialPartition G).2 =
      endsOf ((List.range k).map (colorClass G)) 0 := by
  rw [initialPartition_snd, foldl_ends_eq]
  simp

theorem totalOf_classes (G : Colored n k) :
    totalOf ((List.range k).map (colorClass G)) = n := by
  have h1 := (flatten_classes_perm G).length_eq
  rw [List.length_range, List.length_flatMap] at h1
  have h2 : List.map (fun (a : List Nat) => (id a).length)
      ((List.range k).map (colorClass G)) =
      List.map List.length ((List.range k).map (colorClass G)) :=
    List.map_congr_left fun cl _ => rfl
  rw [h2] at h1
  rw [totalOf]
  exact h1

theorem endsOf_ge :
    ∀ (cls : List (List Nat)) (s e : Nat), e ∈ endsOf cls s → s ≤ e
  | [], _, _, h => by rw [endsOf] at h; cases h
  | cl :: cls, s, e, h => by
    rw [endsOf] at h
    rcases hcl : cl.isEmpty with _ | _
    · rw [hcl] at h
      simp only [Bool.false_eq_true, if_false] at h
      rcases List.mem_cons.mp h with rfl | h
      · have : cl.length ≥ 1 := by
          rcases cl with _ | _
          · simp at hcl
          · simp
        omega
      · have := endsOf_ge cls (s + cl.length) e h
        omega
    · rw [hcl] at h
      simp only [if_true] at h
      exact endsOf_ge cls s e h

theorem endsOf_lt :
    ∀ (cls : List (List Nat)) (s e : Nat), e ∈ endsOf cls s →
      e < s + totalOf cls
  | [], _, _, h => by rw [endsOf] at h; cases h
  | cl :: cls, s, e, h => by
    rw [endsOf] at h
    rw [totalOf_cons]
    rcases hcl : cl.isEmpty with _ | _
    · rw [hcl] at h
      simp only [Bool.false_eq_true, if_false] at h
      rcases List.mem_cons.mp h with rfl | h
      · have : cl.length ≥ 1 := by
          rcases cl with _ | _
          · simp at hcl
          · simp
        omega
      · have := endsOf_lt cls (s + cl.length) e h
        omega
    · rw [hcl] at h
      simp only [if_true] at h
      have := endsOf_lt cls s e h
      omega

theorem endsOf_last_mem :
    ∀ (cls : List (List Nat)) (s : Nat), 0 < totalOf cls →
      s + totalOf cls - 1 ∈ endsOf cls s
  | [], _, h => by rw [totalOf_nil] at h; omega
  | cl :: cls, s, h => by
    rw [endsOf]
    rw [totalOf_cons] at h ⊢
    rcases hcl : cl.isEmpty with _ | _
    · simp only [Bool.false_eq_true, if_false]
      rcases Nat.eq_zero_or_pos (totalOf cls) with hz | hpos
      · refine List.mem_cons.mpr (Or.inl ?_)
        omega
      · refine List.mem_cons.mpr (Or.inr ?_)
        have := endsOf_last_mem cls (s + cl.length) hpos
        have harr : s + (cl.length + totalOf cls) - 1 =
            s + cl.length + totalOf cls - 1 := by omega
        rw [harr]
        exact this
    · have hnil : cl = [] := by
        rcases cl with _ | _
        · rfl
        · simp at hcl
      subst hnil
      simp only [if_true]
      have := endsOf_last_mem cls s (by simpa using h)
      simpa using this

/-! # The initial `ptn` and active set -/

theorem size_foldl_set0 :
    ∀ (ends : List Nat) (a : Array Nat),
      (ends.foldl (fun ptn e => ptn.set! e 0) a).size = a.size
  | [], _ => rfl
  | e :: rest, a => by
    rw [List.foldl_cons, size_foldl_set0 rest, Array.size_set!]

theorem size_initPtn (n inf : Nat) (ends : List Nat) :
    (initPtn n inf ends).size = n := by
  rw [initPtn, size_foldl_set0, Array.size_replicate]

theorem getElem!_foldl_set0 :
    ∀ (ends : List Nat) (a : Array Nat) (q : Nat),
      (ends.foldl (fun ptn e => ptn.set! e 0) a)[q]! =
        if q ∈ ends ∧ q < a.size then 0 else a[q]!
  | [], a, q => by simp
  | e :: rest, a, q => by
    rw [List.foldl_cons, getElem!_foldl_set0 rest, Array.size_set!]
    rcases Decidable.em (q ∈ rest ∧ q < a.size) with h1 | h1
    · rw [if_pos h1, if_pos ⟨List.mem_cons.mpr (Or.inr h1.1), h1.2⟩]
    · rw [if_neg h1]
      rcases Decidable.em (q = e) with rfl | hne
      · rcases Nat.lt_or_ge q a.size with hq | hq
        · rw [Array.getElem!_set!_self _ _ _ hq,
            if_pos ⟨List.mem_cons.mpr (Or.inl rfl), hq⟩]
        · rw [if_neg (by omega),
            getElem!_neg _ _ (by rw [Array.size_set!]; omega),
            getElem!_neg _ _ (by omega)]
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hne he.symm)]
        rw [if_neg (fun hc => h1 ⟨?_, hc.2⟩)]
        rcases List.mem_cons.mp hc.1 with he | hm
        · exact absurd he hne
        · exact hm

theorem getElem!_initPtn (n inf : Nat) (ends : List Nat) (q : Nat) :
    (initPtn n inf ends)[q]! =
      if q ∈ ends ∧ q < n then 0 else if q < n then inf else 0 := by
  rw [initPtn, getElem!_foldl_set0, Array.size_replicate]
  rcases Decidable.em (q ∈ ends ∧ q < n) with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rcases Nat.lt_or_ge q n with hq | hq
    · rw [if_pos hq, getElem!_pos _ _ (by simpa using hq),
        Array.getElem_replicate]
    · rw [if_neg (by omega), getElem!_neg _ _ (by simpa using hq)]
      rfl

theorem elem_foldl_active :
    ∀ (ends : List Nat) (acc : Nat × Nat) (w : Nat),
      elem ((ends.foldl
        (fun (p : Nat × Nat) e => (insert p.1 p.2, e + 1)) acc).1) w =
          true →
      elem acc.1 w = true ∨ w = acc.2 ∨ ∃ e ∈ ends, w = e + 1
  | [], acc, w, h => Or.inl h
  | e :: rest, acc, w, h => by
    rw [List.foldl_cons] at h
    rcases elem_foldl_active rest _ w h with h1 | h1 | h1
    · have h2 : (insert acc.1 acc.2).testBit w = true := h1
      rw [testBit_insert] at h2
      rcases Bool.or_eq_true_iff.mp h2 with h3 | h3
      · exact Or.inl h3
      · have h4 : acc.2 = w := by simpa using h3
        exact Or.inr (Or.inl h4.symm)
    · exact Or.inr (Or.inr ⟨e, by simp, by simpa using h1⟩)
    · rcases h1 with ⟨e', he', hw⟩
      exact Or.inr (Or.inr ⟨e', List.mem_cons.mpr (Or.inr he'), hw⟩)

theorem foldl_active_lt {n : Nat} :
    ∀ (ends : List Nat) (acc : Nat × Nat),
      acc.1 < 2 ^ n → acc.2 < n → (∀ e ∈ ends, e < n) →
      List.Pairwise (· < ·) ends →
      ((ends.foldl
        (fun (p : Nat × Nat) e => (insert p.1 p.2, e + 1)) acc).1) <
        2 ^ n
  | [], acc, h1, _, _, _ => h1
  | e :: rest, acc, h1, h2, hb, hs => by
    rw [List.foldl_cons]
    rcases rest with _ | ⟨e', rest'⟩
    · exact insert_lt h1 h2
    · rcases List.pairwise_cons.mp hs with ⟨hlt, hs'⟩
      refine foldl_active_lt (e' :: rest') _ (insert_lt h1 h2) ?_
        (fun x hx => hb x (List.mem_cons.mpr (Or.inr hx))) hs'
      have he' : e < e' := hlt e' (by simp)
      have := hb e' (by simp)
      show e + 1 < n
      omega

theorem endsOf_pairwise :
    ∀ (cls : List (List Nat)) (s : Nat),
      List.Pairwise (· < ·) (endsOf cls s)
  | [], _ => by rw [endsOf]; exact List.Pairwise.nil
  | cl :: cls, s => by
    rw [endsOf]
    rcases hcl : cl.isEmpty with _ | _
    · simp only [Bool.false_eq_true, if_false]
      refine List.pairwise_cons.mpr ⟨fun e he => ?_,
        endsOf_pairwise cls (s + cl.length)⟩
      have := endsOf_ge cls (s + cl.length) e he
      have hL : cl.length ≥ 1 := by
        rcases cl with _ | _
        · simp at hcl
        · simp
      omega
    · simp only [if_true]
      exact endsOf_pairwise cls s

end Hex.GraphIso.Nauty
