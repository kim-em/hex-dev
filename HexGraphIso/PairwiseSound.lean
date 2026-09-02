/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Pairwise

public section

/-!
Soundness of the pairwise individualization-refinement decision.

The central relation is `Compat φ P Q`: the forward permutation maps the
cells of `P` onto the cells of `Q` position by position, as multisets.
Every step of the search transports it: refinement rounds preserve it
(signature counts are isomorphism-invariant), diverging shapes refute it,
individualizing `v` against `φ v` preserves it, and at a discrete pair it
pins `φ` to the induced transporter. The two verdict theorems
`decideIso?_isomorphic` and `decideIso?_not_isomorphic` follow.
-/

namespace Hex.GraphIso.Pairwise

variable {n k : Nat}

/-- Positionwise relation between two lists. -/
inductive Rel2 (R : α → β → Prop) : List α → List β → Prop
  | nil : Rel2 R [] []
  | cons {a b l m} : R a b → Rel2 R l m → Rel2 R (a :: l) (b :: m)

namespace Rel2

theorem length_eq {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → l.length = m.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simpa using length_eq h

theorem append {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, Rel2 R l₁ m₁ → Rel2 R l₂ m₂ →
      Rel2 R (l₁ ++ l₂) (m₁ ++ m₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons h h₁, h₂ => .cons h (append h₁ h₂)

theorem flatMap {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ}
    (hfg : ∀ a b, R a b → Rel2 S (f a) (g b)) :
    ∀ {l : List α} {m : List β}, Rel2 R l m →
      Rel2 S (l.flatMap f) (m.flatMap g)
  | _, _, .nil => .nil
  | _, _, .cons h hrest => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact append (hfg _ _ h) (flatMap hfg hrest)

theorem getElem? {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → ∀ {i : Nat} {a : α},
      l[i]? = some a → ∃ b, m[i]? = some b ∧ R a b
  | _, _, .cons h hrest, 0, a => fun ha => ⟨_, rfl, by
      injection ha with ha
      exact ha ▸ h⟩
  | _, _, .cons h hrest, i + 1, a => fun ha => getElem? hrest ha
  | _, _, .nil, i, a => fun ha => by simp at ha

theorem mem_left {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → ∀ {a : α}, a ∈ l →
      ∃ b, b ∈ m ∧ R a b
  | _, _, .cons h hrest, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., h⟩
    · rcases mem_left hrest ha with ⟨b, hb, hr⟩
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem take {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → ∀ i,
      Rel2 R (l.take i) (m.take i)
  | _, _, .nil, _ => by simpa using Rel2.nil
  | _, _, .cons h hrest, 0 => .nil
  | _, _, .cons h hrest, i + 1 => by
    rw [List.take_succ_cons, List.take_succ_cons]
    exact .cons h (take hrest i)

theorem drop {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → ∀ i,
      Rel2 R (l.drop i) (m.drop i)
  | _, _, .nil, _ => by simpa using Rel2.nil
  | _, _, .cons h hrest, 0 => .cons h hrest
  | _, _, .cons h hrest, i + 1 => by
    rw [List.drop_succ_cons, List.drop_succ_cons]
    exact drop hrest i

theorem of_maps {R : γ → δ → Prop} {f : α → γ} {g : α → δ}
    (h : ∀ a, R (f a) (g a)) : ∀ (l : List α), Rel2 R (l.map f) (l.map g)
  | [] => .nil
  | a :: l => .cons (h a) (of_maps h l)

end Rel2

/-- The forward permutation `φ` carries the cells of `P` onto the cells
of `Q`, position by position, as multisets. -/
def Compat (φ : Perm n) (P Q : Cells n) : Prop :=
  Rel2 (fun c d => List.Perm (c.map φ.get) d) P Q

/-- Every vertex lies in some cell. -/
def Covers (P : Cells n) : Prop :=
  ∀ v : Fin n, ∃ c, c ∈ P ∧ v ∈ c

/-- Adjacency transport along a forward permutation. -/
def AdjMap (G H : Graph n) (φ : Perm n) : Prop :=
  ∀ i j, H.adj (φ.get i) (φ.get j) = G.adj i j

/-! # Signature transport -/

theorem sig_transport {G H : Graph n} {φ : Perm n} (hadj : AdjMap G H φ)
    {P Q : Cells n} (h : Compat φ P Q) (v : Fin n) :
    sig H Q (φ.get v) = sig G P v := by
  unfold sig
  induction h with
  | nil => rfl
  | cons hcd hrest ih =>
    rw [List.map_cons, List.map_cons, ih]
    refine congrArg (· :: _) ?_
    rename_i c d _ _
    rw [← hcd.countP_eq, List.countP_map]
    refine List.countP_congr fun u hu => ?_
    simp only [Function.comp_apply, hadj v u]

theorem cellSigs_transport {G H : Graph n} {φ : Perm n} (hadj : AdjMap G H φ)
    {P Q : Cells n} (h : Compat φ P Q) {c d : List (Fin n)}
    (hcd : List.Perm (c.map φ.get) d) :
    cellSigs H Q d = cellSigs G P c := by
  unfold cellSigs
  refine congrArg dedupAdj (sortLe_eq_of_perm ?_)
  have h1 : List.Perm (d.map (sig H Q)) ((c.map φ.get).map (sig H Q)) :=
    (hcd.map _).symm
  have h2 : (c.map φ.get).map (sig H Q) = c.map (sig G P) := by
    rw [List.map_map]
    exact List.map_congr_left fun v _ => sig_transport hadj h v
  exact h2 ▸ h1

theorem splitCell_transport {G H : Graph n} {φ : Perm n} (hadj : AdjMap G H φ)
    {P Q : Cells n} (h : Compat φ P Q) {c d : List (Fin n)}
    (hcd : List.Perm (c.map φ.get) d) :
    Rel2 (fun c' d' => List.Perm (c'.map φ.get) d')
      (splitCell G P c) (splitCell H Q d) := by
  unfold splitCell
  rw [cellSigs_transport hadj h hcd]
  refine Rel2.of_maps (fun s => ?_) (cellSigs G P c)
  have h1 : (c.map φ.get).filter (fun w => sig H Q w == s)
      = (c.filter fun v => sig G P v == s).map φ.get := by
    rw [List.filter_map]
    refine congrArg _ (List.filter_congr fun v _ => ?_)
    simp only [Function.comp_apply, sig_transport hadj h v]
  exact h1 ▸ hcd.filter (fun w => sig H Q w == s)

/-! # Refinement rounds -/

theorem refineRound_compat {G H : Graph n} {φ : Perm n} (hadj : AdjMap G H φ)
    {P Q : Cells n} (h : Compat φ P Q) :
    Compat φ (refineRound G P) (refineRound H Q) :=
  Rel2.flatMap (fun _ _ hcd => splitCell_transport hadj h hcd) h

theorem refineRounds_compat {G H : Graph n} {φ : Perm n} (hadj : AdjMap G H φ) :
    ∀ (r : Nat) {P Q : Cells n}, Compat φ P Q →
      Compat φ (refineRounds G r P) (refineRounds H r Q)
  | 0, _, _, h => h
  | r + 1, _, _, h => refineRounds_compat hadj r (refineRound_compat hadj h)

theorem shape_transport {G H : Graph n} {φ : Perm n} (hadj : AdjMap G H φ)
    {P Q : Cells n} (h : Compat φ P Q) :
    shape G P = shape H Q := by
  refine List.ext_getElem? fun i => ?_
  rw [shape, shape, List.getElem?_map, List.getElem?_map]
  cases hP : P[i]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hP
    rw [List.getElem?_eq_none (h.length_eq ▸ hP)]
    rfl
  | some c =>
    rcases h.getElem? hP with ⟨d, hQ, hcd⟩
    rw [hQ, Option.map_some, Option.map_some]
    refine congrArg some ?_
    refine Prod.ext ?_ ?_
    · simpa using hcd.length_eq
    · exact (cellSigs_transport hadj h hcd).symm

/-! # Individualization -/

/-- `List.erase` commutes with mapping an injective function. -/
theorem map_erase_inj {f : Fin n → Fin n}
    (hinj : ∀ a b, f a = f b → a = b) (a : Fin n) :
    ∀ (l : List (Fin n)), (l.erase a).map f = (l.map f).erase (f a)
  | [] => rfl
  | x :: l => by
    rw [List.erase_cons, List.map_cons, List.erase_cons]
    rcases hxa : x == a with _ | _
    · have hfxa : (f x == f a) = false := by
        rcases hb : f x == f a with _ | _
        · rfl
        · exact absurd (beq_iff_eq.mpr (hinj x a (beq_iff_eq.mp hb)))
            (hxa ▸ Bool.false_ne_true)
      simp only [hfxa, Bool.false_eq_true, ite_false, List.map_cons,
        map_erase_inj hinj a l]
    · have hxa' : x = a := beq_iff_eq.mp hxa
      subst hxa'
      simp

theorem mem_of_compat_cell {φ : Perm n} {c d : List (Fin n)}
    (hcd : List.Perm (c.map φ.get) d) {v : Fin n} (hv : v ∈ c) :
    φ.get v ∈ d :=
  hcd.mem_iff.mp (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem individualize_compat {φ : Perm n} {P Q : Cells n} (h : Compat φ P Q)
    {i : Nat} {c d : List (Fin n)} (hP : P[i]? = some c) (hQ : Q[i]? = some d)
    (hcd : List.Perm (c.map φ.get) d) (v : Fin n) :
    Compat φ (individualize P i v) (individualize Q i (φ.get v)) := by
  unfold individualize
  rw [hP, hQ]
  simp only [Option.getD_some]
  refine Rel2.append (Rel2.append (h.take i) ?_) (h.drop (i + 1))
  refine Rel2.cons ?_ (Rel2.cons ?_ Rel2.nil)
  · simp
  · rw [map_erase_inj (fun a b => φ.get_inj) v c]
    exact hcd.erase (φ.get v)

/-! # Coverage -/

theorem covers_refineRound {G : Graph n} {P : Cells n} (h : Covers P) :
    Covers (refineRound G P) := by
  intro v
  rcases h v with ⟨c, hc, hvc⟩
  refine ⟨c.filter fun u => sig G P u == sig G P v, ?_, ?_⟩
  · rw [refineRound, List.mem_flatMap]
    refine ⟨c, hc, ?_⟩
    rw [splitCell, List.mem_map]
    refine ⟨sig G P v, ?_, ?_⟩
    · rw [cellSigs, mem_dedupAdj]
      exact (perm_sortLe _).mem_iff.mpr (List.mem_map.mpr ⟨v, hvc, rfl⟩)
    · rfl
  · rw [List.mem_filter]
    exact ⟨hvc, beq_self_eq_true _⟩

theorem covers_refineRounds {G : Graph n} :
    ∀ (r : Nat) {P : Cells n}, Covers P → Covers (refineRounds G r P)
  | 0, _, h => h
  | r + 1, _, h => covers_refineRounds r (covers_refineRound h)

theorem covers_individualize {P : Cells n} (h : Covers P) {i : Nat}
    {c : List (Fin n)} (hP : P[i]? = some c) (v : Fin n) :
    Covers (individualize P i v) := by
  intro u
  rcases h u with ⟨e, he, hue⟩
  rcases List.mem_iff_getElem?.mp he with ⟨j, hj⟩
  unfold individualize
  rw [hP]
  simp only [Option.getD_some]
  rcases Nat.lt_trichotomy j i with hji | rfl | hij
  · refine ⟨e, ?_, hue⟩
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
    exact List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_take_of_lt hji]; exact hj⟩
  · have hec : e = c := by
      rw [hj] at hP
      injection hP
    subst hec
    rcases Decidable.em (u = v) with rfl | hne
    · exact ⟨[u], List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (List.mem_cons_self ..)))), List.mem_singleton.mpr rfl⟩
    · refine ⟨e.erase v, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), ?_⟩
      exact (List.mem_erase_of_ne hne).mpr hue
  · refine ⟨e, ?_, hue⟩
    refine List.mem_append.mpr (Or.inr ?_)
    refine List.mem_iff_getElem?.mpr ⟨j - (i + 1), ?_⟩
    rw [List.getElem?_drop]
    rw [Nat.add_sub_cancel' hij]
    exact hj

/-! # Discrete pairs pin the transporter -/

theorem firstBig_go_none {P : Cells n} :
    ∀ {i : Nat}, firstBig.go (n := n) i P = none → ∀ c ∈ P, c.length ≤ 1 := by
  induction P with
  | nil => intro i _ c hc; simp at hc
  | cons c rest ih =>
    intro i hgo e he
    rw [firstBig.go] at hgo
    split at hgo
    · simp at hgo
    · next hlen =>
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · exact ih hgo e he

theorem discrete_of_firstBig_none {P : Cells n} (h : firstBig P = none) :
    ∀ c ∈ P, c.length ≤ 1 :=
  firstBig_go_none h

theorem firstBig_go_some {P : Cells n} :
    ∀ {i j : Nat} {c : List (Fin n)}, firstBig.go (n := n) i P = some (j, c) →
      ∃ off, j = i + off ∧ P[off]? = some c ∧ 2 ≤ c.length := by
  induction P with
  | nil => intro i j c h; rw [firstBig.go] at h; exact absurd h (by simp)
  | cons e rest ih =>
    intro i j c h
    rw [firstBig.go] at h
    split at h
    · next hlen =>
        injection h with h
        injection h with h1 h2
        subst h1
        subst h2
        exact ⟨0, by omega, rfl, hlen⟩
    · rcases ih h with ⟨off, hj, hoff, hlen⟩
      exact ⟨off + 1, by omega, by simpa using hoff, hlen⟩

theorem firstBig_spec {P : Cells n} {i : Nat} {c : List (Fin n)}
    (h : firstBig P = some (i, c)) : P[i]? = some c ∧ 2 ≤ c.length := by
  rcases firstBig_go_some h with ⟨off, hj, hoff, hlen⟩
  subst hj
  simpa using ⟨hoff, hlen⟩

theorem Rel2.zip_mem {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → ∀ {a b}, (a, b) ∈ l.zip m → R a b
  | _, _, .nil, a, b => fun hab => by simp at hab
  | _, _, .cons h hrest, a, b => fun hab => by
    rw [List.zip_cons_cons, List.mem_cons] at hab
    rcases hab with hab | hab
    · injection hab with h1 h2
      subst h1; subst h2
      exact h
    · exact Rel2.zip_mem hrest hab

theorem Rel2.mem_zip_left {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Rel2 R l m → ∀ {a}, a ∈ l →
      ∃ b, (a, b) ∈ l.zip m
  | _, _, .nil, a => fun ha => by simp at ha
  | _, _, .cons h hrest, a => fun ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self ..⟩
    · rcases Rel2.mem_zip_left hrest ha with ⟨b, hb⟩
      exact ⟨b, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb⟩

/-- A cell of length at most one containing `v` is `[v]`. -/
theorem eq_singleton_of_small {c : List (Fin n)} (hlen : c.length ≤ 1)
    {v : Fin n} (hv : v ∈ c) : c = [v] := by
  cases c with
  | nil => simp at hv
  | cons x rest =>
    cases rest with
    | nil =>
      rcases List.mem_singleton.mp hv with rfl
      rfl
    | cons y rest => simp at hlen

/-- A list permutation-equal to a singleton is that singleton. -/
theorem eq_singleton_of_perm {d : List (Fin n)} {w : Fin n}
    (h : List.Perm [w] d) : d = [w] := by
  cases d with
  | nil => exact absurd h.symm.nil_eq (by simp)
  | cons x rest =>
    cases rest with
    | nil =>
      rcases List.mem_singleton.mp (h.mem_iff.mp (List.mem_singleton.mpr rfl))
        with rfl
      rfl
    | cons y rest =>
      have := h.length_eq
      simp at this

theorem inducedFun_eq {φ : Perm n} {P Q : Cells n} (h : Compat φ P Q)
    (hdisc : ∀ c ∈ P, c.length ≤ 1) (hcov : Covers P) (v : Fin n) :
    inducedFun P Q v = φ.get v := by
  unfold inducedFun
  rcases hfind : (P.zip Q).find? (fun cd => cd.1.contains v) with _ | ⟨c, d⟩
  · exfalso
    rcases hcov v with ⟨c, hc, hvc⟩
    rcases h.mem_zip_left hc with ⟨d, hzip⟩
    have := List.find?_eq_none.mp hfind (c, d) hzip
    simp only [List.contains_iff_mem] at this
    exact this hvc
  · have hvc : v ∈ c := by
      have := List.find?_some hfind
      simpa [List.contains_iff_mem] using this
    have hcP : c ∈ P := (List.of_mem_zip (List.mem_of_find?_eq_some hfind)).1
    have hc1 : c = [v] := eq_singleton_of_small (hdisc c hcP) hvc
    subst hc1
    have hrel := h.zip_mem (List.mem_of_find?_eq_some hfind)
    simp only [List.map_singleton] at hrel
    have hd : d = [φ.get v] := eq_singleton_of_perm hrel
    rw [hfind, hd]

theorem inducedPerm_eq {φ : Perm n} {P Q : Cells n} (h : Compat φ P Q)
    (hdisc : ∀ c ∈ P, c.length ≤ 1) (hcov : Covers P) :
    inducedPerm P Q = φ := by
  unfold inducedPerm permOfNatArray?
  have hsz : (Hex.Array.ofFn' fun v : Fin n => (inducedFun P Q v).val).size = n := by
    rw [Hex.Array.ofFn'_eq_ofFn, Array.size_ofFn]
  have hbound : ∀ i, (hi : i <
      (Hex.Array.ofFn' fun v : Fin n => (inducedFun P Q v).val).size) →
      (Hex.Array.ofFn' fun v : Fin n => (inducedFun P Q v).val)[i] < n := by
    intro i hi
    rw [Hex.Array.getElem_ofFn']
    exact (inducedFun P Q _).isLt
  rw [dite_eq_left ⟨hsz, hbound⟩]
  have hvec : (Hex.Vector.ofFn' fun i : Fin n =>
      (⟨(Hex.Array.ofFn' fun v : Fin n => (inducedFun P Q v).val)[i.val]'(hsz.symm ▸ i.isLt),
        hbound i.val (hsz.symm ▸ i.isLt)⟩ : Fin n)) = φ.vec := by
    refine Vector.ext fun i hi => ?_
    simp only [Hex.Vector.getElem_ofFn']
    refine Fin.ext ?_
    simp only [Hex.Array.getElem_ofFn']
    rw [inducedFun_eq h hdisc hcov]
    rfl
  rw [hvec, Perm.ofVector?, dite_eq_left ⟨φ.nodup, φ.complete⟩]
  simp only [Option.getD_some]

/-! # The search verdicts -/

variable {G H : Colored n k}

theorem search_false {φ : Perm n} (hiso : IsIso G H φ) :
    ∀ (budget : Nat) {stack : List (Cells n × Cells n)},
      search G H budget stack = some false →
      ∀ pq ∈ stack, Compat φ pq.1 pq.2 → Covers pq.1 → False := by
  have hadj : AdjMap G.graph H.graph φ := hiso.adj_eq
  intro budget
  induction budget with
  | zero =>
    intro stack hrun
    rw [search] at hrun
    simp at hrun
  | succ budget ih =>
    intro stack hrun pq hmem hc hcov
    match stack, hmem with
    | (P, Q) :: stack, hmem =>
      simp only [search] at hrun
      split at hrun
      · next hne =>
          rcases List.mem_cons.mp hmem with rfl | htail
          · exact hne (shape_transport hadj (refineRounds_compat hadj _ hc))
          · exact ih hrun pq htail hc hcov
      · split at hrun
        · next hnone =>
            split at hrun
            · simp at hrun
            · next hcheck =>
                rcases List.mem_cons.mp hmem with rfl | htail
                · refine hcheck ?_
                  rw [inducedPerm_eq (refineRounds_compat hadj _ hc)
                    (discrete_of_firstBig_none hnone)
                    (covers_refineRounds _ hcov)]
                  exact (checkIso_iff G H φ).mpr hiso
                · exact ih hrun pq htail hc hcov
        · next i c hbig =>
            match c, hrun with
            | [], hrun =>
              rcases List.mem_cons.mp hmem with rfl | htail
              · rcases firstBig_spec hbig with ⟨-, hlen⟩
                simp at hlen
              · exact ih hrun pq htail hc hcov
            | v :: rest, hrun =>
              rcases List.mem_cons.mp hmem with rfl | htail
              · rcases firstBig_spec hbig with ⟨hP, -⟩
                have hc' := refineRounds_compat hadj (n + 1) hc
                have hcov' := covers_refineRounds (G := G.graph) (n + 1) hcov
                rcases hc'.getElem? hP with ⟨d, hQ, hcd⟩
                have hvd : φ.get v ∈ d :=
                  mem_of_compat_cell hcd (List.mem_cons_self ..)
                refine ih hrun
                  (individualize (refineRounds G.graph (n + 1) P) i v,
                    individualize (refineRounds H.graph (n + 1) Q) i
                      (φ.get v)) ?_ ?_ ?_
                · refine List.mem_append.mpr (Or.inl ?_)
                  rw [children, hQ]
                  simp only [Option.getD_some]
                  exact List.mem_map.mpr ⟨φ.get v, hvd, rfl⟩
                · exact individualize_compat hc' hP hQ hcd v
                · exact covers_individualize hcov' hP v
              · exact ih hrun pq (List.mem_append.mpr (Or.inr htail)) hc hcov

theorem search_true :
    ∀ (budget : Nat) {stack : List (Cells n × Cells n)},
      search G H budget stack = some true → Isomorphic G H := by
  intro budget
  induction budget with
  | zero =>
    intro stack hrun
    rw [search] at hrun
    simp at hrun
  | succ budget ih =>
    intro stack hrun
    match stack, hrun with
    | [], hrun =>
      rw [search] at hrun
      simp at hrun
    | (P, Q) :: stack, hrun =>
      simp only [search] at hrun
      split at hrun
      · exact ih hrun
      · split at hrun
        · split at hrun
          · next hcheck =>
              exact Isomorphic.intro _ ((checkIso_iff G H _).mp hcheck)
          · exact ih hrun
        · split at hrun
          · exact ih hrun
          · exact ih hrun

/-! # The root partition -/

theorem colorCells_covers (G : Colored n k) : Covers (colorCells G) := by
  intro v
  refine ⟨_, List.mem_map.mpr ⟨(G.coloring.cells[v] : Fin k).val,
    List.mem_range.mpr (G.coloring.cells[v] : Fin k).isLt, rfl⟩, ?_⟩
  rw [List.mem_filter]
  exact ⟨List.mem_finRange v, beq_self_eq_true _⟩

theorem colorCells_compat {φ : Perm n} (hiso : IsIso G H φ) :
    Compat φ (colorCells G) (colorCells H) := by
  unfold colorCells Compat
  refine Rel2.of_maps (fun c => ?_) (List.range k)
  have hnodupG : ((List.finRange n).filter
      fun v => (G.coloring.cells[v] : Fin k).val == c).Nodup :=
    List.filter_sublist.nodup (Reference.nodup_finRange n)
  have hnodupH : ((List.finRange n).filter
      fun v => (H.coloring.cells[v] : Fin k).val == c).Nodup :=
    List.filter_sublist.nodup (Reference.nodup_finRange n)
  have hnodupMap : (((List.finRange n).filter
      fun v => (G.coloring.cells[v] : Fin k).val == c).map φ.get).Nodup := by
    refine List.pairwise_map.mpr (hnodupG.imp ?_)
    intro a b hne heq
    exact hne (φ.get_inj heq)
  refine (List.perm_ext_iff_of_nodup hnodupMap hnodupH).mpr ?_
  intro w
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    beq_iff_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← hv]
    exact congrArg Fin.val (hiso.cells_eq v)
  · intro hw
    rcases φ.get_surj w with ⟨v, rfl⟩
    refine ⟨v, ?_, rfl⟩
    rw [← hw]
    exact (congrArg Fin.val (hiso.cells_eq v)).symm

/-! # The bounded decision -/

theorem decideIso?_isomorphic {limits : SearchLimits}
    (h : decideIso? limits G H = some true) : Isomorphic G H := by
  unfold decideIso? at h
  exact search_true limits.maxNodes h

theorem decideIso?_not_isomorphic {limits : SearchLimits}
    (h : decideIso? limits G H = some false) : ¬ Isomorphic G H := by
  intro hiso
  rcases hiso.elim with ⟨φ, hφ⟩
  unfold decideIso? at h
  exact search_false hφ limits.maxNodes h (colorCells G, colorCells H)
    (List.mem_singleton.mpr rfl) (colorCells_compat hφ) (colorCells_covers G)

end Hex.GraphIso.Pairwise
