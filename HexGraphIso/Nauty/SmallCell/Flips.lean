/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Descent
import all HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
The flip data at triple and pair target cells: for either member of
a small cell, a row-preserving self-symmetry of the node carrying it
to the other.
-/

/-!
The first guard branch (`defect ≤ nontrivial + 1`) forces every cell
of the partition to be a singleton, a pair, or one triple, and any two
size-three cells to coincide. On that shape these lemmas prove the
triple analogues of the pair flip theory:

* `triple_const`: the triple's members have identical bits at every
  member of any other cell of size at most two. The count into a
  singleton is the adjacency bit, and the count into a pair is twice
  it by `pair_odd_eq`'s both-or-neither;
* `triple_internal`: the induced graph on the triple is empty or
  complete. The off-diagonal bits are all equal, by the three row-sum
  equalities of equitability (a one-regular graph on three vertices
  is impossible);
* `triple_flip_rows`: the transposition of any two triple members,
  fixing every other vertex, preserves the adjacency rows. Unlike the
  pair flip no matching closure is needed: every other cell is small,
  so the triple's relations to it are constant across the triple.

The surjectivity hypothesis the flip theorems consume is
`labInj_surj` in `Equitable/Step`. Also here: the transposition's
self-equivalence (`cellsPerm_self_tripleSwap`/`stPerm_self_tripleSwap`,
stating that the mapped labelling is cell-contents equivalent to the
original), the generalized single-deviation theorem
(`deviation_leafRows_self`: any row-preserving self-symmetry of a node
carrying one child's individualized vertex to another's mirrors
discrete descents with equal leaf rows, which is the form both the
pair and the triple deviation use), and its packaged triple instance
(`triple_deviation_leafRows`, which constructs the concrete
transposition and discharges every hypothesis from `IterOk`,
equitability and the first-branch shape). The pair-matching closure
`PairReach` and its position toolkit (start-determinacy,
start-never-second, closure members are pairs, distinct pairs
disjoint) follow.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- Two cells of the partition list sharing a position coincide. -/
theorem cells_eq_of_shared {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {p q : Nat × Nat} (hp : p ∈ cells ptn level nn)
    (hq : q ∈ cells ptn level nn)
    {j : Nat} (hjp1 : p.1 ≤ j) (hjp2 : j ≤ p.2)
    (hjq1 : q.1 ≤ j) (hjq2 : j ≤ q.2) : p = q := by
  have hIp := cells_isCell hnn hend _ hp
  have hIq := cells_isCell hnn hend _ hq
  have hple := cells_le _ hp
  have hqle := cells_le _ hq
  rcases isCell_disj_or_eq hIp hIq with ⟨h1, h2⟩ | hd | hd
  · obtain ⟨pa, pb⟩ := p
    obtain ⟨qa, qb⟩ := q
    simp only at h1 h2 hple hqle
    have : pb = qb := by omega
    rw [h1, this]
  · omega
  · omega

/-! # List toolkit -/

private theorem mapNodup {f : Nat → Nat}
    (hinj : ∀ a b, f a = f b → a = b) :
    ∀ (l : List Nat), l.Nodup → (l.map f).Nodup
  | [], _ => by simp
  | a :: t, h => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at h
    refine ⟨fun hmem => ?_, mapNodup hinj t h.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    rw [hinj b a hfb] at hb
    exact h.1 hb

/-- A duplicate-free list included in a list of no greater length is a
permutation of it. -/
theorem perm_of_nodup_subset :
    ∀ (l₁ l₂ : List Nat), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) →
      l₂.length ≤ l₁.length → l₁.Perm l₂
  | [], l₂, _, _, hlen => by
    have h0 : l₂.length = 0 := by
      simp only [List.length_nil] at hlen
      omega
    rw [List.length_eq_zero_iff.mp h0]
  | a :: t, l₂, hnd, hsub, hlen => by
    have ha : a ∈ l₂ := hsub a List.mem_cons_self
    have hperm2 := List.perm_cons_erase ha
    rw [List.nodup_cons] at hnd
    have hsub' : ∀ x ∈ t, x ∈ l₂.erase a := by
      intro x hx
      have hxl : x ∈ l₂ := hsub x (List.mem_cons_of_mem _ hx)
      have hxa : x ≠ a := fun hcon => hnd.1 (hcon ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr hxl
    have hlen2 : l₂.length = (l₂.erase a).length + 1 :=
      hperm2.length_eq
    have hrec := perm_of_nodup_subset t (l₂.erase a) hnd.2 hsub'
      (by simp only [List.length_cons] at hlen; omega)
    exact (hrec.cons a).trans hperm2.symm

/-- Sums are invariant under permutation. -/
theorem sum_of_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [List.sum_cons, List.sum_cons, ih]
  | swap a b l =>
    rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons]
    omega
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

private theorem countP_pos_extract {p : Nat → Bool} :
    ∀ (l : List Nat), 0 < l.countP p → ∃ w ∈ l, p w = true
  | a :: t, h => by
    rw [List.countP_cons] at h
    rcases Decidable.em (p a = true) with hpa | hpa
    · exact ⟨a, List.mem_cons_self, hpa⟩
    · rw [ite_eq_right hpa] at h
      obtain ⟨w, hw, hpw⟩ := countP_pos_extract t (by omega)
      exact ⟨w, List.mem_cons_of_mem _ hw, hpw⟩

/-- A permutation of `range k` from `k` distinct bounded values. -/
theorem range_perm_of_distinct {l : List Nat} {k : Nat}
    (hlen : l.length = k) (hnd : l.Nodup)
    (hbd : ∀ x ∈ l, x < k) : l.Perm (List.range k) :=
  perm_of_nodup_subset l (List.range k) hnd
    (fun x hx => List.mem_range.mpr (hbd x hx))
    (by rw [List.length_range, hlen]; exact Nat.le_refl _)

/-- A sum over `range k` rewritten through `k` distinct bounded
indices. -/
theorem sum_range_of_distinct {l : List Nat} {k : Nat}
    (F : Nat → Nat) (hlen : l.length = k) (hnd : l.Nodup)
    (hbd : ∀ x ∈ l, x < k) :
    ((List.range k).map F).sum = (l.map F).sum :=
  (sum_of_perm ((range_perm_of_distinct hlen hnd hbd).map F)).symm

/-! # The generic setwise self-equivalence -/

private theorem segN_nodup {lab : Array Nat} {n lo : Nat}
    (hinj : LabInj lab n) :
    ∀ len, lo + len ≤ n → (segN lab lo len).Nodup := by
  intro len
  induction len generalizing lo with
  | zero => intro _; rw [segN_zero]; simp
  | succ len ih =>
    intro hbd
    rw [segN_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih (lo := lo + 1) (by omega)⟩
    obtain ⟨o, ho, heq⟩ := mem_segN_iff.mp hmem
    have := hinj (lo + 1 + o) lo (by omega) (by omega) heq
    omega

/-- A renaming permuting every cell's members within the cell is a
cell-contents self-equivalence of the labelling. -/
theorem cellsPerm_self_setwise {lab ptn : Array Nat} {level : Nat}
    {σ : Renaming n}
    (hps : ptn.size = n) (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : LabInj lab n)
    (hset : ∀ p ∈ cells ptn level n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        σ.toFun lab[p.1 + o]! = lab[p.1 + o']!) :
    cellsPerm ptn level lab (lab.map σ.toFun) := by
  intro α len hIs
  rcases Decidable.em (α < n) with han | han
  · have hcross : α + len ≤ n := by
      have := isCell_no_cross hend hIs (by omega)
      omega
    have hlen0 : 0 < len := hIs.1
    have hmem : (α, α + len - 1) ∈ cells ptn level n :=
      mem_cells_of_isCell (by omega) hend hIs han (by omega)
    have hsegm : segN (lab.map σ.toFun) α len =
        (segN lab α len).map σ.toFun := segN_map (by omega)
    rw [hsegm]
    refine (perm_of_nodup_subset _ _
      (mapNodup σ.inj _ (segN_nodup hinj len hcross)) ?_ ?_).symm
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hz
      obtain ⟨o', ho', heq⟩ := hset _ hmem o (by omega)
      rw [heq]
      exact mem_segN_iff.mpr ⟨o', by omega, rfl⟩
    · rw [segN_length, List.length_map, segN_length]
      exact Nat.le_refl _
  · have hlen1 : len = 1 := isCell_oob hIs (by omega)
    rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero,
      getElem!_oob (by omega : lab.size ≤ α),
      getElem!_oob (by rw [Array.size_map]; omega :
        (lab.map σ.toFun).size ≤ α)]

/-- The setwise self-equivalence packaged as `StPerm`, for a raw
involution. -/
theorem stPerm_self_setwise {f : Nat → Nat} {st : RefineSt n}
    {level : Nat}
    (hok : StOk n level st) (hinj : LabInj st.lab n)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hset : ∀ p ∈ cells st.ptn level n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        f st.lab[p.1 + o]! = st.lab[p.1 + o']!) :
    StPerm level st (mapSt (renamingOfFlip f n hfb hinvol) st) := by
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hok.labOk i (by rw [hok.labSize]; omega)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (st.lab.map _).size = st.lab.size
    rw [Array.size_map]
  · show cellsPerm st.ptn level st.lab
      (st.lab.map (renamingOfFlip f n hfb hinvol).toFun)
    refine cellsPerm_self_setwise hok.ptnSize hok.labSize hok.ptnEnd
      hinj ?_
    intro p hp o ho
    obtain ⟨o', ho', heq⟩ := hset p hp o ho
    have hbd : p.2 < st.ptn.size :=
      cells_bound (by rw [hok.ptnSize]; exact Nat.le_refl _)
        hok.ptnEnd _ hp
    have hle := cells_le _ hp
    rw [hok.ptnSize] at hbd
    refine ⟨o', ho', ?_⟩
    rw [renamingOfFlip_at hfb hinvol (hlb (p.1 + o) (by omega))]
    exact heq


/-- A vertex map sends every cell into itself. -/
@[expose] def CellMap (st : RefineSt n) (level : Nat) (f : Nat → Nat) : Prop :=
  ∀ p ∈ cells st.ptn level n, ∀ o, o < p.2 + 1 - p.1 →
    ∃ o', o' < p.2 + 1 - p.1 ∧ f st.lab[p.1 + o]! = st.lab[p.1 + o']!

/-- Composing maps that preserve each cell preserves each cell. -/
theorem CellMap.comp {st : RefineSt n} {level : Nat} {f g : Nat → Nat}
    (hf : CellMap st level f) (hg : CellMap st level g) :
    CellMap st level (fun v => f (g v)) := by
  intro p hp o ho
  obtain ⟨a, ha, he⟩ := hg p hp o ho
  obtain ⟨b, hb, he'⟩ := hf p hp a ha
  exact ⟨b, hb, (congrArg f he).trans he'⟩

/-- Swapping two members of one cell preserves all cells. -/
theorem sw1_cells {st : RefineSt n} {level c e a b : Nat}
    (hok : StOk n level st) (hinj : LabInj st.lab n)
    (hc : (c, e) ∈ cells st.ptn level n)
    (ha : a ≤ e - c) (hb : b ≤ e - c) (hab : a ≠ b) :
    CellMap st level (sw1 st.lab[c + a]! st.lab[c + b]!) := by
  have hpsz := hok.ptnSize
  have hce := cells_le _ hc
  have he : e < n := by
    have := cells_bound (by omega) hok.ptnEnd _ hc
    rw [hok.ptnSize] at this
    exact this
  have huv : st.lab[c + a]! ≠ st.lab[c + b]! := by
    intro h
    have := hinj _ _ (by omega) (by omega) h
    omega
  intro p hp o ho
  have hpbd : p.2 < n := by
    have := cells_bound (by omega) hok.ptnEnd _ hp
    rw [hok.ptnSize] at this
    exact this
  have hple := cells_le _ hp
  have hsame : ∀ t, t ≤ e - c → st.lab[p.1 + o]! = st.lab[c + t]! → p = (c, e) := by
    intro t ht h
    have hpos := hinj _ _ (by omega) (by omega) h
    exact cells_eq_of_shared (by omega) hok.ptnEnd hp hc
      (j := p.1 + o) (by omega) (by omega) (by omega) (by omega)
  by_cases hua : st.lab[p.1 + o]! = st.lab[c + a]!
  · have hpc := hsame a ha hua
    subst p
    exact ⟨b, by omega, by rw [hua, sw1_u]⟩
  by_cases hub : st.lab[p.1 + o]! = st.lab[c + b]!
  · have hpc := hsame b hb hub
    subst p
    exact ⟨a, by omega, by rw [hub, sw1_v huv]⟩
  exact ⟨o, ho, sw1_fix hua hub⟩

/-- A disjoint double swap preserves cells when its two swaps do. -/
theorem sw2_cells {st : RefineSt n} {level u v x y : Nat}
    (h : Sw2Ok n u v x y)
    (h1 : CellMap st level (sw1 u v)) (h2 : CellMap st level (sw1 x y)) :
    CellMap st level (sw2 u v x y) := by
  simpa only [CellMap, sw2_comp h] using h1.comp h2

/-- A disjoint triple swap preserves cells when its three swaps do. -/
theorem sw3_cells {st : RefineSt n} {level u v x y a b : Nat}
    (h : Sw3Ok n u v x y a b)
    (h1 : CellMap st level (sw1 u v)) (h2 : CellMap st level (sw1 x y))
    (h3 : CellMap st level (sw1 a b)) : CellMap st level (sw3 u v x y a b) := by
  have h2ok : Sw2Ok n u v x y := by
    unfold Sw3Ok at h
    unfold Sw2Ok
    omega
  simpa only [CellMap, sw3_comp h] using (sw2_cells h2ok h1 h2).comp h3

/-! # The sharpened guard: sizes at most three, at most one triple -/

/-- In the first guard branch every cell has size at most three. -/
theorem size_le_three_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, q.2 + 1 - q.1 ≤ 3 := by
  intro q hq
  have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
    fun p hp => cells_le p hp
  have hsum : ((cells ptn level nn).map fun p =>
      p.2 + 1 - p.1).sum = nn := by
    rw [cells]
    have h := cells_go_sizes_sum hps hend nn 0 (by omega)
    rw [show nn - 0 = nn by omega] at h
    exact h
  have hsplit := sum_sizes_split (cells ptn level nn) hwf
  have hmem := sum_excess_ge_countP_add (cells ptn level nn) hwf hq
  have hq12 := hwf q hq
  omega

/-- In the first guard branch any two size-three cells coincide. -/
theorem triple_uniq_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, ∀ q' ∈ cells ptn level nn,
      q.2 + 1 - q.1 = 3 → q'.2 + 1 - q'.1 = 3 → q = q' := by
  intro q hq q' hq' hs hs'
  rcases Decidable.em (q = q') with heq | hne
  · exact heq
  · exfalso
    have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
      fun p hp => cells_le p hp
    have hsum : ((cells ptn level nn).map fun p =>
        p.2 + 1 - p.1).sum = nn := by
      rw [cells]
      have h := cells_go_sizes_sum hps hend nn 0 (by omega)
      rw [show nn - 0 = nn by omega] at h
      exact h
    have hsplit := sum_sizes_split (cells ptn level nn) hwf
    have hmem := sum_excess_ge_countP_add2 (cells ptn level nn) hwf
      hq hq' hne
    have hq12 := hwf q hq
    have hq12' := hwf q' hq'
    omega

/-- The first-branch shape: every cell is a singleton, a pair, or the
unique triple. -/
theorem cells_shape_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn,
      q.2 + 1 - q.1 = 1 ∨ q.2 + 1 - q.1 = 2 ∨
        (q.2 + 1 - q.1 = 3 ∧
          ∀ q' ∈ cells ptn level nn, q'.2 + 1 - q'.1 = 3 → q' = q) := by
  intro q hq
  have hle := size_le_three_of_defect_le hps hend hguard q hq
  have hge := cells_le q hq
  rcases Decidable.em (q.2 + 1 - q.1 = 3) with h3 | h3
  · exact Or.inr (Or.inr ⟨h3, fun q' hq' hs' =>
      triple_uniq_of_defect_le hps hend hguard q' hq' q hq hs' h3⟩)
  · rcases Decidable.em (q.2 + 1 - q.1 = 2) with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inl (by omega)

/-! # The triple against small cells

The triple's members have identical bits at every member of any other
cell of size at most two: the count into a singleton is the adjacency
bit, and the count into a pair is twice the bit at either member by
`pair_odd_eq`'s both-or-neither. -/

/-- Members of the triple cell have identical bits at every member of
any other cell of size at most two. -/
theorem triple_const {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {d : Nat} (hT : (d, d + 2) ∈ cells ptn level n)
    {c ce : Nat} (hC : (c, ce) ∈ cells ptn level n)
    (hsz : ce + 1 - c ≤ 2)
    {o o' w : Nat} (ho : o < 3) (ho' : o' < 3) (hw : w < ce + 1 - c) :
    (ctx.g[lab[d + o]!]!).mem lab[c + w]! =
      (ctx.g[lab[d + o']!]!).mem lab[c + w]! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hce : ce < n := by
    have := cells_bound (by omega) hend _ hC
    omega
  have hcce := cells_le _ hC
  have hcount := hE _ hT _ hC o o' (by omega) (by omega)
  rcases Decidable.em (ce = c) with hone | htwo
  · -- a singleton
    subst hone
    have hw0 : w = 0 := by omega
    subst hw0
    rw [worksetOf_singleton, VSet.cardInter_singleton,
      VSet.cardInter_singleton] at hcount
    rcases hb : (ctx.g[lab[d + o]!]!).mem lab[ce]! with _ | _ <;>
      rcases hb' : (ctx.g[lab[d + o']!]!).mem lab[ce]! with _ | _ <;>
        rw [hb, hb'] at hcount <;> simp_all
  · -- a pair
    have hpair : ce = c + 1 := by omega
    subst hpair
    have hC' : (c, c + 1) ∈ cells ptn level n := hC
    have hodd3 : (d + 2 + 1 - d) % 2 = 1 := by omega
    have hboth := pair_odd_eq hE hps hend hinj hlb hsymm hC' hT
      hodd3
    have hb_o := hboth o (by omega)
    have hb_o' := hboth o' (by omega)
    -- transport the pair-side equalities to the triple side
    have hto : o ≤ 2 := by omega
    have hto' : o' ≤ 2 := by omega
    have hself_o : (ctx.g[lab[d + o]!]!).mem lab[c]! =
        (ctx.g[lab[d + o]!]!).mem lab[c + 1]! := by
      rw [hsymm lab[d + o]! lab[c]! (hlb (d + o) (by omega))
          (hlb c (by omega)),
        hsymm lab[d + o]! lab[c + 1]! (hlb (d + o) (by omega))
          (hlb (c + 1) (by omega))]
      exact hb_o
    have hself_o' : (ctx.g[lab[d + o']!]!).mem lab[c]! =
        (ctx.g[lab[d + o']!]!).mem lab[c + 1]! := by
      rw [hsymm lab[d + o']! lab[c]! (hlb (d + o') (by omega))
          (hlb c (by omega)),
        hsymm lab[d + o']! lab[c + 1]! (hlb (d + o') (by omega))
          (hlb (c + 1) (by omega))]
      exact hb_o'
    rw [count_into_cell hps hend hinj hC',
      count_into_cell hps hend hinj hC',
      show c + 1 + 1 - c = 2 by omega, sum_range_two,
      sum_range_two] at hcount
    simp only [Nat.add_zero] at hcount
    have hcnt_o : bitCnt ctx.g[lab[d + o]!]! lab[c]! =
        bitCnt ctx.g[lab[d + o]!]! lab[c + 1]! :=
      bitCnt_inj.mpr hself_o
    have hcnt_o' : bitCnt ctx.g[lab[d + o']!]! lab[c]! =
        bitCnt ctx.g[lab[d + o']!]! lab[c + 1]! :=
      bitCnt_inj.mpr hself_o'
    have hkey : bitCnt ctx.g[lab[d + o]!]! lab[c]! =
        bitCnt ctx.g[lab[d + o']!]! lab[c]! := by omega
    have hbit0 : (ctx.g[lab[d + o]!]!).mem lab[c]! =
        (ctx.g[lab[d + o']!]!).mem lab[c]! := bitCnt_inj.mp hkey
    rcases Decidable.em (w = 0) with rfl | hw1
    · exact hbit0
    · have hw1' : w = 1 := by omega
      subst hw1'
      rw [← hself_o, ← hself_o']
      exact hbit0

/-! # The triple's internal structure

The induced graph on the triple is empty or complete: the three
off-diagonal bits are all equal, forced by the row-sum equalities of
equitability, symmetry, and looplessness (a one-regular graph on three
vertices would need an odd handshake). -/

/-- All off-diagonal internal bits of the triple agree. -/
theorem triple_internal {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {d : Nat} (hT : (d, d + 2) ∈ cells ptn level n) :
    ∀ o o' u u', o < 3 → o' < 3 → u < 3 → u' < 3 → o ≠ o' → u ≠ u' →
      (ctx.g[lab[d + o]!]!).mem lab[d + o']! =
        (ctx.g[lab[d + u]!]!).mem lab[d + u']! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hbnd : ∀ o, o < 3 → d + o < n := by
    intro o ho
    omega
  -- the three row sums are equal
  have hrow : ∀ o o', o < 3 → o' < 3 →
      bitCnt ctx.g[lab[d + o]!]! lab[d + 0]! +
        bitCnt ctx.g[lab[d + o]!]! lab[d + 1]! +
        bitCnt ctx.g[lab[d + o]!]! lab[d + 2]! =
      bitCnt ctx.g[lab[d + o']!]! lab[d + 0]! +
        bitCnt ctx.g[lab[d + o']!]! lab[d + 1]! +
        bitCnt ctx.g[lab[d + o']!]! lab[d + 2]! := by
    intro o o' ho ho'
    have hcount := hE _ hT _ hT o o' (by omega) (by omega)
    rw [count_into_cell hps hend hinj hT,
      count_into_cell hps hend hinj hT,
      show d + 2 + 1 - d = 3 by omega, sum_range_three,
      sum_range_three] at hcount
    exact hcount
  -- the diagonal is zero
  have hdiag : ∀ o, o < 3 →
      bitCnt ctx.g[lab[d + o]!]! lab[d + o]! = 0 := by
    intro o ho
    exact bitCnt_eq_zero.mpr (hloop _ (hlb _ (hbnd o ho)))
  -- symmetry at the bit-count level
  have hsym : ∀ o o', o < 3 → o' < 3 →
      bitCnt ctx.g[lab[d + o]!]! lab[d + o']! =
        bitCnt ctx.g[lab[d + o']!]! lab[d + o]! := by
    intro o o' ho ho'
    exact bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (hbnd o ho)) (hlb _ (hbnd o' ho')))
  -- name the three off-diagonal counts
  have h01 := hrow 0 1 (by omega) (by omega)
  have h12 := hrow 1 2 (by omega) (by omega)
  rw [hdiag 0 (by omega), hdiag 1 (by omega)] at h01
  rw [hdiag 1 (by omega), hdiag 2 (by omega)] at h12
  rw [hsym 1 0 (by omega) (by omega)] at h01
  rw [hsym 1 0 (by omega) (by omega),
    hsym 2 0 (by omega) (by omega),
    hsym 2 1 (by omega) (by omega)] at h12
  -- h01 : 0 + c01 + c02 = c01 + 0 + c12  →  c02 = c12
  -- h12 : c01 + 0 + c12 = c02 + c12 + 0  →  c01 = c02
  have hle01 := bitCnt_le_one ctx.g[lab[d + 0]!]! lab[d + 1]!
  have hle02 := bitCnt_le_one ctx.g[lab[d + 0]!]! lab[d + 2]!
  have hle12 := bitCnt_le_one ctx.g[lab[d + 1]!]! lab[d + 2]!
  have hall : bitCnt ctx.g[lab[d + 0]!]! lab[d + 1]! =
      bitCnt ctx.g[lab[d + 0]!]! lab[d + 2]! ∧
      bitCnt ctx.g[lab[d + 0]!]! lab[d + 2]! =
      bitCnt ctx.g[lab[d + 1]!]! lab[d + 2]! := by omega
  -- every off-diagonal bit equals bit (0,1)
  have hcanon : ∀ o o', o < 3 → o' < 3 → o ≠ o' →
      bitCnt ctx.g[lab[d + o]!]! lab[d + o']! =
        bitCnt ctx.g[lab[d + 0]!]! lab[d + 1]! := by
    intro o o' ho ho' hne
    have ho3 : o = 0 ∨ o = 1 ∨ o = 2 := by omega
    have ho'3 : o' = 0 ∨ o' = 1 ∨ o' = 2 := by omega
    rcases ho3 with rfl | rfl | rfl <;>
      rcases ho'3 with rfl | rfl | rfl
    · omega
    · rfl
    · omega
    · rw [hsym 1 0 (by omega) (by omega)]
    · omega
    · omega
    · rw [hsym 2 0 (by omega) (by omega)]
      omega
    · rw [hsym 2 1 (by omega) (by omega)]
      omega
    · omega
  intro o o' u u' ho ho' hu hu' hoo huu
  exact bitCnt_inj.mp
    ((hcanon o o' ho ho' hoo).trans (hcanon u u' hu hu' huu).symm)

/-! # The triple flip theorem

The transposition of any two triple members, fixing every other
vertex, preserves the adjacency rows. Unlike the pair flip no matching
closure is needed: under the first-branch shape every other cell has
size at most two, so the triple's relations to it are constant across
the triple (`triple_const`), and the internal bits are off-diagonally
constant (`triple_internal`). -/

section TripleFlip

variable {lab ptn : Array Nat} {level d : Nat} {f : Nat → Nat}

/-- Vertices outside the transposed pair have identical bits at the
two transposed members. -/
private theorem triple_adj_aux
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hT : (d, d + 2) ∈ cells ptn level n)
    (hsmall : ∀ q ∈ cells ptn level n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    {j : Nat} (hj : j < n)
    (hjA : lab[j]! ≠ lab[d + a]!) (hjB : lab[j]! ≠ lab[d + b]!) :
    (ctx.g[lab[d + a]!]!).mem lab[j]! =
      (ctx.g[lab[d + b]!]!).mem lab[j]! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  obtain ⟨q, hq, hj1, hj2⟩ := cells_cover (ptn := ptn)
    (level := level) j hj
  rcases Decidable.em (q = (d, d + 2)) with rfl | hqT
  · -- j sits inside the triple: the third member
    have hj1' : d ≤ j := hj1
    have hj2' : j ≤ d + 2 := hj2
    have hw3 : j - d < 3 := by omega
    have hwa : j - d ≠ a := fun hcon => hjA (by
      have : j = d + a := by omega
      rw [this])
    have hwb : j - d ≠ b := fun hcon => hjB (by
      have : j = d + b := by omega
      rw [this])
    have hint := triple_internal hE hps hend hinj hlb hsymm hloop
      hT a (j - d) b (j - d) ha hw3 hb hw3
      (fun hcon => hwa hcon.symm) (fun hcon => hwb hcon.symm)
    rw [show d + (j - d) = j by omega] at hint
    exact hint
  · -- j sits in another, small cell
    have hqsz := hsmall q hq hqT
    have hconst := triple_const hE hps hend hinj hlb hsymm hT hq
      hqsz (o := a) (o' := b) (w := j - q.1) ha hb (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at hconst
    exact hconst

/-- The triple flip theorem: the transposition of two triple members,
fixing every other vertex, preserves the adjacency rows. -/
theorem triple_flip_rows
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsurj : ∀ v, v < n → ∃ i, i < n ∧ lab[i]! = v)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hT : (d, d + 2) ∈ cells ptn level n)
    (hsmall : ∀ q ∈ cells ptn level n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (hswap : f lab[d + a]! = lab[d + b]! ∧ f lab[d + b]! = lab[d + a]!)
    (hfix : ∀ v, v < n → v ≠ lab[d + a]! → v ≠ lab[d + b]! →
      f v = v) :
    ∀ v, v < n → ctx.g[f v]! = (ctx.g[v]!).image f := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hAn : lab[d + a]! < n := hlb _ (by omega)
  have hBn : lab[d + b]! < n := hlb _ (by omega)
  apply rows_of_bits hfb hinvol
  apply flip_bits (P := fun u v => u = lab[d + a]! ∧ v = lab[d + b]!) hsymm hfb
  · rintro u v ⟨rfl, rfl⟩
    exact hswap
  · intro z hz
    by_cases hza : z = lab[d + a]!
    · exact Or.inr ⟨_, _, hAn, hBn, ⟨rfl, rfl⟩, Or.inl hza⟩
    by_cases hzb : z = lab[d + b]!
    · exact Or.inr ⟨_, _, hAn, hBn, ⟨rfl, rfl⟩, Or.inr hzb⟩
    exact Or.inl (hfix z hz hza hzb)
  · rintro z hz hf u v ⟨rfl, rfl⟩
    by_cases hAB : lab[d + a]! = lab[d + b]!
    · rw [hAB]
    have hza := fixed_ne hf hswap.1 hAB
    have hzb := fixed_ne hf hswap.2 (Ne.symm hAB)
    obtain ⟨j, hj, rfl⟩ := hsurj z hz
    rw [hsymm _ _ (hlb j hj) hAn, hsymm _ _ (hlb j hj) hBn]
    exact triple_adj_aux hE hps hend hinj hlb hsymm hloop hT hsmall ha hb hj hza hzb
  · rintro u v x y ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨by rw [hloop _ hAn, hloop _ hBn], hsymm _ _ hAn hBn⟩

end TripleFlip

/-- The flip data at a triple target: a row-preserving self-symmetry
of the node carrying one child's individualized vertex to the
other's. -/
theorem triple_flip_data {st : RefineSt n} {level tc : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT : (tc, tc + 2) ∈ cells st.ptn level n)
    (hsmall : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + b]! = σ.toFun st.lab[tc + a]! := by
  have hd2 : tc + 2 < n := by
    have := cells_bound (by rw [hIt.ok.ptnSize]; omega)
      hIt.ok.ptnEnd _ hT
    rw [hIt.ok.ptnSize] at this
    omega
  have hlb' : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hIt.ok.labSize]; omega)
  have hAn : st.lab[tc + a]! < n := hlb' (tc + a) (by omega)
  have hBn : st.lab[tc + b]! < n := hlb' (tc + b) (by omega)
  have hABne : st.lab[tc + a]! ≠ st.lab[tc + b]! := by
    intro hcon
    have := hIt.inj (tc + a) (tc + b) (by omega) (by omega) hcon
    omega
  let f := sw1 st.lab[tc + a]! st.lab[tc + b]!
  have hswapf : f st.lab[tc + a]! = st.lab[tc + b]! ∧
      f st.lab[tc + b]! = st.lab[tc + a]! := ⟨sw1_u, sw1_v hABne⟩
  have hfixf : ∀ v, v < n → v ≠ st.lab[tc + a]! →
      v ≠ st.lab[tc + b]! → f v = v := fun _ _ h1 h2 => sw1_fix h1 h2
  have hfb : ∀ v, v < n → f v < n := sw1_lt hAn hBn
  have hinvol : ∀ v, v < n → f (f v) = v := fun v _ => sw1_invol hABne v
  have hsurj := labInj_surj
    (by rw [hIt.ok.labSize] ; exact Nat.le_refl _ : n ≤ _)
    hIt.ok.labOk hIt.inj
  have hrows := triple_flip_rows hE hIt.ok.ptnSize hIt.ok.ptnEnd
    hIt.inj hlb' hsurj hsymm hloop hfb hinvol hT hsmall ha hb
    hswapf hfixf
  have hgmap := rowsMap_of_flip_rows hgsz hfb hinvol hrows
  refine ⟨renamingOfFlip f n hfb hinvol, hgmap,
    stPerm_self_setwise hIt.ok hIt.inj hfb hinvol
      (sw1_cells hIt.ok hIt.inj hT (by omega) (by omega) hab), ?_⟩
  rw [renamingOfFlip_at hfb hinvol hAn]
  exact hswapf.1.symm

/-! # The pair-matching closure

The pair deviation needs the involution swapping every pair in the
`PairMatch`-reachability closure of the target pair. This section
defines the closure and proves the position facts its construction
consumes: a cell is determined by its start, a pair start is never
another pair's second position, and every closure member is a pair
cell. -/

section PairClosure

variable {lab ptn : Array Nat} {level : Nat}

/-- The `PairMatch`-reachability closure of a pair-cell start. -/
inductive PairReach (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat)
    (t : Nat) : Nat → Prop where
  | base : PairReach ctx lab ptn level t t
  | step {c e : Nat} : PairReach ctx lab ptn level t c →
      (c, c + 1) ∈ cells ptn level n →
      (e, e + 1) ∈ cells ptn level n →
      PairMatch ctx.g lab[c]! lab[c + 1]! lab[e]! lab[e + 1]! →
      PairReach ctx lab ptn level t e

/-- A cell is determined by its start. -/
theorem cells_eq_of_start {nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c e e' : Nat} (h1 : (c, e) ∈ cells ptn level nn)
    (h2 : (c, e') ∈ cells ptn level nn) : e = e' := by
  obtain ⟨-, -, he⟩ := (mem_cells_iff hnn hend).mp h1
  obtain ⟨-, -, he'⟩ := (mem_cells_iff hnn hend).mp h2
  rw [he, he']

/-- A pair start is never another pair's second position. -/
theorem pair_start_ne_second {nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c c' : Nat} (h1 : (c, c + 1) ∈ cells ptn level nn)
    (h2 : (c', c' + 1) ∈ cells ptn level nn) : c ≠ c' + 1 := by
  intro heq
  obtain ⟨hlt', -, he'⟩ := (mem_cells_iff hnn hend).mp h2
  obtain ⟨-, hstart, -⟩ := (mem_cells_iff hnn hend).mp h1
  have hopen : ptn[c']! > level := by
    have hIs := cells_isCell hnn hend _ h2
    rw [show c' + 1 + 1 - c' = 2 by omega] at hIs
    exact hIs.2.2.1 c' (Nat.le_refl _) (by omega)
  rcases hstart with h0 | hcl
  · omega
  · rw [heq, show c' + 1 - 1 = c' by omega] at hcl
    omega

/-- Every member of the closure of a pair start is itself a pair-cell
start. -/
theorem pairReach_pair {t c : Nat}
    (hroot : (t, t + 1) ∈ cells ptn level n)
    (h : PairReach ctx lab ptn level t c) :
    (c, c + 1) ∈ cells ptn level n := by
  induction h with
  | base => exact hroot
  | step hr hc he hm ih => exact he

/-- Distinct closure pairs occupy disjoint positions. -/
theorem pair_cells_disj {nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c c' : Nat} (h1 : (c, c + 1) ∈ cells ptn level nn)
    (h2 : (c', c' + 1) ∈ cells ptn level nn) (hne : c ≠ c') :
    c + 2 ≤ c' ∨ c' + 2 ≤ c := by
  have hIs1 := cells_isCell hnn hend _ h1
  have hIs2 := cells_isCell hnn hend _ h2
  rw [show c + 1 + 1 - c = 2 by omega] at hIs1
  rw [show c' + 1 + 1 - c' = 2 by omega] at hIs2
  rcases isCell_disj_or_eq hIs1 hIs2 with ⟨heq, -⟩ | hd | hd
  · exact absurd heq hne
  · exact Or.inl hd
  · exact Or.inr hd

end PairClosure

end Hex.GraphIso.Nauty

/-!
The pair-closure involution.

The pair deviation swaps every pair cell in the `PairMatch`-reachability
closure of the target pair at once. This part of the file constructs
that involution (`pairFlip`: a member of a closure pair maps to its
partner and every other vertex is fixed, a `Classical.choose` over the
closure made well defined by the position toolkit's uniqueness facts),
proves its evaluation laws, bounds, and involutivity, and discharges
the `S`-hypotheses of `flip_rows` for it: closure pairs swap
(`pairFlip_first`/`pairFlip_second`), members of non-closure cells are
fixed (`pairFlip_fix_cell`), and the closure is `PairMatch`-closed by
construction (`PairReach.step`). The self-equivalence
(`cellsPerm_self_flip`, stated for any renaming swapping `S`-pairs and
fixing the other cells pointwise) and the packaged pair deviation
(`pair_deviation_leafRows`, through `deviation_leafRows_self` exactly
as the triple instance) complete the pair analogue of the triple
theory.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # The involution -/

section PairFlip

open Classical

variable {lab ptn : Array Nat} {level t : Nat}

/-- The involution swapping every pair in the `PairReach` closure of
`t`: a vertex that is a member of a closure pair maps to its partner,
and every other vertex is fixed. -/
noncomputable def pairFlip (ctx : Ctx n) (lab ptn : Array Nat)
    (level t : Nat) : Nat → Nat := fun v =>
  if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]! then
    lab[h.choose + 1]!
  else if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]! then
    lab[h.choose]!
  else v

/-- Two closure pairs sharing a first member coincide. -/
private theorem first_eq (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c]! = lab[c']!) : c = c' := by
  have h1 := cells_bound (by omega) hend _ hcell
  have h2 := cells_bound (by omega) hend _ hcell'
  have h1' : c + 1 < ptn.size := h1
  have h2' : c' + 1 < ptn.size := h2
  exact hinj c c' (by omega) (by omega) hv

/-- Two closure pairs sharing a second member coincide. -/
private theorem second_eq (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c + 1]! = lab[c' + 1]!) : c = c' := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have := hinj (c + 1) (c' + 1) (by omega) (by omega) hv
  omega

/-- A first member of one pair cell is never the second member of
another. -/
private theorem first_ne_second (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c]! = lab[c' + 1]!) : False := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have heq := hinj c (c' + 1) (by omega) (by omega) hv
  exact pair_start_ne_second (by omega) hend hcell hcell' heq

/-- The flip carries a closure pair's first member to its second. -/
theorem pairFlip_first (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level n) :
    pairFlip ctx lab ptn level t lab[c]! = lab[c + 1]! := by
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧ lab[c]! = lab[c']! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (first_eq hpsz hend hinj hcell hcell' hv).symm
  show (if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧ lab[c]! = lab[c']! then
      lab[h.choose + 1]!
    else _) = _
  rw [dite_eq_left hex]
  show lab[hex.choose + 1]! = lab[c + 1]!
  rw [hcc]

/-- The flip carries a closure pair's second member to its first. -/
theorem pairFlip_second (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level n) :
    pairFlip ctx lab ptn level t lab[c + 1]! = lab[c]! := by
  have hno : ¬ ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c']! := by
    rintro ⟨c', -, hcell', hv⟩
    exact first_ne_second hpsz hend hinj hcell' hcell hv.symm
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c' + 1]! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (second_eq hpsz hend hinj hcell hcell' hv).symm
  show (if _ : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c']! then _
    else if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c' + 1]! then lab[h.choose]!
    else _) = _
  rw [dite_eq_right hno, dite_eq_left hex]
  show lab[hex.choose]! = lab[c]!
  rw [hcc]

/-- The flip fixes every vertex that is not a closure-pair member. -/
theorem pairFlip_fix {v : Nat}
    (hnone : ∀ c, PairReach ctx lab ptn level t c →
      (c, c + 1) ∈ cells ptn level n →
        v ≠ lab[c]! ∧ v ≠ lab[c + 1]!) :
    pairFlip ctx lab ptn level t v = v := by
  have h1 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).1 hv
  have h2 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).2 hv
  show (if _ : _ then _ else if _ : _ then _ else v) = v
  rw [dite_eq_right h1, dite_eq_right h2]

/-- The flip is bounded on the vertex range. -/
theorem pairFlip_lt (hpsz : ptn.size = n)
    (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hlb : LabOk lab n)
    {v : Nat} (hv : v < n) :
    pairFlip ctx lab ptn level t v < n := by
  show (if _ : _ then _ else if _ : _ then _ else v) < n
  split
  · next h =>
    obtain ⟨-, hcell, -⟩ := h.choose_spec
    have hb : (h.choose, h.choose + 1).2 < ptn.size :=
      cells_bound (by omega) hend _ hcell
    exact hlb _ (by rw [hlsz]; omega)
  · split
    · next h =>
      obtain ⟨-, hcell, -⟩ := h.choose_spec
      have hb : (h.choose, h.choose + 1).2 < ptn.size :=
        cells_bound (by omega) hend _ hcell
      exact hlb _ (by rw [hlsz]; omega)
    · exact hv

/-- The flip is an involution on the vertex range. -/
theorem pairFlip_invol (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {v : Nat} :
    pairFlip ctx lab ptn level t
      (pairFlip ctx lab ptn level t v) = v := by
  rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]!) with h1 | h1
  · obtain ⟨c, hr, hcell, rfl⟩ := h1
    rw [pairFlip_first hpsz hend hinj hr hcell,
      pairFlip_second hpsz hend hinj hr hcell]
  · rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
        (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]!) with
      h2 | h2
    · obtain ⟨c, hr, hcell, rfl⟩ := h2
      rw [pairFlip_second hpsz hend hinj hr hcell,
        pairFlip_first hpsz hend hinj hr hcell]
    · have hfix : pairFlip ctx lab ptn level t v = v := by
        refine pairFlip_fix fun c hr hcell => ⟨?_, ?_⟩
        · intro hcon
          exact h1 ⟨c, hr, hcell, hcon⟩
        · intro hcon
          exact h2 ⟨c, hr, hcell, hcon⟩
      rw [hfix, hfix]

/-- A member of a cell outside the closure is fixed by the flip: its
position would otherwise sit inside a closure pair's window. -/
theorem pairFlip_fix_cell (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {q : Nat × Nat} (hq : q ∈ cells ptn level n)
    (hnotS : ¬ PairReach ctx lab ptn level t q.1)
    {o : Nat} (ho : o < q.2 + 1 - q.1) :
    pairFlip ctx lab ptn level t lab[q.1 + o]! = lab[q.1 + o]! := by
  have hqbd : q.2 < ptn.size := cells_bound (by omega) hend _ hq
  have hqle := cells_le _ hq
  have hqIs := cells_isCell (by omega) hend _ hq
  refine pairFlip_fix fun c hr hcell => ?_
  have hcbd : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have hcIs := cells_isCell (by omega) hend _ hcell
  rw [show c + 1 + 1 - c = 2 by omega] at hcIs
  constructor
  · intro hcon
    have hpos : q.1 + o = c :=
      hinj (q.1 + o) c (by omega) (by omega) hcon
    rcases isCell_disj_or_eq hqIs hcIs with ⟨he1, he2⟩ | hd | hd
    · have he1' : q.1 = c := he1
      apply hnotS
      rw [he1']
      exact hr
    · omega
    · omega
  · intro hcon
    have hpos : q.1 + o = c + 1 :=
      hinj (q.1 + o) (c + 1) (by omega) (by omega) hcon
    rcases isCell_disj_or_eq hqIs hcIs with ⟨he1, he2⟩ | hd | hd
    · have he1' : q.1 = c := he1
      apply hnotS
      rw [he1']
      exact hr
    · omega
    · omega

end PairFlip

/-- The flip data at a pair target: a row-preserving self-symmetry of
the node carrying one child's individualized vertex to the other's. -/
theorem pair_flip_data {st : RefineSt n} {level tc : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hP : (tc, tc + 1) ∈ cells st.ptn level n)
    (hOdd : ∀ q ∈ cells st.ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {a b : Nat} (ha : a < 2) (hb : b < 2) (hab : a ≠ b) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + b]! = σ.toFun st.lab[tc + a]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinjr : ∀ i j, i < n → j < n →
      st.lab[i]! = st.lab[j]! → i = j := hIt.inj
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hfb : ∀ v, v < n →
      pairFlip ctx st.lab st.ptn level tc v < n := fun v hv =>
    pairFlip_lt hpsz hlsz hend hIt.ok.labOk hv
  have hinvol : ∀ v, v < n →
      pairFlip ctx st.lab st.ptn level tc
        (pairFlip ctx st.lab st.ptn level tc v) = v := fun v _ =>
    pairFlip_invol hpsz hend hIt.inj
  have hSpair : ∀ p ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 → p.2 = p.1 + 1 := by
    intro p hp hS
    have hcell := pairReach_pair hP hS
    have hpm : (p.1, p.2) ∈ cells st.ptn level n := hp
    exact cells_eq_of_start (by omega) hend hpm hcell
  have hSswap : ∀ p ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 →
      pairFlip ctx st.lab st.ptn level tc st.lab[p.1]! =
          st.lab[p.1 + 1]! ∧
        pairFlip ctx st.lab st.ptn level tc st.lab[p.1 + 1]! =
          st.lab[p.1]! := by
    intro p hp hS
    have hcell := pairReach_pair hP hS
    exact ⟨pairFlip_first hpsz hend hIt.inj hS hcell,
      pairFlip_second hpsz hend hIt.inj hS hcell⟩
  have hSfix : ∀ p ∈ cells st.ptn level n,
      ¬ PairReach ctx st.lab st.ptn level tc p.1 →
      ∀ o, o < p.2 + 1 - p.1 →
        pairFlip ctx st.lab st.ptn level tc st.lab[p.1 + o]! =
          st.lab[p.1 + o]! := by
    intro p hp hS o ho
    exact pairFlip_fix_cell hpsz hend hIt.inj hp hS ho
  have hSclosed : ∀ p ∈ cells st.ptn level n,
      ∀ q ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 → q.2 = q.1 + 1 →
      PairMatch ctx.g st.lab[p.1]! st.lab[p.1 + 1]!
        st.lab[q.1]! st.lab[q.1 + 1]! →
      PairReach ctx st.lab st.ptn level tc q.1 := by
    intro p hp q hq hS hq2 hm
    have hqm : (q.1, q.1 + 1) ∈ cells st.ptn level n := by
      have hqm' : (q.1, q.2) ∈ cells st.ptn level n := hq
      rw [hq2] at hqm'
      exact hqm'
    exact PairReach.step hS (pairReach_pair hP hS) hqm hm
  have hsurj := labInj_surj
    (by rw [hlsz]; exact Nat.le_refl _ : n ≤ st.lab.size)
    hIt.ok.labOk hIt.inj
  have hrows := flip_rows hE hpsz hend hinjr hlb hsurj hsymm
    hloop hfb hinvol hSpair hSswap hSfix hSclosed hOdd
  have hgmap := rowsMap_of_flip_rows hgsz hfb hinvol hrows
  have hsp := stPerm_self_setwise hIt.ok hIt.inj hfb hinvol (by
    intro p hp o ho
    by_cases hs : PairReach ctx st.lab st.ptn level tc p.1
    · have he := hSpair p hp hs
      obtain ⟨hf1, hf2⟩ := hSswap p hp hs
      by_cases hz : o = 0
      · subst o
        exact ⟨1, by omega, by simpa only [Nat.add_zero] using hf1⟩
      · have ho1 : o = 1 := by omega
        subst o
        exact ⟨0, by omega, by simpa only [Nat.add_zero] using hf2⟩
    · exact ⟨o, ho, hSfix p hp hs o ho⟩)
  have hbd : (tc, tc + 1).2 < st.ptn.size :=
    cells_bound (by omega) hend _ hP
  have hbase : PairReach ctx st.lab st.ptn level tc tc :=
    PairReach.base
  have hvv : st.lab[tc + b]! =
      (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
        hfb hinvol).toFun st.lab[tc + a]! := by
    have hat : ∀ i, i < n →
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[i]! =
          pairFlip ctx st.lab st.ptn level tc st.lab[i]! := fun i hi =>
      renamingOfFlip_at hfb hinvol (hlb i hi)
    rcases Decidable.em (a = 0) with rfl | ha0
    · have hb1 : b = 1 := by omega
      subst hb1
      show st.lab[tc + 1]! =
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[tc]!
      rw [hat tc (by rw [hpsz] at hbd; omega),
        pairFlip_first hpsz hend hIt.inj hbase hP]
    · have ha1 : a = 1 := by omega
      have hb0 : b = 0 := by omega
      subst ha1; subst hb0
      show st.lab[tc]! =
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[tc + 1]!
      rw [hat (tc + 1) (by rw [hpsz] at hbd; omega),
        pairFlip_second hpsz hend hIt.inj hbase hP]
  exact ⟨renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
    hfb hinvol, hgmap, hsp, hvv⟩

end Hex.GraphIso.Nauty
