/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Cells
import all HexGraphIso.Nauty.Equitable.Basic

public section

/-!
Neighbour counts and balanced sets of distinguishing vertices. Equal
counts balance the two directions of disagreement. On at most three
vertices, disagreement is empty or consists of one opposite pair.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- The adjacency bit as a count. -/
def bitCnt (r : VSet n) (v : Nat) : Nat := if r.mem v then 1 else 0

theorem bitCnt_le_one (r : VSet n) (v : Nat) : bitCnt r v ≤ 1 := by
  rw [bitCnt]
  split <;> omega

theorem bitCnt_eq_zero {r : VSet n} {v : Nat} :
    bitCnt r v = 0 ↔ r.mem v = false := by
  rw [bitCnt]
  rcases h : r.mem v with _ | _ <;> simp

theorem bitCnt_eq_one {r : VSet n} {v : Nat} :
    bitCnt r v = 1 ↔ r.mem v = true := by
  rw [bitCnt]
  rcases h : r.mem v with _ | _ <;> simp

theorem bitCnt_inj {r r' : VSet n} {v v' : Nat} :
    bitCnt r v = bitCnt r' v' ↔ r.mem v = r'.mem v' := by
  rw [bitCnt, bitCnt]
  rcases h : r.mem v with _ | _ <;>
    rcases h' : r'.mem v' with _ | _ <;> simp

/-- The count into a window's splitter set expands into the sum of the
adjacency bits at the window's members. -/
theorem cardInter_workset {lab : Array Nat} (r : VSet n) :
    ∀ (len lo : Nat),
      (∀ o o', o ≤ len → o' ≤ len → o ≠ o' →
        lab[lo + o]! ≠ lab[lo + o']!) →
      (worksetOf n lab lo (lo + len)).cardInter r =
        ((List.range (len + 1)).map fun o => bitCnt r lab[lo + o]!).sum
  | 0, lo, _ => by
    rw [Nat.add_zero, worksetOf_singleton, VSet.cardInter_singleton]
    simp [bitCnt]
  | len + 1, lo, hdist => by
    have hsplit : worksetOf n lab lo (lo + (len + 1)) =
        (worksetOf n lab lo (lo + len)).union
          (worksetOf n lab (lo + len + 1) (lo + len + 1)) :=
      worksetOf_split (by omega) (by omega)
    have hdisj : (worksetOf n lab lo (lo + len)).inter
        (worksetOf n lab (lo + len + 1) (lo + len + 1)) = VSet.empty := by
      refine worksetOf_disjoint fun v hv1 hv2 => ?_
      rw [segN] at hv1 hv2
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv1
      obtain ⟨o', ho', he⟩ := List.mem_map.mp hv2
      have ho2 := List.mem_range.mp ho
      have ho2' := List.mem_range.mp ho'
      have ho'0 : o' = 0 := by omega
      subst ho'0
      have he' : lab[lo + (len + 1)]! = lab[lo + o]! := he
      exact hdist o (len + 1) (by omega) (by omega) (by omega) he'.symm
    rw [hsplit, VSet.cardInter_union_disjoint hdisj,
      cardInter_workset r len lo
        (fun o o' h1 h2 h3 => hdist o o' (by omega) (by omega) h3),
      worksetOf_singleton, VSet.cardInter_singleton]
    conv => rhs; rw [sum_range_succ]
    have hidx : lo + len + 1 = lo + (len + 1) := by omega
    rw [hidx, bitCnt]

/-- Adjacency-bit counts are symmetric between vertices. -/
theorem bitCnt_symm
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {u w : Nat} (hu : u < n) (hw : w < n) :
    bitCnt ctx.g[u]! w = bitCnt ctx.g[w]! u := by
  rw [bitCnt, bitCnt, hsymm u w hu hw]

/-- The count of a vertex into a cell's splitter set is the sum of its
adjacency bits at the cell's members. -/
theorem count_into_cell {lab ptn : Array Nat} {level : Nat}
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    {d e : Nat} (hD : (d, e) ∈ cells ptn level n)
    {u : Nat} :
    (worksetOf n lab d e).cardInter ctx.g[u]! =
      ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[u]! lab[d + o]!).sum := by
  have hde : d ≤ e := cells_le _ hD
  have he : e < n := by
    have := cells_bound (by omega) hend _ hD
    omega
  have h := cardInter_workset (lab := lab) (n := n) ctx.g[u]! (e - d) d
    (fun o o' h1 h2 h3 heq2 => h3 (by
      have := hinj (d + o) (d + o') (by omega) (by omega) heq2
      omega))
  rw [show d + (e - d) = e by omega] at h
  rw [show e + 1 - d = (e - d) + 1 by omega]
  exact h

/-- Equal Boolean counts balance the two directions of disagreement. -/
theorem countP_balance {α : Type} (p q : α → Bool) (l : List α) :
    l.countP p + l.countP (fun x => q x && !p x) =
      l.countP q + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp_all <;> omega

/-- The count into a list is the sum of its adjacency bits. -/
theorem countP_bits (r : VSet n) (l : List Nat) :
    l.countP r.mem = (l.map (bitCnt r)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, bitCnt]
    cases r.mem a <;> simp_all [Nat.add_comm]

/-- Counting adjacent cell members agrees with the splitter-set count. -/
theorem countP_cell {lab ptn : Array Nat} {level d e u : Nat}
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hD : (d, e) ∈ cells ptn level n) :
    (List.range (e + 1 - d)).countP (fun o => (ctx.g[u]!).mem lab[d + o]!) =
      (worksetOf n lab d e).cardInter ctx.g[u]! := by
  rw [count_into_cell hps hend hinj hD]
  simpa only [segN, List.countP_map, List.map_map, Function.comp_def] using
    countP_bits ctx.g[u]! (segN lab d (e + 1 - d))

/-- Equitability balances the two directions of disagreement in each cell. -/
theorem differ_balance {lab ptn : Array Nat} {level c e d de u v : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hC : (c, e) ∈ cells ptn level n) (hD : (d, de) ∈ cells ptn level n)
    (hu : u < e + 1 - c) (hv : v < e + 1 - c) :
    (segN lab d (de + 1 - d)).countP
        (fun w => (ctx.g[lab[c + u]!]!).mem w && !(ctx.g[lab[c + v]!]!).mem w) =
      (segN lab d (de + 1 - d)).countP
        (fun w => (ctx.g[lab[c + v]!]!).mem w && !(ctx.g[lab[c + u]!]!).mem w) := by
  have he := hE _ hC _ hD u v hu hv
  rw [count_into_cell hps hend hinj hD,
    count_into_cell hps hend hinj hD] at he
  have hb := countP_balance (ctx.g[lab[c + u]!]!).mem
    (ctx.g[lab[c + v]!]!).mem (segN lab d (de + 1 - d))
  rw [countP_bits, countP_bits] at hb
  simp only [segN, List.map_map, Function.comp_def] at hb ⊢
  simp only at he
  omega

/-- On a list of at most one vertex, equal neighbour counts force
pointwise equal adjacency. -/
theorem bits_eq_of_short {r s : VSet n} {l : List Nat}
    (hlen : l.length ≤ 1)
    (he : (l.map (bitCnt r)).sum = (l.map (bitCnt s)).sum) :
    ∀ w ∈ l, r.mem w = s.mem w := by
  cases l with
  | nil => simp
  | cons a l =>
    have hl : l = [] := by simpa using hlen
    subst l
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero] at he
    simpa using bitCnt_inj.mp he

/-- A predicate counted at most once selects at most one distinct element. -/
theorem countP_unique {α : Type} {p : α → Bool} {l : List α}
    (hc : l.countP p ≤ 1) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hpa : p a = true) (hpb : p b = true) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.mem_cons] at ha hb
    rw [List.countP_cons] at hc
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have ht := List.countP_pos_iff.mpr ⟨b, hb, hpb⟩
      simp only [hpa, ite_true] at hc
      omega
    · have ht := List.countP_pos_iff.mpr ⟨a, ha, hpa⟩
      simp only [hpb, ite_true] at hc
      omega
    · exact ih (by split at hc <;> omega) ha hb

/-- Disagreement in either direction uses at most the whole list. -/
theorem countP_differ_le {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun x => p x && !q x) +
      l.countP (fun x => q x && !p x) ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons]
    cases p a <;> cases q a <;> simp_all <;> omega

/-- Equal counts on at most three vertices give either identical bits
or a single pair distinguishing the two rows in opposite directions. -/
theorem differ_pair {α : Type} (p q : α → Bool) {l : List α}
    (hlen : l.length ≤ 3) (he : l.countP p = l.countP q) :
    (∀ w ∈ l, p w = q w) ∨
      ∃ a ∈ l, ∃ b ∈ l, a ≠ b ∧
        p a = true ∧ q a = false ∧ p b = false ∧ q b = true ∧
        ∀ w ∈ l, w ≠ a → w ≠ b → p w = q w := by
  classical
  have hbal := countP_balance p q l
  have hle := countP_differ_le p q l
  have hcnt : l.countP (fun x => p x && !q x) =
      l.countP (fun x => q x && !p x) := by omega
  have hc : l.countP (fun x => p x && !q x) ≤ 1 := by omega
  by_cases hz : l.countP (fun x => p x && !q x) = 0
  · left
    have h1 := List.countP_eq_zero.mp hz
    have h2 := List.countP_eq_zero.mp (hcnt ▸ hz)
    intro w hw
    have hp := h1 w hw
    have hq := h2 w hw
    cases hpw : p w <;> cases hqw : q w <;> simp_all
  · obtain ⟨a, ha, hpa⟩ := List.countP_pos_iff.mp (show
        0 < l.countP (fun x => p x && !q x) by omega)
    obtain ⟨b, hb, hpb⟩ := List.countP_pos_iff.mp (show
        0 < l.countP (fun x => q x && !p x) by omega)
    have ha' : p a = true ∧ q a = false := by simpa using hpa
    have hb' : p b = false ∧ q b = true := by simpa [and_comm] using hpb
    refine Or.inr ⟨a, ha, b, hb, ?_, ha'.1, ha'.2, hb'.1, hb'.2, ?_⟩
    · intro hab
      subst b
      simp_all
    · intro w hw hwa hwb
      have h1 : ¬(p w && !q w) = true := fun h =>
        hwa (countP_unique hc hw ha h hpa)
      have h2 : ¬(q w && !p w) = true := fun h =>
        hwb (countP_unique (p := fun x => q x && !p x) (by omega) hw hb h hpb)
      cases hpw : p w <;> cases hqw : q w <;> simp_all

/-- Swapping both pairs preserves adjacency: the bits between two pair
cells of an equitable partition satisfy the two cross equalities, in
every configuration (empty, complete, or either matching). -/
theorem pair_swap_eq {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {c d : Nat} (hP : (c, c + 1) ∈ cells ptn level n)
    (hQ : (d, d + 1) ∈ cells ptn level n) :
    (ctx.g[lab[c]!]!).mem lab[d]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d + 1]! ∧
    (ctx.g[lab[c]!]!).mem lab[d + 1]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d]! := by
  have hc1 : c + 1 < n := by
    have := cells_bound (by omega) hend _ hP
    omega
  have hd1 : d + 1 < n := by
    have := cells_bound (by omega) hend _ hQ
    omega
  have h1 := hE _ hP _ hQ 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h1
  rw [count_into_cell hps hend hinj hQ,
    count_into_cell hps hend hinj hQ,
    show d + 1 + 1 - d = 2 by omega, sum_range_two, sum_range_two] at h1
  simp only [Nat.add_zero] at h1
  have h2 := hE _ hQ _ hP 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h2
  rw [count_into_cell hps hend hinj hP,
    count_into_cell hps hend hinj hP,
    show c + 1 + 1 - c = 2 by omega, sum_range_two, sum_range_two] at h2
  simp only [Nat.add_zero] at h2
  rw [bitCnt_symm hsymm (hlb d (by omega)) (hlb c (by omega)),
    bitCnt_symm hsymm (hlb d (by omega)) (hlb (c + 1) hc1),
    bitCnt_symm hsymm (hlb (d + 1) hd1) (hlb c (by omega)),
    bitCnt_symm hsymm (hlb (d + 1) hd1) (hlb (c + 1) hc1)] at h2
  exact ⟨bitCnt_inj.mp (by omega), bitCnt_inj.mp (by omega)⟩

/-- The matching configuration between two pair cells: each member of
one pair is adjacent to exactly one member of the other, in one of the
two consistent ways. -/
def PairMatch (g : Array (VSet n)) (x y z t : Nat) : Prop :=
  ((g[x]!).mem z = true ∧ (g[y]!).mem t = true ∧
    (g[x]!).mem t = false ∧ (g[y]!).mem z = false) ∨
  ((g[x]!).mem t = true ∧ (g[y]!).mem z = true ∧
    (g[x]!).mem z = false ∧ (g[y]!).mem t = false)

/-- Between two non-matching pair cells of an equitable partition the
bits are insensitive to swapping either pair alone. -/
theorem pair_eq_of_not_match {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {c d : Nat} (hP : (c, c + 1) ∈ cells ptn level n)
    (hQ : (d, d + 1) ∈ cells ptn level n)
    (hnm : ¬ PairMatch ctx.g lab[c]! lab[c + 1]! lab[d]! lab[d + 1]!) :
    (ctx.g[lab[c]!]!).mem lab[d]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d]! ∧
    (ctx.g[lab[c]!]!).mem lab[d + 1]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d + 1]! := by
  obtain ⟨h1, h2⟩ :=
    pair_swap_eq hE hps hend hinj hlb hsymm hP hQ
  rw [PairMatch] at hnm
  rcases hp : (ctx.g[lab[c]!]!).mem lab[d]! with _ | _ <;>
    rcases hq : (ctx.g[lab[c]!]!).mem lab[d + 1]! with _ | _ <;>
      rw [hp] at h1 <;> rw [hq] at h2 <;>
        rw [hp, hq] at hnm <;> simp_all

/-- The members of a pair cell have identical bits at every member of
a cell of odd size: parity forces the count between them to be empty
or complete. -/
theorem pair_odd_eq {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {c d e : Nat} (hP : (c, c + 1) ∈ cells ptn level n)
    (hD : (d, e) ∈ cells ptn level n)
    (hodd : (e + 1 - d) % 2 = 1) :
    ∀ o, o < e + 1 - d →
      (ctx.g[lab[c]!]!).mem lab[d + o]! =
        (ctx.g[lab[c + 1]!]!).mem lab[d + o]! := by
  have hc1 : c + 1 < n := by
    have := cells_bound (by omega) hend _ hP
    omega
  have hde : d ≤ e := cells_le _ hD
  have he : e < n := by
    have := cells_bound (by omega) hend _ hD
    omega
  have hxy := hE _ hP _ hD 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at hxy
  rw [count_into_cell hps hend hinj hD,
    count_into_cell hps hend hinj hD]
    at hxy
  have hB : ∀ o, o < e + 1 - d →
      bitCnt ctx.g[lab[c]!]! lab[d + o]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]! =
      bitCnt ctx.g[lab[c]!]! lab[d]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d]! := by
    intro o ho
    have h := hE _ hD _ hP o 0 (by omega) (by omega)
    simp only [Nat.add_zero] at h
    rw [count_into_cell hps hend hinj hP,
      count_into_cell hps hend hinj hP,
      show c + 1 + 1 - c = 2 by omega, sum_range_two, sum_range_two]
      at h
    simp only [Nat.add_zero] at h
    rw [bitCnt_symm hsymm (hlb (d + o) (by omega)) (hlb c (by omega)),
      bitCnt_symm hsymm (hlb (d + o) (by omega)) (hlb (c + 1) hc1),
      bitCnt_symm hsymm (hlb d (by omega)) (hlb c (by omega)),
      bitCnt_symm hsymm (hlb d (by omega)) (hlb (c + 1) hc1)] at h
    exact h
  have hsum : ((List.range (e + 1 - d)).map fun o =>
      bitCnt ctx.g[lab[c]!]! lab[d + o]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!).sum =
      (e + 1 - d) * (bitCnt ctx.g[lab[c]!]! lab[d]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d]!) := by
    rw [List.map_congr_left fun o ho =>
      hB o (List.mem_range.mp ho), sum_range_const]
  rw [sum_map_add] at hsum
  have hcD : bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! ≤ 2 := by
    have := bitCnt_le_one ctx.g[lab[c]!]! lab[d]!
    have := bitCnt_le_one ctx.g[lab[c + 1]!]! lab[d]!
    omega
  intro o ho
  have hcases : bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! = 0 ∨
    bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! = 1 ∨
    bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, Nat.mul_zero] at hsum
    have hx0 : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c]!]! lab[d + o]!).sum = 0 := by omega
    have hy0 : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!).sum = 0 := by omega
    rw [bitCnt_eq_zero.mp (sum_range_eq_zero _ hx0 o ho),
      bitCnt_eq_zero.mp (sum_range_eq_zero _ hy0 o ho)]
  · rw [h1, Nat.mul_one] at hsum
    omega
  · rw [h2] at hsum
    have hx : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c]!]! lab[d + o]!).sum = e + 1 - d := by
      have hlx := sum_range_le
        (fun o => bitCnt ctx.g[lab[c]!]! lab[d + o]!) (e + 1 - d)
        fun o _ => bitCnt_le_one ..
      have hly := sum_range_le
        (fun o => bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!) (e + 1 - d)
        fun o _ => bitCnt_le_one ..
      omega
    have hy : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!).sum = e + 1 - d := by
      have hlx := sum_range_le
        (fun o => bitCnt ctx.g[lab[c]!]! lab[d + o]!) (e + 1 - d)
        fun o _ => bitCnt_le_one ..
      omega
    rw [bitCnt_eq_one.mp (sum_range_eq_len _
        (fun o _ => bitCnt_le_one ..) hx o ho),
      bitCnt_eq_one.mp (sum_range_eq_len _
        (fun o _ => bitCnt_le_one ..) hy o ho)]

/-- Equal internal degrees in a four-element cell make complementary
pairs equally adjacent. -/
theorem reg4_comp {e01 e02 e03 e12 e13 e23 : Nat}
    (h01 : e01 + e02 + e03 = e01 + e12 + e13)
    (h02 : e01 + e02 + e03 = e02 + e12 + e23)
    (h03 : e01 + e02 + e03 = e03 + e13 + e23) :
    e01 = e23 ∧ e02 = e13 ∧ e03 = e12 := by
  omega

end Hex.GraphIso.Nauty
