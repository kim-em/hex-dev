/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Spec.Descent
import all HexGraphIso.Nauty.Equitable.Basic
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
Neighbour counts and balanced sets of distinguishing vertices. Equal
counts balance the two directions of disagreement. On at most three
vertices, disagreement is empty or consists of one opposite pair.
Regularity gives equal internal adjacency on triples and complementary
adjacency on four-cells.
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

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

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

theorem mem_erase_nodup :
    ∀ {l : List Nat}, l.Nodup → ∀ a w,
      (w ∈ l.erase a ↔ w ∈ l ∧ w ≠ a)
  | [], _, a, w => by simp
  | b :: t, hnd, a, w => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      constructor
      · intro hw
        exact ⟨List.mem_cons_of_mem _ hw,
          fun hcon => hnd.1 (hcon ▸ hw)⟩
      · rintro ⟨hw, hne⟩
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact absurd rfl hne
        · exact hmem
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba)]
      rw [List.mem_cons, List.mem_cons,
        mem_erase_nodup hnd.2 a w]
      constructor
      · rintro (rfl | ⟨hw, hne⟩)
        · exact ⟨Or.inl rfl, hba⟩
        · exact ⟨Or.inr hw, hne⟩
      · rintro ⟨rfl | hw, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hw, hne⟩

/-- The count of one row into a singleton cell is its bit there, so
equitability makes the bits of all members of a cell agree at every
singleton-cell vertex. -/
theorem cell_const_into_singleton {lab ptn : Array Nat}
    {level : Nat}
    (hE : Equitable ctx level lab ptn)
    {tc te : Nat} (hC : (tc, te) ∈ cells ptn level n)
    {s : Nat} (hS : (s, s) ∈ cells ptn level n)
    {o o' : Nat} (ho : o ≤ te - tc) (ho' : o' ≤ te - tc) :
    (ctx.g[lab[tc + o]!]!).mem lab[s]! =
      (ctx.g[lab[tc + o']!]!).mem lab[s]! := by
  have hle : tc ≤ te := cells_le _ hC
  have h := hE _ hC _ hS o o' (by omega) (by omega)
  rw [worksetOf_singleton, VSet.cardInter_singleton,
    VSet.cardInter_singleton] at h
  rcases hb : (ctx.g[lab[tc + o]!]!).mem lab[s]! with _ | _ <;>
    rcases hb' : (ctx.g[lab[tc + o']!]!).mem lab[s]! with _ | _ <;>
      rw [hb, hb'] at h <;> simp_all

theorem nodup_erase :
    ∀ {l : List Nat}, l.Nodup → ∀ a, (l.erase a).Nodup
  | [], _, _ => by simp
  | b :: t, hnd, a => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      exact hnd.2
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba),
        List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_erase hnd.2 a⟩
      exact hnd.1 ((mem_erase_nodup hnd.2 a b).mp hmem).1

theorem nodup_subset_length :
    ∀ (l r : List Nat), l.Nodup → (∀ x ∈ l, x ∈ r) →
      l.length ≤ r.length
  | [], r, _, _ => by simp
  | a :: t, r, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ r := hsub a List.mem_cons_self
    have hlen := (List.perm_cons_erase ha).length_eq
    have hsub' : ∀ x ∈ t, x ∈ r.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun hcon => hnd.1
        (by rw [← hcon]; exact hx))).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have h := nodup_subset_length t (r.erase a) hnd.2 hsub'
    simp only [List.length_cons] at hlen ⊢
    omega

theorem sum3_eq_of_cover {f : Nat → Nat} {a b c : Nat}
    (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f 0 + f 1 + f 2 = f a + f b + f c := by
  have h0 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have h1 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have h2 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;> omega

/-- Two distinct offsets below four leave two more. -/
theorem other_two {p q : Nat} (hp : p ≤ 3) (hq : q ≤ 3)
    (hpq : p ≠ q) :
    ∃ r s, r ≤ 3 ∧ s ≤ 3 ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      r ≠ s := by
  have hp3 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  have hq3 : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hp3 with rfl | rfl | rfl | rfl <;>
    rcases hq3 with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hpq
      | exact ⟨2, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨1, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨1, 2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 1, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩

section

variable {st : RefineSt n} {level tc te oU oV : Nat}

set_option maxHeartbeats 1000000 in
/-- In a five-member window, the member outside a crossed pair has
equal bits at the pair: the pair's two row sums expand over the five
named offsets, the crossed types cancel, and the shared internal bit
cancels by symmetry. -/
theorem differ_five {wa wb wf : Nat}
    (hIt : IterOk ctx level st)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hm : te + 1 - tc = 5)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hwf : wf ≤ te - tc)
    (hab : wa ≠ wb) (haf : wa ≠ wf) (hbf : wb ≠ wf)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (hfu : wf ≠ oU) (hfv : wf ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! =
      true) :
    (ctx.g[st.lab[tc + wf]!]!).mem st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + wf]!]!).mem st.lab[tc + wb]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hnd : ([oU, oV, wa, wb, wf] : List Nat).Nodup := by
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro (h | h | h | h | h) <;> omega
    · rintro (h | h | h | h) <;> omega
    · rintro (h | h | h) <;> omega
    · rintro (h | h) <;> omega
    · simp
  have hbd : ∀ x ∈ ([oU, oV, wa, wb, wf] : List Nat),
      x < te + 1 - tc := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hxf : x = wf := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hcic : ∀ o : Nat, o ≤ te - tc →
      (worksetOf n st.lab tc te).cardInter
          ctx.g[st.lab[tc + o]!]! =
        ((List.range (te + 1 - tc)).map fun w =>
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w]!).sum := by
    intro o ho
    exact count_into_cell hpsz hend hinj hC
  have hrow := hE _ hC _ hC wa wb (by omega) (by omega)
  rw [hcic wa hwa, hcic wb hwb, hm] at hrow
  rw [sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd),
    sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd)] at hrow
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hrow
  have hloopa : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wa]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hloopb : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wb]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsymab : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wb]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wa]! :=
    bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have h1 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oU]! = 1 :=
    bitCnt_eq_one.mpr htau
  have h2 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oV]! = 0 :=
    bitCnt_eq_zero.mpr htav
  have h3 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oU]! = 0 :=
    bitCnt_eq_zero.mpr htbu
  have h4 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oV]! = 1 :=
    bitCnt_eq_one.mpr htbv
  have hkey : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wf]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wf]! := by
    omega
  have hbit := bitCnt_inj.mp hkey
  rw [hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wa) (by omega)),
    hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wb) (by omega))]
  exact hbit

end

section

variable {st : RefineSt n} {level tc oU oV w1 w2 : Nat}

/-- Complementary pairs of a four-cell are equally adjacent. -/
theorem fourCell_comp
    (hIt : IterOk ctx level st)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hnd : ([oU, oV, w1, w2] : List Nat).Nodup) :
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w1]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w2]! ∧
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w2]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w1]! ∧
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + oV]! =
      (ctx.g[st.lab[tc + w1]!]!).mem st.lab[tc + w2]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hbd : ∀ x ∈ ([oU, oV, w1, w2] : List Nat), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have : x = w2 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hm : tc + 3 + 1 - tc = 4 := by omega
  -- each member's count into the cell, reindexed by the four names
  have hdeg : ∀ o, o ≤ 3 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w2]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hC
    rw [hm] at h
    rw [h, sum_range_of_distinct _ (by simp) hnd hbd]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  -- the diagonal terms vanish and the off-diagonal ones are symmetric
  have hz : ∀ o, o ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + o]! = 0 := by
    intro o ho
    exact bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsy : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + o']! =
        bitCnt ctx.g[st.lab[tc + o']!]! st.lab[tc + o]! := by
    intro o o' ho ho'
    exact bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  -- the four degrees agree
  have hUV := hE _ hC _ hC oU oV (by omega) (by omega)
  have hUw1 := hE _ hC _ hC oU w1 (by omega) (by omega)
  have hUw2 := hE _ hC _ hC oU w2 (by omega) (by omega)
  rw [hdeg oU hoU, hdeg oV hoV] at hUV
  rw [hdeg oU hoU, hdeg w1 hw1] at hUw1
  rw [hdeg oU hoU, hdeg w2 hw2] at hUw2
  have e1 := hz oU hoU
  have e2 := hz oV hoV
  have e3 := hz w1 hw1
  have e4 := hz w2 hw2
  have s1 := hsy oV oU hoV hoU
  have s2 := hsy w1 oU hw1 hoU
  have s3 := hsy w1 oV hw1 hoV
  have s4 := hsy w2 oU hw2 hoU
  have s5 := hsy w2 oV hw2 hoV
  have s6 := hsy w2 w1 hw2 hw1
  obtain ⟨c1, c2, c3⟩ :=
    reg4_comp (e01 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oV]!)
      (e02 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + w1]!)
      (e03 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + w2]!)
      (e12 := bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + w1]!)
      (e13 := bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + w2]!)
      (e23 := bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[tc + w2]!)
      (by omega) (by omega) (by omega)
  exact ⟨bitCnt_inj.mp c2, bitCnt_inj.mp c3, bitCnt_inj.mp c1⟩

end

end Hex.GraphIso.Nauty
