/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Basic
import all HexGraphIso.Nauty.Equitable.Basic

public section

/-! Neighbour counts and balanced sets of distinguishing vertices. -/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Counting toolkit -/

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

/-! # Small cells in an equitable partition -/

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

/-- Equitability balances vertices adjacent to the first member alone
and vertices adjacent to the second member alone, in every cell. -/
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

end Hex.GraphIso.Nauty
