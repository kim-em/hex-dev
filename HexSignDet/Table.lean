/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Induction

public section

namespace Hex.SignDet

/-- Sparse natural counts on distinct well-formed sign conditions. Root
completeness is a property of the producing replay and its interpretation,
not a consequence of these structural invariants alone. -/
structure SignTable (arity : Nat) where
  private mk ::
  rows : Array (List Int × Nat)
  wellFormed : ∀ row ∈ rows.toList, row.1.length = arity ∧
    (∀ s ∈ row.1, s = -1 ∨ s = 0 ∨ s = 1) ∧ 0 < row.2
  distinct : (rows.toList.map Prod.fst).Nodup

/-- Total lookup, including zero for every omitted condition. -/
@[expose] def SignTable.count {arity : Nat} (t : SignTable arity) (condition : List Int) : Nat :=
  (t.rows.toList.lookup condition).getD 0

/-- Convert only positive coordinates; zero counts remain implicit. -/
@[expose] def System.tableRows {r : Nat} (s : System r) : Array (List Int × Nat) :=
  (s.positive.map fun i => (s.columns[i], s.counts[i].toNat)).toArray

/-- Literal sparse lookup used by replay without constructing an opaque table. -/
@[expose] def System.count {r : Nat} (s : System r) (c : List Int) : Nat :=
  (s.tableRows.toList.lookup c).getD 0

theorem System.tableRows_valid {r arity : Nat} (s : System r) (h : s.check arity = true) :
    ∀ row ∈ s.tableRows.toList, row.1.length = arity ∧
      (∀ v ∈ row.1, v = -1 ∨ v = 0 ∨ v = 1) ∧ 0 < row.2 := by
  intro row hr
  simp only [tableRows, List.toList_toArray] at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hc : s.columns.toList.all (fun c => decide (c.length = arity) &&
      c.all (fun v => decide (v = -1 ∨ v = 0 ∨ v = 1))) = true := by
    simp only [System.check, Bool.and_eq_true] at h
    exact h.1.1.1.1.2
  have hm : s.columns[i] ∈ s.columns.toList := by
    exact List.getElem_mem (by simp)
  have hw := List.all_eq_true.mp hc _ hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  have hp : 0 < s.counts[i] := by simpa [positive] using hi
  exact ⟨hw.1, hw.2, by omega⟩

theorem System.tableRows_distinct {r arity : Nat} (s : System r) (h : s.check arity = true) :
    (s.tableRows.toList.map Prod.fst).Nodup := by
  have hc : s.columns.toList.Nodup := by
    simp only [System.check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.2
  have hi : s.positive.Nodup := List.Pairwise.filter _ (List.nodup_finRange r)
  simp only [tableRows, List.toList_toArray, List.map_map, Function.comp_def]
  apply hi.map (fun i => s.columns[i])
  intro i j hne he
  apply hne
  apply Fin.ext
  exact hc.eq_of_getElem_eq (by simp) (by simp)
    (by simpa only [Vector.getElem_toList, Fin.getElem_fin] using he)

/-- Extract the checked integer system's sparse counts with an exact cast.
This is a finite representation adapter; its root interpretation must be
derived from the complete recursive replay. -/
def SignTable.ofSystem {r arity : Nat} (s : System r) (h : s.check arity = true) : SignTable arity :=
  ⟨s.tableRows, s.tableRows_valid h, s.tableRows_distinct h⟩

private theorem lookup_member {rows : List (List Int × Nat)}
    (h : (rows.map Prod.fst).Nodup) {c : List Int} {n : Nat} (hm : (c, n) ∈ rows) :
    rows.lookup c = some n := by
  induction rows with
  | nil => simp at hm
  | cons row rows ih =>
    obtain ⟨d, k⟩ := row
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      simp
    · have hne : c ≠ d := by
        intro he
        apply h.1
        exact List.mem_map.mpr ⟨(c, n), hm, he⟩
      have hb : (c == d) = false := by simpa using hne
      simpa only [List.lookup_cons, hb] using ih h.2 hm

/-- Every stored row is returned exactly; distinctness prevents shadowing. -/
theorem SignTable.count_mem {arity : Nat} (t : SignTable arity) {c : List Int} {n : Nat}
    (h : (c, n) ∈ t.rows.toList) : t.count c = n := by
  simp only [count, lookup_member t.distinct h, Option.getD_some]

/-- An absent condition has count zero, without a sentinel or an unchecked
integer-to-natural conversion. -/
theorem SignTable.count_omitted {arity : Nat} (t : SignTable arity) (c : List Int)
    (h : c ∉ t.rows.toList.map Prod.fst) : t.count c = 0 := by
  have hn : t.rows.toList.lookup c = none := by
    apply List.lookup_eq_none_iff.mpr
    intro row hr
    simp only [bne_iff_ne]
    intro he
    exact h (List.mem_map.mpr ⟨row, hr, he.symm⟩)
  simp only [count, hn, Option.getD_none]

/-- Positive lookup cannot come from an omitted condition. -/
theorem SignTable.mem_of_count_pos {arity : Nat} (t : SignTable arity) {c : List Int}
    (hp : 0 < t.count c) : ∃ n, (c, n) ∈ t.rows.toList := by
  by_cases hm : c ∈ t.rows.toList.map Prod.fst
  · obtain ⟨⟨d, n⟩, hn, he⟩ := List.mem_map.mp hm
    exact ⟨n, he ▸ hn⟩
  · rw [t.count_omitted c hm] at hp
    omega

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Extract a sparse table only after the full recursive replay has passed.
The companion must still supply the root interpretation of its query values. -/
def Replay.table {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} (t : Replay E Ctx)
    (h : t.check sign context p a b qs = true) : SignTable qs.length :=
  SignTable.ofSystem t.node.system (Node.check_bindings (Replay.check_node h)).2

/-- Opaque table extraction preserves the literal rows checked by replay. -/
theorem Replay.table_rows {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} (t : Replay E Ctx)
    (h : t.check sign context p a b qs = true) :
    (t.table h).rows = t.node.system.tableRows := by rfl

/-- Literal replay lookup agrees with the opaque validated table API. -/
theorem Replay.table_lookup {sign : E → Int} {context : Ctx} {p : DensePoly E} {a b : Endpoint E}
    {qs : List (DensePoly E)} (t : Replay E Ctx)
    (h : t.check sign context p a b qs = true) (c : List Int) :
    (t.table h).count c = t.node.system.count c := by rfl

/-- Every lookup, including omitted conditions, agrees with the finite
observations interpreted by the actual accepted replay. Root-sum semantics
are required to instantiate this theorem with roots. -/
theorem Replay.table_count {sign : E → Int} {context : Ctx}
    {p : DensePoly E} {a b : Endpoint E} {qs : List (DensePoly E)}
    (t : Replay E Ctx) {xs : List (List Int)}
    (hc : t.check sign context p a b qs = true)
    (ho : Observations qs.length xs) (hm : t.Interprets qs.length xs) (c : List Int) :
    (t.table hc).count c = xs.countP (fun x => decide (x = c)) := by
  obtain ⟨cover, counts⟩ := t.support_complete hc ho hm
  by_cases hs : c ∈ t.node.system.support
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp hs
    have hr : (c, t.node.system.counts[i].toNat) ∈ (t.table hc).rows.toList := by
      simp only [table, SignTable.ofSystem, System.tableRows, List.toList_toArray]
      exact List.mem_map.mpr ⟨i, hi, by simp [he]⟩
    rw [SignTable.count_mem _ hr]
    have hvalue := congrArg (fun v : Vector Int t.node.size => v[i]) counts
    simp only [SignDet.counts, Fin.getElem_fin, Vector.getElem_ofFn] at hvalue
    simp only [Fin.getElem_fin]
    rw [← hvalue, Int.toNat_natCast]
    congr 1
    funext x
    exact congrArg (fun d : List Int => decide (x = d)) he
  · have hz : (t.table hc).count c = 0 := by
      apply SignTable.count_omitted
      simpa only [table, SignTable.ofSystem, System.tableRows, List.toList_toArray,
        List.map_map, Function.comp_def, System.support] using hs
    rw [hz]
    symm
    apply List.countP_eq_zero.mpr
    intro x hx
    have hne : x ≠ c := fun he => hs (he ▸ cover x hx)
    simpa using hne

end Hex.SignDet
