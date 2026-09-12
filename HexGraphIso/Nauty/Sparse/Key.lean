/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse
public import HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std
attribute [local instance] lexOrd

/-- Compare sorted sparse rows: smaller degree wins, and with equal degrees
the row containing the first differing vertex wins. -/
@[expose] def rowCmp (a b : List (Fin n)) : Ordering :=
  compare (b.length, b) (a.length, a)

instance : TransCmp (rowCmp (n := n)) :=
  inferInstanceAs (TransCmp (fun a b : List (Fin n) =>
    compareOn (fun r : List (Fin n) => (r.length, r)) b a))

instance : LawfulEqCmp (rowCmp (n := n)) where
  eq_of_compare h := (congrArg Prod.snd (LawfulEqOrd.eq_of_compare h)).symm

/-- Canonical sparse storage supplies sorted rows without dense expansion. -/
@[expose] def graphRows (G : Hex.SparseGraph n) : List (List (Fin n)) :=
  List.ofFn fun i => (G.nbrs i).toList

theorem graphRows_injective : Function.Injective (graphRows (n := n)) := by
  intro G H h
  apply Hex.SparseGraph.ext
  intro i j
  have hr := congrArg (fun rows : List (List (Fin n)) => rows[i.val]!) h
  rw [getElem!_pos (graphRows G) i.val (by simp [graphRows]),
    getElem!_pos (graphRows H) i.val (by simp [graphRows])] at hr
  simp only [graphRows, List.getElem_ofFn] at hr
  rw [Bool.eq_iff_iff, ← Hex.SparseGraph.mem_nbrs, ← Hex.SparseGraph.mem_nbrs,
    ← Array.mem_toList_iff, ← Array.mem_toList_iff, hr]

/-- Sparse nauty's row-by-row canonical graph order. -/
@[expose] def graphCmp (G H : Hex.SparseGraph n) : Ordering :=
  List.compareLex rowCmp (graphRows G) (graphRows H)

instance : TransCmp (graphCmp (n := n)) where
  eq_swap := OrientedCmp.eq_swap (cmp := List.compareLex rowCmp)
  isLE_trans := TransCmp.isLE_trans (cmp := List.compareLex rowCmp)

instance : LawfulEqCmp (graphCmp (n := n)) where
  eq_of_compare h := graphRows_injective
    (LawfulEqCmp.eq_of_compare (cmp := List.compareLex rowCmp) h)

/-- A sparse leaf key, with a normalized sparse graph and its path codes.
This type is distinct from the dense key and its adjacency-row ordering. -/
structure Key (n : Nat) where
  codes : List Nat
  graph : Hex.SparseGraph n
deriving DecidableEq

namespace Key

/-- Codes precede graph comparison; a terminal code uses `codeSentinel`. -/
@[expose] def cmp (a b : Key n) : Ordering :=
  (compare a.codes b.codes).then (graphCmp a.graph b.graph)

private instance : TransCmp (fun a b : Key n => graphCmp a.graph b.graph) where
  eq_swap := OrientedCmp.eq_swap (cmp := graphCmp)
  isLE_trans := TransCmp.isLE_trans (cmp := graphCmp)

instance : TransCmp (cmp (n := n)) :=
  inferInstanceAs (TransCmp (compareLex (compareOn Key.codes)
    (fun a b : Key n => graphCmp a.graph b.graph)))

instance : LawfulEqCmp (cmp (n := n)) where
  eq_of_compare {a b} h := by
    have h' : a.codes = b.codes ∧ a.graph = b.graph := by
      simpa only [cmp, Ordering.then_eq_eq, LawfulEqOrd.compare_eq_iff_eq,
        LawfulEqCmp.compare_eq_iff_eq] using h
    cases a
    cases b
    cases h'.1
    cases h'.2
    rfl

@[simp] theorem cmp_eq {a b : Key n} : cmp a b = .eq ↔ a = b :=
  LawfulEqCmp.compare_eq_iff_eq

theorem cmp_swap {a b : Key n} : cmp a b = .gt ↔ cmp b a = .lt :=
  OrientedCmp.gt_iff_lt

theorem cmp_trans {a b c : Key n} (hab : cmp a b = .gt) (hbc : cmp b c = .gt) :
    cmp a c = .gt := TransCmp.gt_trans hab hbc

/-- Non-strict comparison used in subtree coverage contracts. -/
@[expose] def Le (a b : Key n) : Prop := (cmp a b).isLE = true

theorem le_refl (a : Key n) : Le a a := ReflCmp.isLE_rfl

theorem le_trans {a b c : Key n} (hab : Le a b) (hbc : Le b c) : Le a c :=
  TransCmp.isLE_trans hab hbc

theorem le_antisymm {a b : Key n} (hab : Le a b) (hba : Le b a) : a = b :=
  cmp_eq.mp (OrientedCmp.isLE_antisymm hab hba)

/-- Select the greater key, keeping the first argument on a tie. -/
@[expose] def max (a b : Key n) : Key n := if cmp a b = .lt then b else a

theorem max_mem (a b : Key n) : max a b = a ∨ max a b = b := by
  unfold max
  split <;> simp

theorem le_max_left (a b : Key n) : Le a (max a b) := by
  unfold max
  split
  · next h => exact Ordering.isLE_of_eq_lt h
  · exact le_refl a

theorem le_max_right (a b : Key n) : Le b (max a b) := by
  unfold max
  split
  · exact le_refl b
  · next h =>
    have hs := OrientedCmp.eq_swap (cmp := cmp) (a := b) (b := a)
    unfold Le
    rw [hs]
    cases hab : cmp a b <;> simp_all

theorem max_le {a b c : Key n} (ha : Le a c) (hb : Le b c) : Le (max a b) c := by
  rcases max_mem a b with h | h <;> rwa [h]

end Key

end Hex.GraphIso.Nauty.Sparse
