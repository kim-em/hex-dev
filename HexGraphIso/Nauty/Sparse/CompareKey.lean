/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Compare

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std

private theorem first_order {α : Type} [Inhabited α] (cmp : α → α → Ordering)
    [ReflCmp cmp] (xs ys : List α) (i : Nat)
    (hi : i < xs.length) (hj : i < ys.length)
    (hp : ∀ j, j < i → xs[j]! = ys[j]!) (hn : cmp xs[i]! ys[i]! ≠ .eq) :
    List.compareLex cmp xs ys = cmp xs[i]! ys[i]! := by
  induction i generalizing xs ys with
  | zero =>
    cases xs <;> cases ys <;> try simp_all only [List.length_nil, Nat.not_lt_zero]
    next x xs y ys =>
      simp only [List.getElem!_cons_zero, List.compareLex_cons_cons] at *
      cases hc : cmp x y <;> simp_all
  | succ i ih =>
    cases xs <;> cases ys <;> try simp_all only [List.length_nil, Nat.not_lt_zero]
    next x xs y ys =>
      have he : x = y := by simpa using hp 0 (by omega)
      subst y
      simp only [List.compareLex_cons_cons, ReflCmp.compare_self, Ordering.eq_then,
        List.getElem!_cons_succ] at *
      apply ih xs ys (by simp_all) (by simp_all) _ hn
      intro j hj
      simpa using hp (j + 1) (by omega)

namespace Compare.Result

/-- The first unequal row determines the entire sparse graph-key comparison. -/
theorem order {A B : Hex.SparseGraph n} {r : Int × Nat} (h : Compare.Result A B r) :
    r.1 = ordInt (graphCmp A B) := by
  by_cases hi : r.2 < n
  · have hf := h.first r.2 hi rfl
    have hc := first_order rowCmp (graphRows A) (graphRows B) r.2
      (by simpa [graphRows] using hi) (by simpa [graphRows] using hi) h.agrees hf.2
    exact hf.1.trans (congrArg ordInt hc).symm
  · have hn : r.2 = n := by have := h.bound; omega
    have he : graphRows A = graphRows B := by
      apply List.ext_getElem
      · simp [graphRows]
      · intro i hi hj
        have hb : i < n := by simpa [graphRows] using hi
        have hr := h.agrees i (by omega)
        simpa only [Compare.row, getElem!_pos (graphRows A) i hi,
          getElem!_pos (graphRows B) i hj] using hr
    rw [h.terminal hn]
    simp [graphCmp, he, ReflCmp.compare_self, ordInt]

end Compare.Result

/-- The executed comparison sign agrees with the sparse canonical graph key. -/
theorem testcanlab_fst (G H : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix H n) :
    (testcanlab (.ofGraph G) R lab).1 = ordInt (graphCmp (G.relabel l.perm) H) :=
  (testcanlab_result G H R lab l hl hR).order

/-- A tie means literal equality of the normalized native sparse graphs. -/
theorem testcanlab_eq_zero (G H : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix H n) :
    (testcanlab (.ofGraph G) R lab).1 = 0 ↔ G.relabel l.perm = H := by
  rw [testcanlab_fst G H R lab l hl hR]
  have hz (c : Ordering) : ordInt c = 0 ↔ c = .eq := by cases c <;> decide
  rw [hz, LawfulEqCmp.compare_eq_iff_eq]

end Hex.GraphIso.Nauty.Sparse
