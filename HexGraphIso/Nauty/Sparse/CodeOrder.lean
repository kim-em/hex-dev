/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeRead

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std

/-- The shared code machine and the native sparse key use the same
lexicographic order on refinement codes. -/
theorem codes_compare (xs ys : List Nat) : listCmp compare xs ys = compare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      rw [listCmp, List.compare_cons_cons]
      cases compare x y <;> simp [ih, Ordering.then]

/-- A frozen code rejection dominates every continuation, independently
of the native sparse rows below it. -/
theorem codes_less {cs bs : List Nat} {st : State n}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1))
    (ext : List Nat) (A B : Hex.SparseGraph n) :
    Key.cmp ⟨cs ++ ext, A⟩ ⟨bs ++ [codeSentinel], B⟩ = .lt := by
  have hc := codeInv_listCmp_lt h ext
  rw [codes_compare] at hc
  simp only [Key.cmp, hc, Ordering.then]

/-- A frozen positive comparison dominates the incumbent before any
sparse adjacency row is read. -/
theorem codes_greater {cs bs : List Nat} {st : State n}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 1)
    (ext : List Nat) (A B : Hex.SparseGraph n) :
    Key.cmp ⟨cs ++ ext, A⟩ ⟨bs ++ [codeSentinel], B⟩ = .gt := by
  have hc := codeInv_listCmp_gt h ext
  rw [codes_compare] at hc
  simp only [Key.cmp, hc, Ordering.then]

/-- At a shorter tied leaf, the sentinel wins against the next real
incumbent code. This uses only the shared code-order theorem. -/
theorem codes_short {cs bs : List Nat} {st : State n}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0)
    (hlen : cs.length < bs.length) (A B : Hex.SparseGraph n) :
    Key.cmp ⟨cs ++ [codeSentinel], A⟩ ⟨bs ++ [codeSentinel], B⟩ = .gt := by
  have hc := tied_short_keyCmp_gt h hlen ([] : List (VSet 0)) []
  have he : compare (cs ++ [codeSentinel]) (bs ++ [codeSentinel]) = .gt := by
    simp only [keyCmp, codes_compare, listCmp] at hc
    cases hh : compare (cs ++ [codeSentinel]) (bs ++ [codeSentinel]) <;> simp_all
  simp only [Key.cmp, he, Ordering.then]

/-- Equal complete code sequences hand the verdict to sparse row order. -/
theorem codes_tied {cs bs : List Nat} {st : State n}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0)
    (hlen : cs.length = bs.length) (A B : Hex.SparseGraph n) :
    Key.cmp ⟨cs ++ [codeSentinel], A⟩ ⟨bs ++ [codeSentinel], B⟩ = graphCmp A B := by
  rw [codeInv_eq_of_tied h hlen]
  simp only [Key.cmp, ReflCmp.compare_self, Ordering.then]

theorem Key.max_eq_left {a b : Key n} (h : Le b a) : max a b = a := by
  unfold max
  have hs := OrientedCmp.eq_swap (cmp := cmp) (a := b) (b := a)
  cases hc : cmp a b <;> simp_all [Le]

theorem Key.max_eq_right {a b : Key n} (h : cmp b a = .gt) : max a b = b := by
  rw [max, ite_eq_left (OrientedCmp.gt_iff_lt.mp h)]

end Hex.GraphIso.Nauty.Sparse
