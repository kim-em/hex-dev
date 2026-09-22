/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Matrix

public section

/-! Ordered support products and zero-count pruning. The pruning lemma uses
uniqueness of the actual checked system, without inferring support from rank. -/
namespace Hex.SignDet

/-- Cartesian product in left-major concatenation order. -/
@[expose] def product (xs ys : List (List α)) : List (List α) :=
  xs.flatMap fun x => ys.map (x ++ ·)

/-- Restriction to complete child supports puts a parent condition in their
Cartesian product. This step requires both child membership hypotheses. -/
theorem mem_product {xs ys : List (List α)} {x y : List α}
    (hx : x ∈ xs) (hy : y ∈ ys) : x ++ y ∈ product xs ys := by
  exact List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

/-- All and only strictly positive columns, in their original order. -/
@[expose] def System.positive {r : Nat} (s : System r) : List (Fin r) :=
  (List.finRange r).filter fun i => s.counts[i] > 0

/-- The retained support is computed, never supplied by the certificate. -/
@[expose] def System.support {r : Nat} (s : System r) : List (List Int) :=
  s.positive.map fun i => s.columns[i]

/-- Every positive entry in any solution of an accepted system is retained.
For semantic use, the caller must separately establish that actual counts
satisfy the equations on an already complete candidate support. -/
theorem System.mem_support {r : Nat} {arity : Nat} {s : System r}
    (h : s.check arity = true) (v : Vector Int r)
    (hv : momentMatrix s.rows s.columns * v = s.values)
    (i : Fin r) (hp : 0 < v[i]) : s.columns[i] ∈ s.support := by
  have he := s.unique h v hv
  subst v
  apply List.mem_map.mpr
  refine ⟨i, ?_, rfl⟩
  simp only [System.positive, List.mem_filter, List.mem_finRange, decide_eq_true_eq,
    true_and]
  exact hp

/-- Zero-column removal keeps the matrix's original row order. -/
@[expose] def System.retainedMatrix {r : Nat} (s : System r) :
    Matrix Int r s.positive.length :=
  Matrix.selectCols (momentMatrix s.rows s.columns) s.positive.toArray.toVector

end Hex.SignDet
