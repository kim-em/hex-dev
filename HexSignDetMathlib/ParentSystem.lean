/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.FiniteSolve
public import HexSignDetMathlib.NodeBasis

public section

namespace Hex.SignDet

private theorem product_all {α : Type*} (p : α → Bool) (xs ys : List (List α)) (a b : Nat)
    (hx : xs.all (fun x => decide (x.length = a) && x.all p) = true)
    (hy : ys.all (fun y => decide (y.length = b) && y.all p) = true) :
    (product xs ys).all (fun z => decide (z.length = a + b) && z.all p) = true := by
  apply List.all_eq_true.mpr
  intro z hz
  obtain ⟨x, hxm, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨y, hym, rfl⟩ := List.mem_map.mp hz
  have hx := List.all_eq_true.mp hx x hxm
  have hy := List.all_eq_true.mp hy y hym
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx hy
  simp [hx, hy]

private theorem support_valid {r arity : Nat} (s : System r) (h : s.check arity = true) :
    s.support.all (fun c => decide (c.length = arity) &&
      c.all (fun x => decide (x = -1 ∨ x = 0 ∨ x = 1))) = true := by
  simp only [System.check, Bool.and_eq_true] at h
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  exact List.all_eq_true.mp h.1.1.1.1.2 _ (List.getElem_mem (by simp))

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

private theorem rows_valid (n : Node E Ctx) {arity : Nat} (h : n.system.check arity = true) :
    n.rows.all (fun e => decide (e.length = arity) && e.all (· ≤ 2)) = true := by
  simp only [System.check, Bool.and_eq_true] at h
  apply List.all_eq_true.mpr
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact List.all_eq_true.mp h.1.1.1.1.1 _ (List.getElem_mem (by simp))

/-- Complete child supports construct a checked parent system on their exact
Cartesian product. The tensor identity, distinctness, integrality and
nonnegativity are derived before solving the parent's moment equations. -/
theorem Node.product_system (l r : Node E Ctx) {a b : Nat}
    (hl : l.system.check a = true) (hr : r.system.check b = true)
    (hbl : l.basis = Matrix.rankCert l.system.retainedMatrix)
    (hbr : r.basis = Matrix.rankCert r.system.retainedMatrix)
    (xs : List (List Int))
    (cl : ∀ x ∈ xs, x.take a ∈ l.system.support)
    (cr : ∀ x ∈ xs, x.drop a ∈ r.system.support) :
    let rows := productVector l.basisRows r.basisRows
    let cols := productVector l.basisCols r.basisCols
    (System.mk rows cols (counts cols xs) (SignDet.moments rows xs)
      (tensor l.basis.adj r.basis.adj) (l.basis.denom * r.basis.denom)).check (a + b) = true := by
  dsimp only
  obtain ⟨hrows, hcols, hinv⟩ := l.product_inverse r hl hr hbl hbr
  apply system_counts
  · rw [hrows]
    exact product_all _ _ _ a b (rows_valid l hl) (rows_valid r hr)
  · rw [hcols]
    exact product_all _ _ _ a b (support_valid l.system hl) (support_valid r.system hr)
  · apply Int.mul_ne_zero
    · rw [hbl]
      exact (Matrix.checkRank_iff _ _).mp l.system.basis_checks |>.1
    · rw [hbr]
      exact (Matrix.checkRank_iff _ _).mp r.system.basis_checks |>.1
  · exact hinv
  · intro x hx
    rw [hcols, ← List.take_append_drop a x]
    exact mem_product (cl x hx) (cr x hx)

end Hex.SignDet
