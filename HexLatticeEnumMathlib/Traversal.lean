/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Enumerate
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat}

/-- Complete fixed-radius traversal appends each newly feasible point exactly once. -/
@[expose] def BallResult (before : SearchState n m) (run : Traversal n m) (P : Point n m → Prop) : Prop :=
  run.pending = [] ∧ run.tree.isSome = true ∧ run.state.radius = before.radius ∧
    ∃ fresh : List (Point n m), run.state.points = fresh ++ before.points ∧ fresh.Nodup ∧
      ∀ q, q ∈ fresh ↔ P q

/-- Combining disjoint complete child searches preserves exhaustion and exact point coverage. -/
theorem children_spec (z : Vector Int n) (cost : Rat) (k : Nat) (interval : Interval)
    (visit : Int → SearchState n m → Traversal n m) (P : Int → Point n m → Prop)
    (r : Rat) (hvisit : ∀ a s, s.radius = r → BallResult s (visit a s) (P a))
    (hdisjoint : ∀ a b q, P a q → P b q → a = b)
    (fuel : Nat) (cursor : Coefficients) (s : SearchState n m) (trees : List (Int × Tree))
    (hn : (Coefficients.toList.go fuel cursor).Nodup) (hs : s.radius = r) :
    BallResult s (traverseAux.children z cost true k interval visit fuel cursor s trees)
      (fun q => ∃ a ∈ Coefficients.toList.go fuel cursor, P a q) := by
  induction fuel generalizing cursor s trees with
  | zero =>
    simp only [traverseAux.children, BallResult, Coefficients.toList.go]
    refine ⟨True.intro, rfl, True.intro, [], by simp, by simp, ?_⟩
    simp
  | succ fuel ih =>
    cases he : cursor.next? with
    | none =>
      simp only [traverseAux.children, he, BallResult, Coefficients.toList.go]
      refine ⟨True.intro, rfl, True.intro, [], by simp, by simp, ?_⟩
      simp
    | some step =>
      rcases step with ⟨a, cursor'⟩
      obtain ⟨hempty, htree, hradius, fresh, hfresh, hnodup, hmem⟩ := hvisit a s hs
      have hn' : a ∉ Coefficients.toList.go fuel cursor' ∧
          (Coefficients.toList.go fuel cursor').Nodup := by
        simpa [Coefficients.toList.go, he] using hn
      simp only [traverseAux.children, he, hempty, List.isEmpty_nil,
        ite_true]
      obtain ⟨htail, htree', hradius', rest, hrest, hrestnodup, hrestmem⟩ :=
        ih cursor' (visit a s).state ((a, (visit a s).tree.getD .empty) :: trees) hn'.2 (hradius.trans hs)
      refine ⟨htail, htree', hradius'.trans hradius, rest ++ fresh, ?_, ?_, ?_⟩
      · rw [hrest, hfresh, List.append_assoc]
      · apply List.nodup_append.mpr
        refine ⟨hrestnodup, hnodup, ?_⟩
        intro q hq q' hq' heq
        subst q'
        obtain ⟨b, hb, hbp⟩ := (hrestmem q).mp hq
        have hab := hdisjoint a b q ((hmem q).mp hq') hbp
        exact hn'.1 (hab ▸ hb)
      · intro q
        simp only [List.mem_append, hrestmem, hmem, Coefficients.toList.go, he,
          List.mem_cons]
        constructor
        · rintro (⟨b, hb, hp⟩ | hp)
          · exact ⟨b, Or.inr hb, hp⟩
          · exact ⟨a, Or.inl rfl, hp⟩
        · rintro ⟨b, hb, hp⟩
          rcases hb with rfl | hb
          · exact Or.inr hp
          · exact Or.inl ⟨b, hb, hp⟩

/-- Coefficients agree on the suffix already fixed by traversal. -/
@[expose] def Matches (k : Nat) (z w : Vector Int n) : Prop :=
  ∀ i : Fin n, k ≤ i.val → w[i] = z[i]

/-- Setting the next coefficient extends the suffix by exactly one coordinate. -/
theorem matches_set (k : Nat) (hk : k < n) (z w : Vector Int n) (a : Int) :
    Matches k (z.set k a hk) w ↔ Matches (k + 1) z w ∧ w[k] = a := by
  constructor
  · intro h
    constructor
    · intro i hi
      have he := h i (by omega)
      simpa only [Fin.getElem_fin, Vector.getElem_set_ne hk i.isLt (by omega)] using he
    · have he := h ⟨k, hk⟩ (by rfl)
      simpa using he
  · rintro ⟨h, ha⟩ i hi
    by_cases hik : i.val = k
    · have he : i = ⟨k, hk⟩ := Fin.ext hik
      subst i
      simpa using ha
    · have he := h i (by omega)
      simpa only [Fin.getElem_fin, Vector.getElem_set_ne hk i.isLt (Ne.symm hik)] using he

/-- A directly reconstructed point satisfying the fixed suffix and closed-ball bound. -/
@[expose] def Feasible (b : Basis n m) (t : Vector Rat m) (r : Rat) (k : Nat)
    (z : Vector Int n) (q : Point n m) : Prop :=
  q = point b t q.coefficients ∧ Matches k z q.coefficients ∧ q.distanceSq ≤ r

/-- Fixing the next coordinate reduces feasibility to the extended suffix and that coordinate. -/
theorem feasible_set (b : Basis n m) (t : Vector Rat m) (r : Rat) (k : Nat) (hk : k < n)
    (z : Vector Int n) (a : Int) (q : Point n m) :
    Feasible b t r k (z.set k a hk) q ↔
      Feasible b t r (k + 1) z q ∧ q.coefficients[k] = a := by
  simp only [Feasible, matches_set]
  tauto

/-- A fully fixed suffix admits exactly its directly reconstructed point within the radius. -/
theorem feasible_zero (b : Basis n m) (t : Vector Rat m) (r : Rat)
    (z : Vector Int n) (q : Point n m) :
    Feasible b t r 0 z q ↔ q = point b t z ∧ (point b t z).distanceSq ≤ r := by
  constructor
  · rintro ⟨hq, hm, hr⟩
    have he : q.coefficients = z := by
      apply Vector.ext
      intro i hi
      exact hm ⟨i, hi⟩ (Nat.zero_le i)
    rw [he] at hq
    exact ⟨hq, by rwa [← hq]⟩
  · rintro ⟨rfl, hr⟩
    exact ⟨rfl, fun _ _ => rfl, hr⟩

/-- Exact child bounds characterize all feasible completions of a suffix. -/
theorem feasible_children (b : Basis n m) (t : Vector Rat m) (p : Prepared b t)
    (hp : p.Valid) (r : Rat) (k : Nat) (hk : k < n) (z : Vector Int n) (q : Point n m) :
    let interval := bounds (p.centre z ⟨k, hk⟩) p.norms[k]
      (r - p.residual.normSq - suffix p.toData z (k + 1))
    (∃ a ∈ (coefficients interval (p.centre z ⟨k, hk⟩)).toList,
      Feasible b t r k (z.set k a hk) q) ↔ Feasible b t r (k + 1) z q := by
  dsimp only
  constructor
  · rintro ⟨a, _, h⟩
    exact ((feasible_set b t r k hk z a q).mp h).1
  · intro h
    refine ⟨q.coefficients[k], ?_, (feasible_set b t r k hk z _ q).mpr ⟨h, rfl⟩⟩
    rw [mem_coefficients]
    apply completion_bound p.toData b.rows t hp z q.coefficients k hk r
    · intro j hj
      exact h.2.1 j (by omega)
    · have he := h.2.2
      have hd : q.distanceSq = distance (Hex.Matrix.vecMul q.coefficients b.rows) t := by
        conv_lhs => rw [h.1]
        rfl
      rwa [← hd]

/-- Unlimited fixed-radius traversal exhausts exactly the feasible suffix completions. -/
theorem traverse_ball (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (k : Nat) (hk : k ≤ n) (z : Vector Int n) (s : SearchState n m) :
    BallResult s
      (traverseAux b t p {} .ball p.residual.normSq k hk z (suffix p.toData z k) s)
      (Feasible b t s.radius k z) := by
  induction k generalizing z s with
  | zero =>
    rw [traverseAux]
    simp only [room, Bool.not_true, Bool.and_false, Bool.false_or, Bool.false_eq_true,
      ite_false, beq_self_eq_true, ite_true]
    split_ifs with hdist
    · refine ⟨rfl, rfl, rfl, [], by simp, by simp, ?_⟩
      intro q
      rw [feasible_zero]
      simp only [List.not_mem_nil, false_iff, not_and]
      intro _
      exact not_le.mpr hdist
    · refine ⟨rfl, rfl, rfl, [point b t z], rfl, by simp, ?_⟩
      intro q
      rw [feasible_zero]
      simp [le_of_not_gt hdist]
  | succ k ih =>
    rw [traverseAux]
    simp only [room, Bool.not_true, Bool.and_false, Bool.false_or, Bool.false_eq_true,
      ite_false, beq_self_eq_true, ite_true]
    split_ifs with hempty
    · refine ⟨rfl, rfl, rfl, [], by simp, by simp, ?_⟩
      intro q
      simp only [List.not_mem_nil, false_iff]
      intro hq
      obtain ⟨a, ha, _⟩ := (feasible_children b t p hp s.radius k (by omega) z q).mpr hq
      rw [mem_coefficients] at ha
      have he : (bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))).size = 0 := by
        simpa using hempty
      unfold Interval.size at he
      omega
    · let interval := bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))
      let visit := fun a (state : SearchState n m) =>
        traverseAux b t p {} .ball p.residual.normSq k (by omega) (z.set k a (by omega))
          (suffix p.toData z (k + 1) + p.norms[k] *
            ((a : Rat) - p.centre z ⟨k, by omega⟩) * ((a : Rat) - p.centre z ⟨k, by omega⟩)) state
      let state : SearchState n m := { s with counts :=
        { s.counts with nodes := s.counts.nodes + 1, certificateNodes := s.counts.certificateNodes + 1 } }
      have hchildren := children_spec z (suffix p.toData z (k + 1)) k interval visit
        (fun a => Feasible b t s.radius k (z.set k a (by omega))) s.radius
        (fun a state hs => by
          dsimp only [visit]
          have h := ih (by omega) (z.set k a (by omega)) state
          rw [suffix_step p.toData z k (Nat.lt_of_succ_le hk) a] at h
          simpa only [hs, Prepared.centre] using h)
        (fun a c q ha hc => by
          have ha' := ((feasible_set b t s.radius k (by omega) z a q).mp ha).2
          have hc' := ((feasible_set b t s.radius k (by omega) z c q).mp hc).2
          exact ha'.symm.trans hc')
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state []
        (coefficients_spec interval (p.centre z ⟨k, by omega⟩)).2 rfl
      have hpred : (fun q => ∃ a ∈ (coefficients interval (p.centre z ⟨k, by omega⟩)).toList,
          Feasible b t s.radius k (z.set k a (by omega)) q) = Feasible b t s.radius (k + 1) z := by
        funext q
        exact propext (feasible_children b t p hp s.radius k (by omega) z q)
      change BallResult s (traverseAux.children z (suffix p.toData z (k + 1)) true k interval visit
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state []) _
      rw [← hpred]
      exact hchildren

/-- The full unbudgeted run has an exhaustive tree and exactly the reconstructed ball points. -/
theorem ball_complete (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    BallResult { radius := r }
      (traverse b t (prepare b t) {} .ball n (Nat.le_refl n) 0 0 { radius := r })
      (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ r) := by
  have h := traverse_ball b t (prepare b t) (prepare_valid b t) n (Nat.le_refl n) 0 { radius := r }
  rw [suffix_rank] at h
  have hp : Feasible b t r n 0 = (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ r) := by
    funext q
    apply propext
    simp [Feasible, Matches, not_le.mpr]
  rw [hp] at h
  exact h

/-- Complete enumeration contains exactly the directly reconstructed points in the closed ball. -/
theorem enumerate_point_spec (b : Basis n m) (t : Vector Rat m) (r : Rat) (q : Point n m) :
    q ∈ enumerate b t r ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
  obtain ⟨_, _, _, fresh, hfresh, _, hmem⟩ := ball_complete b t r
  simp only [enumerate, sortPoints, Hex.List.sort_eq, List.mem_mergeSort]
  rw [hfresh]
  simpa using hmem q

/-- Complete enumeration never repeats a coefficient/ambient/distance record. -/
theorem enumerate_nodup (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    (enumerate b t r).Nodup := by
  obtain ⟨_, _, _, fresh, hfresh, hn, _⟩ := ball_complete b t r
  unfold enumerate sortPoints
  rw [Hex.List.sort_eq]
  apply (List.mergeSort_perm _ _).symm.nodup
  rw [hfresh]
  simpa using hn

/-- Reported coefficients reconstruct their ambient point and exact distance. -/
theorem enumerate_reconstruct (b : Basis n m) (t : Vector Rat m) (r : Rat) (q : Point n m)
    (hq : q ∈ enumerate b t r) :
    q.ambient = vector b q.coefficients ∧ q.distanceSq = distanceSq b t q.coefficients := by
  have he := ((enumerate_point_spec b t r q).mp hq).1
  constructor
  · conv_lhs => rw [he]
    rfl
  · conv_lhs => rw [he]
    rfl

/-- Enumeration exhausts the integer row lattice in the closed ball, including off-span targets. -/
theorem enumerate_spec (b : Basis n m) (t : Vector Rat m) (r : Rat) (v : Vector Int m) :
    v ∈ (enumerate b t r).map Point.ambient ↔ b.rows.memLattice v ∧ distance v t ≤ r := by
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    obtain ⟨ha, hd⟩ := enumerate_reconstruct b t r q hq
    refine ⟨⟨q.coefficients, ha.symm⟩, ?_⟩
    rw [ha]
    change distanceSq b t q.coefficients ≤ r
    rw [← hd]
    exact ((enumerate_point_spec b t r q).mp hq).2
  · rintro ⟨⟨z, rfl⟩, hr⟩
    apply List.mem_map.mpr
    refine ⟨point b t z, ?_, rfl⟩
    rw [enumerate_point_spec]
    exact ⟨rfl, hr⟩

/-- Uniqueness of independent coefficient representations also excludes duplicate ambient vectors. -/
theorem enumerate_ambient_nodup (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    ((enumerate b t r).map Point.ambient).Nodup := by
  apply List.Nodup.map_on ?_ (enumerate_nodup b t r)
  intro q hq q' hq' he
  obtain ⟨hqv, _⟩ := enumerate_reconstruct b t r q hq
  obtain ⟨hqv', _⟩ := enumerate_reconstruct b t r q' hq'
  have hz : q.coefficients = q'.coefficients := vector_injective b (hqv.symm.trans (he.trans hqv'))
  have hqpoint := ((enumerate_point_spec b t r q).mp hq).1
  have hqpoint' := ((enumerate_point_spec b t r q').mp hq').1
  rw [hqpoint, hqpoint', hz]

/-- Public sorting puts ambient coordinates in nondecreasing lexicographic order. -/
theorem sortPoints_sorted (ps : List (Point n m)) :
    (sortPoints ps).Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) := by
  have ht : ∀ a b c : Point n m, pointLE a b → pointLE b c → pointLE a c := by
    intro a b c hab hbc
    simp only [pointLE, decide_eq_true_eq] at hab hbc ⊢
    exact Ordering.isLE_iff_ne_gt.mp (Std.TransOrd.isLE_trans
      (Ordering.isLE_iff_ne_gt.mpr hab) (Ordering.isLE_iff_ne_gt.mpr hbc))
  have hall : ∀ a b : Point n m, pointLE a b || pointLE b a := by
    intro a b
    simp only [pointLE, Bool.or_eq_true, decide_eq_true_eq]
    have hswap := Std.OrientedOrd.eq_swap (a := a.ambient.toList) (b := b.ambient.toList)
    cases hab : compare a.ambient.toList b.ambient.toList <;>
      cases hba : compare b.ambient.toList a.ambient.toList <;> simp_all
  have hs := List.pairwise_mergeSort ht hall ps
  simpa only [sortPoints, Hex.List.sort_eq, pointLE, decide_eq_true_eq] using hs

/-- Complete enumeration is sorted independently of the coefficient visitation order. -/
theorem enumerate_sorted (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    (enumerate b t r).Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) :=
  sortPoints_sorted _

/-- The sorted ambient answer list depends only on the integer lattice, even
when its two presentations use different index types for their rows. -/
theorem enumerate_lattice {n' : Nat} (b : Basis n m) (c : Basis n' m)
    (h : ∀ v, b.rows.memLattice v ↔ c.rows.memLattice v) (t : Vector Rat m) (r : Rat) :
    (enumerate b t r).map Point.ambient = (enumerate c t r).map Point.ambient := by
  have hp : ((enumerate b t r).map Point.ambient).Perm
      ((enumerate c t r).map Point.ambient) := by
    apply (List.perm_ext_iff_of_nodup (enumerate_ambient_nodup b t r)
      (enumerate_ambient_nodup c t r)).mpr
    intro v
    simp only [enumerate_spec, h]
  apply hp.eq_of_pairwise (le := fun v w => compare v.toList w.toList ≠ .gt)
    ?_ ((List.pairwise_map).mpr (enumerate_sorted b t r))
    ((List.pairwise_map).mpr (enumerate_sorted c t r))
  intro v w _ _ hvw hwv
  apply Vector.toList_inj.mp
  apply Std.LawfulEqOrd.eq_of_compare
  exact Std.OrientedCmp.isLE_antisymm
    (Ordering.isLE_iff_ne_gt.mpr hvw) (Ordering.isLE_iff_ne_gt.mpr hwv)

/-- Exact distances are determined by the ambient answer, independently of its coordinates. -/
theorem enumerate_distances (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    (enumerate b t r).map (fun q => (q.ambient, q.distanceSq)) =
      ((enumerate b t r).map Point.ambient).map (fun v => (v, distance v t)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  obtain ⟨ha, hd⟩ := enumerate_reconstruct b t r q hq
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  rw [hd, ha]
  rfl

/-- Changing any independent presentation of the same lattice preserves the
entire ordered list of ambient points and squared distances. -/
theorem enumerate_lattice_distances {n' : Nat} (b : Basis n m) (c : Basis n' m)
    (h : ∀ v, b.rows.memLattice v ↔ c.rows.memLattice v) (t : Vector Rat m) (r : Rat) :
    (enumerate b t r).map (fun q => (q.ambient, q.distanceSq)) =
      (enumerate c t r).map (fun q => (q.ambient, q.distanceSq)) := by
  rw [enumerate_distances, enumerate_distances, enumerate_lattice b c h]

end HexLatticeEnumMathlib
