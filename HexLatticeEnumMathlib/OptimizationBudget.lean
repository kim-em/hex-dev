/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Budget
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- Interrupted optimization retains an attained incumbent; exhaustion also proves the lower bound. -/
@[expose] def PartialOpt (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (before : SearchState n m) (run : Traversal n m) (P : Point n m → Prop) : Prop :=
  run.state.radius ≤ before.radius ∧ Incumbent b t mode run.state ∧
    (run.pending = [] → ∀ q, P q → run.state.radius ≤ q.distanceSq)

/-- Sequential budgeted optimization preserves an incumbent and all bounds from exhausted children. -/
theorem children_partial_opt (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (z : Vector Int n) (cost : Rat) (k : Nat) (interval : Interval)
    (visit : Int → SearchState n m → Traversal n m) (P : Int → Point n m → Prop)
    (hv : ∀ a s, Incumbent b t mode s → PartialOpt b t mode s (visit a s) (P a))
    (fuel : Nat) (cursor : Coefficients) (s : SearchState n m) (trees : List (Int × Tree))
    (hs : Incumbent b t mode s) :
    PartialOpt b t mode s (traverseAux.children z cost false k interval visit fuel cursor s trees)
      (fun q => ∃ a ∈ Coefficients.toList.go fuel cursor, P a q) := by
  induction fuel generalizing cursor s trees with
  | zero => exact ⟨le_rfl, hs, by simp [Coefficients.toList.go]⟩
  | succ fuel ih =>
    cases he : cursor.next? with
    | none =>
      simp only [traverseAux.children, he]
      exact ⟨le_rfl, hs, by simp [Coefficients.toList.go, he]⟩
    | some step =>
      rcases step with ⟨a, cursor'⟩
      obtain ⟨hr, hinc, hb⟩ := hv a s hs
      by_cases hempty : (visit a s).pending = []
      · simp only [traverseAux.children, he, hempty, List.isEmpty_nil, ite_true, Bool.false_eq_true, ite_false]
        obtain ⟨hr', hinc', hb'⟩ := ih cursor' (visit a s).state trees hinc
        refine ⟨le_trans hr' hr, hinc', ?_⟩
        intro hdone q hq
        obtain ⟨c, hc, hp⟩ := hq
        simp only [Coefficients.toList.go, he, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact le_trans hr' (hb hempty q hp)
        · exact hb' hdone q ⟨c, hc, hp⟩
      · have hne : (visit a s).pending.isEmpty = false := by simp [hempty]
        simp only [traverseAux.children, he, hne, Bool.false_eq_true, ite_false]
        exact ⟨hr, hinc, fun hdone => False.elim (hempty (List.append_eq_nil_iff.mp hdone).1)⟩

/-- Budgeted branch-and-bound retains an attained incumbent and is globally exhaustive when it finishes. -/
theorem traverse_partial_opt (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (budget : Budget) (mode : SearchMode) (hmode : mode ≠ .ball) (k : Nat) (hk : k ≤ n) (z : Vector Int n)
    (s : SearchState n m) (hs : Incumbent b t mode s) :
    PartialOpt b t mode s
      (traverseAux b t p budget mode p.residual.normSq k hk z (suffix p.toData z k) s)
      (Possible b t mode k z) := by
  have hsave : (mode == .ball) = false := by simp [hmode]
  induction k generalizing z s with
  | zero =>
    rw [traverseAux]
    simp only [hsave, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false, Nat.add_zero]
    by_cases hstop : (!room budget.nodes s.counts.nodes) = true
    · simp only [ite_eq_left hstop]
      exact ⟨le_rfl, hs, by simp⟩
    simp only [ite_eq_right hstop]
    by_cases hdist : (point b t z).distanceSq > s.radius
    · simp only [ite_eq_left hdist]
      refine ⟨le_rfl, hs, ?_⟩
      intro _ q hq
      obtain ⟨rfl, _⟩ := (possible_zero b t mode z q).mp hq
      exact le_of_lt hdist
    · simp only [ite_eq_right hdist]
      by_cases hupdate : ((mode == .closest || (point b t z).ambient != 0) &&
          decide ((point b t z).distanceSq < s.radius)) = true
      · simp only [ite_eq_left hupdate]
        have hu : Eligible mode (point b t z) ∧ (point b t z).distanceSq < s.radius := by
          simpa [Eligible] using hupdate
        refine ⟨le_of_lt hu.2, ?_, ?_⟩
        · exact ⟨point b t z, rfl, rfl, rfl, hu.1⟩
        · intro _ q hq
          obtain ⟨rfl, _⟩ := (possible_zero b t mode z q).mp hq
          exact le_rfl
      · simp only [ite_eq_right hupdate]
        have hu : ¬(Eligible mode (point b t z) ∧ (point b t z).distanceSq < s.radius) := by
          simpa [Eligible] using hupdate
        refine ⟨le_rfl, hs, ?_⟩
        intro _ q hq
        obtain ⟨rfl, he⟩ := (possible_zero b t mode z q).mp hq
        exact le_of_not_gt (fun hlt => hu ⟨he, hlt⟩)
  | succ k ih =>
    rw [traverseAux]
    simp only [hsave, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false, Nat.add_zero]
    by_cases hstop : (!room budget.nodes s.counts.nodes) = true
    · simp only [ite_eq_left hstop]
      exact ⟨le_rfl, hs, by simp⟩
    simp only [ite_eq_right hstop]
    split_ifs with hempty
    · refine ⟨le_rfl, hs, ?_⟩
      intro _ q hq
      by_contra hnot
      have hr : q.distanceSq ≤ s.radius := le_of_lt (lt_of_not_ge hnot)
      obtain ⟨a, ha, _⟩ := possible_children b t p hp mode s.radius k (by omega) z q hq hr
      rw [mem_coefficients] at ha
      have he : (bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))).size = 0 := by
        simpa using hempty
      unfold Interval.size at he
      omega
    · let interval := bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))
      let visit := fun a (state : SearchState n m) =>
        traverseAux b t p budget mode p.residual.normSq k (by omega) (z.set k a (by omega))
          (suffix p.toData z (k + 1) + p.norms[k] *
            ((a : Rat) - p.centre z ⟨k, by omega⟩) * ((a : Rat) - p.centre z ⟨k, by omega⟩)) state
      let state : SearchState n m := { s with counts := { s.counts with nodes := s.counts.nodes + 1 } }
      have hchildren := children_partial_opt b t mode z (suffix p.toData z (k + 1)) k interval visit
        (fun a => Possible b t mode k (z.set k a (by omega)))
        (fun a state hs' => by
          have h := ih (by omega) (z.set k a (by omega)) state hs'
          rw [suffix_step p.toData z k (Nat.lt_of_succ_le hk) a] at h
          exact h)
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state [] hs
      change PartialOpt b t mode s
        (traverseAux.children z (suffix p.toData z (k + 1)) false k interval visit
          interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state []) _
      refine ⟨hchildren.1, hchildren.2.1, ?_⟩
      intro hdone q hq
      by_cases hr : q.distanceSq ≤ s.radius
      · exact hchildren.2.2 hdone q (possible_children b t p hp mode s.radius k (by omega) z q hq hr)
      · exact le_trans hchildren.1 (le_of_lt (lt_of_not_ge hr))

/-- Optimization children retain point storage unchanged during the incumbent-only pass. -/
theorem children_points (z : Vector Int n) (cost : Rat) (k : Nat) (interval : Interval)
    (visit : Int → SearchState n m → Traversal n m)
    (hv : ∀ a s, (visit a s).state.points = s.points) (fuel : Nat) (cursor : Coefficients)
    (s : SearchState n m) (trees : List (Int × Tree)) :
    (traverseAux.children z cost false k interval visit fuel cursor s trees).state.points = s.points := by
  induction fuel generalizing cursor s trees with
  | zero => rfl
  | succ fuel ih =>
    cases he : cursor.next? with
    | none => simp only [traverseAux.children, he]
    | some step =>
      rcases step with ⟨a, cursor'⟩
      simp only [traverseAux.children, he, Bool.false_eq_true, ite_false]
      by_cases hd : (visit a s).pending.isEmpty = true
      · simp only [ite_eq_left hd]
        exact (ih cursor' (visit a s).state trees).trans (hv a s)
      · simp only [ite_eq_right hd]
        exact hv a s

/-- The incumbent-only traversal does not allocate answer records. -/
theorem traverse_points (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (budget : Budget)
    (mode : SearchMode) (hmode : mode ≠ .ball) (residual : Rat) (k : Nat) (hk : k ≤ n)
    (z : Vector Int n) (cost : Rat) (s : SearchState n m) :
    (traverseAux b t p budget mode residual k hk z cost s).state.points = s.points := by
  have hsave : (mode == .ball) = false := by simp [hmode]
  induction k generalizing z cost s with
  | zero =>
    rw [traverseAux]
    simp only [hsave, Id.run, pure, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | succ k ih =>
    rw [traverseAux]
    simp only [hsave, Id.run, pure, Bool.false_and, Bool.or_false, Bool.false_eq_true, ite_false]
    split_ifs
    · rfl
    · rfl
    · apply children_points
      intro a state
      exact ih (by omega) _ _ state

/-- The two phases retain an eligible candidate and distinguish unfinished optimization from tie enumeration. -/
@[expose] def Progress (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (mode : SearchMode)
    (run : OptimumRun n m) : Prop :=
  run.incumbent = point b t run.incumbent.coefficients ∧ Eligible mode run.incumbent ∧
    (run.phase = .optimum → run.traversal.pending ≠ [] ∧ run.traversal.state.points = []) ∧
    (run.phase = .ties → Optimal b t mode run.incumbent ∧
      PartialBall { radius := run.incumbent.distanceSq } run.traversal
        (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ run.incumbent.distanceSq) ∧
      TreeResult run.incumbent.distanceSq
        (Exhaustive b.rows t p.toData run.incumbent.distanceSq n 0) run.traversal)

/-- Budgeted two-pass optimization has a checked incumbent in either phase and a complete tie ball only on exhaustion. -/
theorem optimize_progress (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (budget : Budget) (mode : SearchMode) (hmode : mode ≠ .ball) (seed : Point n m)
    (hseed : seed = point b t seed.coefficients) (he : Eligible mode seed) :
    Progress b t p mode (optimize budget b t p mode seed) := by
  let initial : SearchState n m := { radius := seed.distanceSq, incumbent := some seed }
  let first := traverse b t p budget mode n (Nat.le_refl n) 0 0 initial
  have hfirst := traverse_partial_opt b t p hp budget mode hmode n (Nat.le_refl n) 0 initial
    ⟨seed, rfl, hseed, rfl, he⟩
  rw [suffix_rank] at hfirst
  change PartialOpt b t mode initial first (Possible b t mode n 0) at hfirst
  obtain ⟨q, hq, hpq, hdq, heq⟩ := hfirst.2.1
  change Progress b t p mode (if !first.pending.isEmpty then
      ⟨first.state.incumbent.getD seed, first, .optimum⟩ else
      ⟨first.state.incumbent.getD seed,
        traverse b t p budget .ball n (Nat.le_refl n) 0 0
          { radius := (first.state.incumbent.getD seed).distanceSq,
            incumbent := some (first.state.incumbent.getD seed), counts := first.state.counts }, .ties⟩)
  rw [hq]
  simp only [Option.getD_some]
  by_cases hdone : first.pending = []
  · simp only [hdone, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
    refine ⟨hpq, heq, by simp, ?_⟩
    intro _
    have ho : Optimal b t mode q := by
      refine ⟨hpq, heq, ?_⟩
      intro v hv he
      rw [hdq]
      exact hfirst.2.2 hdone v ⟨hv, fun i hi => by omega, he⟩
    let start : SearchState n m := { radius := q.distanceSq, incumbent := some q, counts := first.state.counts }
    have hb := traverse_partial b t p hp budget n (Nat.le_refl n) 0 start
    have ht := traverse_exhaustive b t p budget n (Nat.le_refl n) 0 start
    rw [suffix_rank] at hb ht
    have hpred : Feasible b t q.distanceSq n 0 =
        (fun v => v = point b t v.coefficients ∧ v.distanceSq ≤ q.distanceSq) := by
      funext v
      apply propext
      simp [Feasible, Matches, not_le.mpr]
    change PartialBall start _ (Feasible b t q.distanceSq n 0) at hb
    rw [hpred] at hb
    exact ⟨ho, hb, ht⟩
  · have hne : first.pending.isEmpty = false := by simp [hdone]
    simp only [hne, Bool.not_false, ite_true]
    refine ⟨hpq, heq, ?_, by simp⟩
    intro _
    exact ⟨hdone, traverse_points b t p budget mode hmode p.residual.normSq n (Nat.le_refl n) 0 0 initial⟩

/-- The public all-minima contract, with common exact distance, global lower bound, and every tie. -/
@[expose] def MinimumSpec (b : Basis n m) (t : Vector Rat m) (mode : SearchMode) (answer : Minimum n m) : Prop :=
  (∃ q, q ∈ answer.points) ∧ answer.points.Nodup ∧
    answer.points.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) ∧
    (∀ q, q ∈ answer.points ↔ q = point b t q.coefficients ∧ Eligible mode q ∧ q.distanceSq = answer.distanceSq) ∧
    ∀ q, q = point b t q.coefficients → Eligible mode q → answer.distanceSq ≤ q.distanceSq

/-- Completed optimization proves all minima; incomplete progress has only checked points and pending work. -/
@[expose] def OptimizationSpec (b : Basis n m) (t : Vector Rat m) (mode : SearchMode) : Optimization n m → Prop
  | .complete answer _ _ => MinimumSpec b t mode answer
  | .incomplete incumbent points pending _ _ =>
    incumbent = point b t incumbent.coefficients ∧ Eligible mode incumbent ∧ pending ≠ [] ∧
      points.Nodup ∧ points.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) ∧
      ∀ q, q ∈ points → q = point b t q.coefficients ∧ Eligible mode q ∧ q.distanceSq ≤ incumbent.distanceSq

/-- The final eligibility filter implements precisely the nonzero restriction for shortest vectors. -/
theorem filter_eligible (mode : SearchMode) (hmode : mode ≠ .ball) (q : Point n m) :
    (mode != .shortest || q.ambient != 0) = true ↔ Eligible mode q := by
  cases mode with
  | ball => exact False.elim (hmode rfl)
  | closest => simp [Eligible]
  | shortest => simp [Eligible]

/-- Filtering eligible points and sorting preserves uniqueness. -/
theorem minimumPoints_nodup (mode : SearchMode) (ps : List (Point n m)) (h : ps.Nodup) :
    (minimumPoints mode ps).Nodup := by
  unfold minimumPoints sortPoints
  rw [Hex.List.sort_eq]
  exact (List.mergeSort_perm _ _).symm.nodup (h.filter _)

/-- Exhausting the tie pass reports exactly the eligible points on the attained minimum shell. -/
theorem tie_points (b : Basis n m) (t : Vector Rat m) (mode : SearchMode) (hmode : mode ≠ .ball)
    (run : OptimumRun n m) (ho : Optimal b t mode run.incumbent)
    (hb : PartialBall { radius := run.incumbent.distanceSq } run.traversal
      (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ run.incumbent.distanceSq))
    (hdone : run.traversal.pending = []) (q : Point n m) :
    q ∈ minimumPoints mode run.traversal.state.points ↔
      q = point b t q.coefficients ∧ Eligible mode q ∧ q.distanceSq = run.incumbent.distanceSq := by
  obtain ⟨fresh, hf, _, hm, hc⟩ := hb.2
  have hmem : q ∈ fresh ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ run.incumbent.distanceSq :=
    ⟨hm q, hc hdone q⟩
  simp only [minimumPoints, sortPoints, Hex.List.sort_eq, List.mem_mergeSort, List.mem_filter]
  rw [hf]
  simp only [List.append_nil, hmem, filter_eligible mode hmode]
  constructor
  · rintro ⟨⟨hq, hd⟩, he⟩
    exact ⟨hq, he, le_antisymm hd (ho.2.2 q hq he)⟩
  · rintro ⟨hq, he, hd⟩
    exact ⟨⟨hq, le_of_eq hd⟩, he⟩

/-- Classification of optimization progress preserves the complete/incomplete distinction. -/
theorem progress_result (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (mode : SearchMode)
    (hmode : mode ≠ .ball) (run : OptimumRun n m) (h : Progress b t p mode run) :
    OptimizationSpec b t mode (run.result mode) := by
  cases hphase : run.phase with
  | optimum =>
    obtain ⟨hpending, hpoints⟩ := h.2.2.1 hphase
    have he : minimumPoints mode run.traversal.state.points = [] := by
      simp [minimumPoints, hpoints, sortPoints, Hex.List.sort_eq]
    simp only [OptimumRun.result, hphase, he, OptimizationSpec]
    exact ⟨h.1, h.2.1, hpending, by simp, by simp, by simp⟩
  | ties =>
    obtain ⟨ho, hb, ht⟩ := h.2.2.2 hphase
    obtain ⟨fresh, hf, hn, hm, _⟩ := hb.2
    have hnodup : (minimumPoints mode run.traversal.state.points).Nodup := by
      apply minimumPoints_nodup
      rw [hf]
      simpa using hn
    cases he : run.traversal.tree with
    | none =>
      simp only [OptimumRun.result, hphase, he, OptimizationSpec]
      refine ⟨h.1, h.2.1, ?_, hnodup, sortPoints_sorted _, ?_⟩
      · intro hdone
        have hsome := ht.2.1.mp hdone
        rw [he] at hsome
        cases hsome
      · intro q hq
        simp only [minimumPoints, sortPoints, Hex.List.sort_eq, List.mem_mergeSort, List.mem_filter,
          filter_eligible mode hmode] at hq
        obtain ⟨hq, heligible⟩ := hq
        rw [hf] at hq
        have hq := hm q (by simpa using hq)
        exact ⟨hq.1, heligible, hq.2⟩
    | some tree =>
      have hdone := ht.2.1.mpr (by rw [he]; rfl)
      have hmem := tie_points b t mode hmode run ho hb hdone
      simp only [OptimumRun.result, hphase, he, OptimizationSpec, MinimumSpec]
      refine ⟨⟨run.incumbent, (hmem _).mpr ⟨h.1, h.2.1, rfl⟩⟩, hnodup, sortPoints_sorted _, hmem, ho.2.2⟩

/-- Every budgeted closest-vector result satisfies the full complete or checked-partial contract. -/
theorem closestWith_spec (b : Basis n m) (t : Vector Rat m) (budget : Budget) :
    OptimizationSpec b t .closest (closestWith budget b t) :=
  progress_result b t (prepare b t) .closest (by decide) _
    (optimize_progress b t (prepare b t) (prepare_valid b t) budget .closest (by decide)
      (babai b t) rfl (Or.inl rfl))

/-- Budgeting cannot change the rank-zero condition for shortest-vector queries. -/
theorem shortestWith_none (b : Basis n m) (budget : Budget) : shortestWith budget b = none ↔ n = 0 := by
  simp only [shortestWith, Option.map_eq_none_iff, shortestSeed_none]

/-- Budgeted shortest-vector calls preserve the rank-zero and complete/partial contracts. -/
theorem shortestWith_spec (b : Basis n m) (budget : Budget) :
    match shortestWith budget b with
    | none => n = 0
    | some result => OptimizationSpec b 0 .shortest result := by
  cases hs : shortestSeed b with
  | none =>
    simp only [shortestWith, hs, Option.map_none]
    exact (shortestSeed_none b).mp hs
  | some seed =>
    obtain ⟨hp, he, _⟩ := shortestSeed_spec b seed hs
    simp only [shortestWith, hs, Option.map_some]
    exact progress_result b 0 (prepare b 0) .shortest (by decide) _
      (optimize_progress b 0 (prepare b 0) (prepare_valid b 0) budget .shortest (by decide)
        seed hp (Or.inr he))

end HexLatticeEnumMathlib
