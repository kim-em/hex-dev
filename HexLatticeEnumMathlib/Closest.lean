/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Closest
public import HexLatticeEnumMathlib.Traversal
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat}

/-- An eligible optimization candidate; shortest-vector searches exclude zero. -/
@[expose] def Eligible (mode : SearchMode) (q : Point n m) : Prop := mode = .closest ∨ q.ambient ≠ 0

/-- The incumbent is an attained, eligible point at the current search radius. -/
@[expose] def Incumbent (b : Basis n m) (t : Vector Rat m) (mode : SearchMode) (s : SearchState n m) : Prop :=
  ∃ q, s.incumbent = some q ∧ q = point b t q.coefficients ∧
    q.distanceSq = s.radius ∧ Eligible mode q

/-- An optimization pass preserves attainment and bounds every eligible suffix completion. -/
@[expose] def OptResult (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (before : SearchState n m) (run : Traversal n m) (P : Point n m → Prop) : Prop :=
  run.pending = [] ∧ run.state.radius ≤ before.radius ∧ Incumbent b t mode run.state ∧
    ∀ q, P q → run.state.radius ≤ q.distanceSq

/-- Sequential child optimization retains all earlier lower bounds as the radius shrinks. -/
theorem children_optimum (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (z : Vector Int n) (cost : Rat) (k : Nat) (interval : Interval)
    (visit : Int → SearchState n m → Traversal n m) (P : Int → Point n m → Prop)
    (hvisit : ∀ a s, Incumbent b t mode s → OptResult b t mode s (visit a s) (P a))
    (fuel : Nat) (cursor : Coefficients) (s : SearchState n m) (trees : List (Int × Tree))
    (hs : Incumbent b t mode s) :
    OptResult b t mode s (traverseAux.children z cost false k interval visit fuel cursor s trees)
      (fun q => ∃ a ∈ Coefficients.toList.go fuel cursor, P a q) := by
  induction fuel generalizing cursor s trees with
  | zero =>
    refine ⟨rfl, le_rfl, hs, ?_⟩
    simp [Coefficients.toList.go]
  | succ fuel ih =>
    cases he : cursor.next? with
    | none =>
      simp only [traverseAux.children, he]
      refine ⟨rfl, le_rfl, hs, ?_⟩
      simp [Coefficients.toList.go, he]
    | some step =>
      rcases step with ⟨a, cursor'⟩
      obtain ⟨hempty, hr, hinc, hbound⟩ := hvisit a s hs
      simp only [traverseAux.children, he, hempty, List.isEmpty_nil, ite_true, Bool.false_eq_true,
        ite_false]
      obtain ⟨htail, hr', hinc', hbound'⟩ := ih cursor' (visit a s).state trees hinc
      refine ⟨htail, le_trans hr' hr, hinc', ?_⟩
      intro q hq
      obtain ⟨c, hc, hp⟩ := hq
      simp only [Coefficients.toList.go, he, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact le_trans hr' (hbound q hp)
      · exact hbound' q ⟨c, hc, hp⟩

/-- Eligible reconstructed points matching the current suffix. -/
@[expose] def Possible (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (k : Nat) (z : Vector Int n) (q : Point n m) : Prop :=
  q = point b t q.coefficients ∧ Matches k z q.coefficients ∧ Eligible mode q

/-- Fixing the next coordinate reduces eligible answers to the extended suffix. -/
theorem possible_set (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (k : Nat) (hk : k < n) (z : Vector Int n) (a : Int) (q : Point n m) :
    Possible b t mode k (z.set k a hk) q ↔
      Possible b t mode (k + 1) z q ∧ q.coefficients[k] = a := by
  simp only [Possible, matches_set]
  tauto

/-- A fully fixed suffix admits only its reconstructed eligible point. -/
theorem possible_zero (b : Basis n m) (t : Vector Rat m) (mode : SearchMode)
    (z : Vector Int n) (q : Point n m) :
    Possible b t mode 0 z q ↔ q = point b t z ∧ Eligible mode q := by
  constructor
  · rintro ⟨hq, hm, he⟩
    have hz : q.coefficients = z := by
      apply Vector.ext
      intro i hi
      exact hm ⟨i, hi⟩ (Nat.zero_le i)
    rw [hz] at hq
    exact ⟨hq, he⟩
  · rintro ⟨rfl, he⟩
    exact ⟨rfl, fun _ _ => rfl, he⟩

/-- The exact child intervals cover every eligible completion within the current bound. -/
theorem possible_children (b : Basis n m) (t : Vector Rat m) (p : Prepared b t)
    (hp : p.Valid) (mode : SearchMode) (r : Rat) (k : Nat) (hk : k < n)
    (z : Vector Int n) (q : Point n m) (hq : Possible b t mode (k + 1) z q)
    (hr : q.distanceSq ≤ r) :
    let interval := bounds (p.centre z ⟨k, hk⟩) p.norms[k]
      (r - p.residual.normSq - suffix p.toData z (k + 1))
    ∃ a ∈ (coefficients interval (p.centre z ⟨k, hk⟩)).toList,
      Possible b t mode k (z.set k a hk) q := by
  obtain ⟨a, ha, hf⟩ := (feasible_children b t p hp r k hk z q).mpr ⟨hq.1, hq.2.1, hr⟩
  exact ⟨a, ha, hf.1, hf.2.1, hq.2.2⟩

/-- Exact branch-and-bound attains a radius no larger than any eligible suffix completion. -/
theorem traverse_optimum (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (mode : SearchMode) (hmode : mode ≠ .ball) (k : Nat) (hk : k ≤ n) (z : Vector Int n)
    (s : SearchState n m) (hs : Incumbent b t mode s) :
    OptResult b t mode s
      (traverseAux b t p {} mode p.residual.normSq k hk z (suffix p.toData z k) s)
      (Possible b t mode k z) := by
  have hsave : (mode == .ball) = false := by simp [hmode]
  induction k generalizing z s with
  | zero =>
    rw [traverseAux]
    simp only [room, hsave, Bool.not_true, Bool.and_false, Bool.false_or, Bool.false_eq_true,
      ite_false, Nat.add_zero]
    by_cases hdist : (point b t z).distanceSq > s.radius
    · simp only [ite_eq_left hdist]
      refine ⟨rfl, le_rfl, hs, ?_⟩
      intro q hq
      obtain ⟨rfl, _⟩ := (possible_zero b t mode z q).mp hq
      exact le_of_lt hdist
    · simp only [ite_eq_right hdist]
      by_cases hupdate : ((mode == .closest || (point b t z).ambient != 0) &&
          decide ((point b t z).distanceSq < s.radius)) = true
      · simp only [ite_eq_left hupdate]
        have hu : Eligible mode (point b t z) ∧ (point b t z).distanceSq < s.radius := by
          simpa [Eligible] using hupdate
        refine ⟨rfl, le_of_lt hu.2, ?_, ?_⟩
        · exact ⟨point b t z, rfl, rfl, rfl, hu.1⟩
        · intro q hq
          obtain ⟨rfl, _⟩ := (possible_zero b t mode z q).mp hq
          exact le_rfl
      · simp only [ite_eq_right hupdate]
        have hu : ¬(Eligible mode (point b t z) ∧ (point b t z).distanceSq < s.radius) := by
          simpa [Eligible] using hupdate
        refine ⟨rfl, le_rfl, hs, ?_⟩
        intro q hq
        obtain ⟨rfl, he⟩ := (possible_zero b t mode z q).mp hq
        exact le_of_not_gt (fun hlt => hu ⟨he, hlt⟩)
  | succ k ih =>
    rw [traverseAux]
    simp only [room, hsave, Bool.not_true, Bool.and_false, Bool.false_or, Bool.false_eq_true,
      ite_false, Nat.add_zero]
    split_ifs with hempty
    · refine ⟨rfl, le_rfl, hs, ?_⟩
      intro q hq
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
        traverseAux b t p {} mode p.residual.normSq k (by omega) (z.set k a (by omega))
          (suffix p.toData z (k + 1) + p.norms[k] *
            ((a : Rat) - p.centre z ⟨k, by omega⟩) * ((a : Rat) - p.centre z ⟨k, by omega⟩)) state
      let state : SearchState n m := { s with counts := { s.counts with nodes := s.counts.nodes + 1 } }
      have hchildren := children_optimum b t mode z (suffix p.toData z (k + 1)) k interval visit
        (fun a => Possible b t mode k (z.set k a (by omega)))
        (fun a state hs' => by
          have h := ih (by omega) (z.set k a (by omega)) state hs'
          rw [suffix_step p.toData z k (Nat.lt_of_succ_le hk) a] at h
          exact h)
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state [] hs
      change OptResult b t mode s
        (traverseAux.children z (suffix p.toData z (k + 1)) false k interval visit
          interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state []) _
      refine ⟨hchildren.1, hchildren.2.1, hchildren.2.2.1, ?_⟩
      intro q hq
      by_cases hr : q.distanceSq ≤ s.radius
      · exact hchildren.2.2.2 q (possible_children b t p hp mode s.radius k (by omega) z q hq hr)
      · exact le_trans hchildren.2.1 (le_of_lt (lt_of_not_ge hr))

/-- An attained global optimum among eligible lattice points. -/
@[expose] def Optimal (b : Basis n m) (t : Vector Rat m) (mode : SearchMode) (q : Point n m) : Prop :=
  q = point b t q.coefficients ∧ Eligible mode q ∧
    ∀ v : Point n m, v = point b t v.coefficients → Eligible mode v → q.distanceSq ≤ v.distanceSq

/-- The two-pass optimizer attains a global optimum and exhausts its complete tie ball. -/
theorem optimize_spec (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (mode : SearchMode) (hmode : mode ≠ .ball) (seed : Point n m)
    (hseed : seed = point b t seed.coefficients) (heligible : Eligible mode seed) :
    let run := optimize {} b t p mode seed
    Optimal b t mode run.incumbent ∧ run.phase = .ties ∧
      BallResult { radius := run.incumbent.distanceSq } run.traversal
        (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ run.incumbent.distanceSq) := by
  let initial : SearchState n m := { radius := seed.distanceSq, incumbent := some seed }
  let first := traverse b t p {} mode n (Nat.le_refl n) 0 0 initial
  have hinc : Incumbent b t mode initial := ⟨seed, rfl, hseed, rfl, heligible⟩
  have hfirst := traverse_optimum b t p hp mode hmode n (Nat.le_refl n) 0 initial hinc
  rw [suffix_rank] at hfirst
  change OptResult b t mode initial first (Possible b t mode n 0) at hfirst
  obtain ⟨q, hq, hpoint, hdist, he⟩ := hfirst.2.2.1
  have hoptimal : Optimal b t mode q := by
    refine ⟨hpoint, he, ?_⟩
    intro v hv he
    rw [hdist]
    exact hfirst.2.2.2 v ⟨hv, fun i hi => by omega, he⟩
  have hball := traverse_ball b t p hp n (Nat.le_refl n) 0
    { radius := q.distanceSq, incumbent := some q, counts := first.state.counts }
  rw [suffix_rank] at hball
  have hpred : Feasible b t q.distanceSq n 0 =
      (fun v => v = point b t v.coefficients ∧ v.distanceSq ≤ q.distanceSq) := by
    funext v
    apply propext
    simp [Feasible, Matches, not_le.mpr]
  rw [hpred] at hball
  have hdone := hfirst.1
  dsimp only [first, initial] at hdone hq
  simp only [optimize, hdone, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false,
    hq, Option.getD_some]
  exact ⟨hoptimal, trivial, hball⟩

/-- The all-ties output consists exactly of eligible reconstructed points at the attained minimum. -/
theorem minimum_points (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (mode : SearchMode) (hmode : mode ≠ .ball) (seed : Point n m)
    (hseed : seed = point b t seed.coefficients) (heligible : Eligible mode seed) (q : Point n m) :
    let run := optimize {} b t p mode seed
    q ∈ minimumPoints mode run.traversal.state.points ↔
      q = point b t q.coefficients ∧ Eligible mode q ∧ q.distanceSq = run.incumbent.distanceSq := by
  obtain ⟨hoptimal, _, _, _, _, fresh, hfresh, _, hmem⟩ :=
    optimize_spec b t p hp mode hmode seed hseed heligible
  simp only [minimumPoints, sortPoints, Hex.List.sort_eq, List.mem_mergeSort, List.mem_filter]
  rw [hfresh]
  simp only [List.append_nil, hmem]
  have he : (mode != .shortest || q.ambient != 0) = true ↔ Eligible mode q := by
    cases mode with
    | ball => exact False.elim (hmode rfl)
    | closest => simp [Eligible]
    | shortest => simp [Eligible]
  rw [he]
  constructor
  · rintro ⟨⟨hq, hr⟩, he⟩
    exact ⟨hq, he, le_antisymm hr (hoptimal.2.2 q hq he)⟩
  · rintro ⟨hq, he, hd⟩
    exact ⟨⟨hq, le_of_eq hd⟩, he⟩

/-- The global optimum itself occurs in the all-ties output. -/
theorem minimum_nonempty (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (mode : SearchMode) (hmode : mode ≠ .ball) (seed : Point n m)
    (hseed : seed = point b t seed.coefficients) (heligible : Eligible mode seed) :
    ∃ q, q ∈ minimumPoints mode (optimize {} b t p mode seed).traversal.state.points := by
  have h := (optimize_spec b t p hp mode hmode seed hseed heligible).1
  exact ⟨_, (minimum_points b t p hp mode hmode seed hseed heligible _).mpr ⟨h.1, h.2.1, rfl⟩⟩

/-- Filtering and sorting the complete tie ball preserves uniqueness. -/
theorem minimum_nodup (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (mode : SearchMode) (hmode : mode ≠ .ball) (seed : Point n m)
    (hseed : seed = point b t seed.coefficients) (heligible : Eligible mode seed) :
    (minimumPoints mode (optimize {} b t p mode seed).traversal.state.points).Nodup := by
  obtain ⟨_, _, _, _, _, fresh, hfresh, hn, _⟩ :=
    optimize_spec b t p hp mode hmode seed hseed heligible
  unfold minimumPoints sortPoints
  rw [Hex.List.sort_eq]
  apply (List.mergeSort_perm _ _).symm.nodup
  rw [hfresh]
  simpa using hn.filter _

/-- Babai's coefficients always reconstruct its reported candidate and distance. -/
theorem babai_reconstruct (b : Basis n m) (t : Vector Rat m) :
    babai b t = point b t (babai b t).coefficients := rfl

/-- Every closest point is reconstructed and lies at the reported minimum radius. -/
theorem closest_point_spec (b : Basis n m) (t : Vector Rat m) (q : Point n m) :
    q ∈ (closest b t).points ↔
      q = point b t q.coefficients ∧ q.distanceSq = (closest b t).distanceSq := by
  have h := minimum_points b t (prepare b t) (prepare_valid b t) .closest (by decide)
    (babai b t) rfl (Or.inl rfl) q
  simpa only [closest, babai, Eligible, true_or, true_and] using h

/-- The reported closest distance bounds every lattice point, without a target restriction. -/
theorem closest_le (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) :
    (closest b t).distanceSq ≤ distanceSq b t z := by
  have h := (optimize_spec b t (prepare b t) (prepare_valid b t) .closest (by decide)
    (babai b t) rfl (Or.inl rfl)).1
  exact h.2.2 (point b t z) rfl (Or.inl rfl)

/-- Closest-vector search always attains its minimum, including rank zero. -/
theorem closest_nonempty (b : Basis n m) (t : Vector Rat m) :
    ∃ q, q ∈ (closest b t).points :=
  minimum_nonempty b t (prepare b t) (prepare_valid b t) .closest (by decide)
    (babai b t) rfl (Or.inl rfl)

/-- All closest vectors occur exactly once as point records. -/
theorem closest_nodup (b : Basis n m) (t : Vector Rat m) : (closest b t).points.Nodup :=
  minimum_nodup b t (prepare b t) (prepare_valid b t) .closest (by decide)
    (babai b t) rfl (Or.inl rfl)

/-- The closest-vector list contains the entire lattice shell at its attained radius. -/
theorem closest_radius_spec (b : Basis n m) (t : Vector Rat m) (v : Vector Int m) :
    v ∈ (closest b t).points.map Point.ambient ↔
      b.rows.memLattice v ∧ distance v t = (closest b t).distanceSq := by
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    obtain ⟨he, hd⟩ := (closest_point_spec b t q).mp hq
    have ha : q.ambient = vector b q.coefficients := congrArg Point.ambient he
    refine ⟨⟨q.coefficients, ha.symm⟩, ?_⟩
    have hr : q.distanceSq = distance q.ambient t := by
      conv_lhs => rw [he]
      change distance (vector b q.coefficients) t = _
      rw [ha]
    exact hr.symm.trans hd
  · rintro ⟨⟨z, rfl⟩, hd⟩
    exact List.mem_map.mpr ⟨point b t z, (closest_point_spec b t _).mpr ⟨rfl, hd⟩, rfl⟩

/-- Unconditional global closest-vector correctness, including every minimizer. -/
theorem closest_spec (b : Basis n m) (t : Vector Rat m) (v : Vector Int m) :
    v ∈ (closest b t).points.map Point.ambient ↔
      b.rows.memLattice v ∧ ∀ w, b.rows.memLattice w → distance v t ≤ distance w t := by
  rw [closest_radius_spec]
  constructor
  · rintro ⟨hv, hd⟩
    refine ⟨hv, ?_⟩
    rintro w ⟨z, rfl⟩
    rw [hd]
    exact closest_le b t z
  · rintro ⟨hv, hmin⟩
    refine ⟨hv, le_antisymm ?_ ?_⟩
    · obtain ⟨q, hq⟩ := closest_nonempty b t
      have h := (closest_radius_spec b t q.ambient).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
      rw [← h.2]
      exact hmin _ h.1
    · obtain ⟨z, rfl⟩ := hv
      exact closest_le b t z

/-- Distinct returned closest points also have distinct ambient vectors. -/
theorem closest_ambient_nodup (b : Basis n m) (t : Vector Rat m) :
    ((closest b t).points.map Point.ambient).Nodup := by
  apply List.Nodup.map_on ?_ (closest_nodup b t)
  intro q hq q' hq' he
  have hr := ((closest_point_spec b t q).mp hq).1
  have hr' := ((closest_point_spec b t q').mp hq').1
  have ha := congrArg Point.ambient hr
  have ha' := congrArg Point.ambient hr'
  have hz : q.coefficients = q'.coefficients := vector_injective b (ha.symm.trans (he.trans ha'))
  rw [hr, hr', hz]

/-- Closest-vector ties are returned in ambient lexicographic order. -/
theorem closest_sorted (b : Basis n m) (t : Vector Rat m) :
    (closest b t).points.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) :=
  sortPoints_sorted _

end HexLatticeEnumMathlib
