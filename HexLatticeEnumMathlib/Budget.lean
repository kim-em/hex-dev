/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Native
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- Budgeted ball traversal reports sound, unique leaves and is complete exactly when exhausted. -/
@[expose] def PartialBall (before : SearchState n m) (run : Traversal n m) (P : Point n m → Prop) : Prop :=
  run.state.radius = before.radius ∧ ∃ fresh, run.state.points = fresh ++ before.points ∧
    fresh.Nodup ∧ (∀ q, q ∈ fresh → P q) ∧ (run.pending = [] → ∀ q, P q → q ∈ fresh)

/-- The child loop preserves sound partial output, and covers every child if it finishes. -/
theorem children_partial (z : Vector Int n) (cost : Rat) (k : Nat) (interval : Interval)
    (visit : Int → SearchState n m → Traversal n m) (P : Int → Point n m → Prop)
    (r : Rat) (hv : ∀ a s, s.radius = r → PartialBall s (visit a s) (P a))
    (hd : ∀ a b q, P a q → P b q → a = b)
    (fuel : Nat) (cursor : Coefficients) (s : SearchState n m) (trees : List (Int × Tree))
    (hn : (Coefficients.toList.go fuel cursor).Nodup) (hs : s.radius = r) :
    PartialBall s (traverseAux.children z cost true k interval visit fuel cursor s trees)
      (fun q => ∃ a ∈ Coefficients.toList.go fuel cursor, P a q) := by
  induction fuel generalizing cursor s trees with
  | zero =>
    refine ⟨rfl, [], by simp [traverseAux.children], by simp, by simp, ?_⟩
    simp [Coefficients.toList.go]
  | succ fuel ih =>
    cases he : cursor.next? with
    | none =>
      refine ⟨by simp [traverseAux.children, he], [], by simp [traverseAux.children, he], by simp, by simp, ?_⟩
      simp [Coefficients.toList.go, he]
    | some step =>
      rcases step with ⟨a, cursor'⟩
      obtain ⟨hr, fresh, hf, hfn, hfm, hfc⟩ := hv a s hs
      have hn' : a ∉ Coefficients.toList.go fuel cursor' ∧ (Coefficients.toList.go fuel cursor').Nodup := by
        simpa [Coefficients.toList.go, he] using hn
      by_cases hempty : (visit a s).pending = []
      · simp only [traverseAux.children, he, hempty, List.isEmpty_nil, ite_true]
        obtain ⟨hrr, rest, hrest, hrestn, hrestm, hrestc⟩ :=
          ih cursor' (visit a s).state ((a, (visit a s).tree.getD .empty) :: trees) hn'.2 (hr.trans hs)
        refine ⟨hrr.trans hr, rest ++ fresh, ?_, ?_, ?_, ?_⟩
        · rw [hrest, hf, List.append_assoc]
        · apply List.nodup_append.mpr
          refine ⟨hrestn, hfn, ?_⟩
          intro q hq q' hq' heq
          subst q'
          obtain ⟨b, hb, hbp⟩ := hrestm q hq
          exact hn'.1 ((hd a b q (hfm q hq') hbp) ▸ hb)
        · intro q hq
          simp only [Coefficients.toList.go, he, List.mem_cons]
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨b, hb, hp⟩ := hrestm q hq
            exact ⟨b, Or.inr hb, hp⟩
          · exact ⟨a, Or.inl rfl, hfm q hq⟩
        · intro hdone q hq
          simp only [Coefficients.toList.go, he, List.mem_cons] at hq
          obtain ⟨b, hb, hp⟩ := hq
          rcases hb with rfl | hb
          · exact List.mem_append.mpr (Or.inr (hfc hempty q hp))
          · exact List.mem_append.mpr (Or.inl (hrestc hdone q ⟨b, hb, hp⟩))
      · have hne : (visit a s).pending.isEmpty = false := by simp [hempty]
        simp only [traverseAux.children, he, hne, Bool.false_eq_true, ite_false]
        refine ⟨hr, fresh, hf, hfn, ?_, ?_⟩
        · intro q hq
          exact ⟨a, by simp [Coefficients.toList.go, he], hfm q hq⟩
        · intro hdone
          exact False.elim (hempty (List.append_eq_nil_iff.mp hdone).1)

/-- A budgeted fixed-radius traversal preserves the exact suffix invariant and all completed coverage. -/
theorem traverse_partial (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (hp : p.Valid)
    (budget : Budget) (k : Nat) (hk : k ≤ n) (z : Vector Int n) (s : SearchState n m) :
    PartialBall s (traverseAux b t p budget .ball p.residual.normSq k hk z (suffix p.toData z k) s)
      (Feasible b t s.radius k z) := by
  induction k generalizing z s with
  | zero =>
    rw [traverseAux]
    simp only [beq_self_eq_true, Bool.true_and, ite_true]
    split_ifs with hbudget hdist hanswers
    · refine ⟨rfl, [], by simp, by simp, by simp, ?_⟩
      simp
    · refine ⟨rfl, [], by simp, by simp, by simp, ?_⟩
      intro _ q hq
      have h := (feasible_zero b t s.radius z q).mp hq
      exact False.elim (not_le.mpr hdist h.2)
    · refine ⟨rfl, [], by simp, by simp, by simp, ?_⟩
      simp
    · refine ⟨rfl, [point b t z], rfl, by simp, ?_, ?_⟩
      · intro q hq
        have he : q = point b t z := List.mem_singleton.mp hq
        exact (feasible_zero b t s.radius z q).mpr ⟨he, le_of_not_gt hdist⟩
      · intro _ q hq
        exact List.mem_singleton.mpr ((feasible_zero b t s.radius z q).mp hq).1
  | succ k ih =>
    rw [traverseAux]
    simp only [beq_self_eq_true, Bool.true_and, ite_true]
    split_ifs with hbudget hempty
    · refine ⟨rfl, [], by simp, by simp, by simp, ?_⟩
      simp
    · refine ⟨rfl, [], by simp, by simp, by simp, ?_⟩
      intro _ q hq
      obtain ⟨a, ha, _⟩ := (feasible_children b t p hp s.radius k (by omega) z q).mpr hq
      rw [mem_coefficients] at ha
      have he : (bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))).size = 0 := by
        simpa only [beq_iff_eq, Fin.getElem_fin] using hempty
      unfold Interval.size at he
      omega
    · let interval := bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
          (s.radius - p.residual.normSq - suffix p.toData z (k + 1))
      let visit := fun a (state : SearchState n m) =>
        traverseAux b t p budget .ball p.residual.normSq k (by omega) (z.set k a (by omega))
          (suffix p.toData z (k + 1) + p.norms[k] *
            ((a : Rat) - p.centre z ⟨k, by omega⟩) * ((a : Rat) - p.centre z ⟨k, by omega⟩)) state
      let state : SearchState n m := { s with counts :=
        { s.counts with nodes := s.counts.nodes + 1, certificateNodes := s.counts.certificateNodes + 1 } }
      have hchildren := children_partial z (suffix p.toData z (k + 1)) k interval visit
        (fun a => Feasible b t s.radius k (z.set k a (by omega))) s.radius
        (fun a state hs => by
          dsimp only [visit]
          have h := ih (by omega) (z.set k a (by omega)) state
          rw [suffix_step] at h
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
      change PartialBall s (traverseAux.children z (suffix p.toData z (k + 1)) true k interval visit
        interval.size (coefficients interval (p.centre z ⟨k, by omega⟩)) state []) _
      rw [← hpred]
      exact hchildren

/-- At the root, a budgeted ball run reports only reconstructed points within the query radius. -/
theorem budget_ball (b : Basis n m) (t : Vector Rat m) (r : Rat) (budget : Budget) :
    PartialBall { radius := r }
      (traverse b t (prepare b t) budget .ball n (Nat.le_refl n) 0 0 { radius := r })
      (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ r) := by
  have h := traverse_partial b t (prepare b t) (prepare_valid b t) budget n (Nat.le_refl n) 0 { radius := r }
  rw [suffix_rank] at h
  have hp : Feasible b t r n 0 = (fun q => q = point b t q.coefficients ∧ q.distanceSq ≤ r) := by
    funext q
    apply propext
    simp [Feasible, Matches, not_le.mpr]
  rw [hp] at h
  exact h

/-- `enumerateWith` distinguishes the complete accepted ball from sound partial progress with pending work. -/
theorem enumerateWith_spec (b : Basis n m) (t : Vector Rat m) (r : Rat) (budget : Budget) :
    match enumerateWith budget b t r with
    | .complete points tree _ => points = enumerate b t r ∧
        checkEnumeration b.rows t r
          ⟨b.rows, Hex.Matrix.identity n, Hex.Matrix.identity n, (prepare b t).toData, tree, points⟩ = true
    | .incomplete points pending _ => points.Nodup ∧ pending ≠ [] ∧
        ∀ q, q ∈ points → q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
  let p := prepare b t
  let run := traverse b t p budget .ball n (Nat.le_refl n) 0 0 { radius := r }
  have ht := traverse_exhaustive b t p budget n (Nat.le_refl n) 0 { radius := r }
  rw [suffix_rank] at ht
  change TreeResult r (Exhaustive b.rows t p.toData r n 0) run at ht
  have hb := budget_ball b t r budget
  obtain ⟨fresh, hf, hn, hm, hc⟩ := hb.2
  have hnodup : (sortPoints run.state.points).Nodup := by
    unfold sortPoints
    rw [Hex.List.sort_eq]
    apply (List.mergeSort_perm _ _).symm.nodup
    rw [hf]
    simpa using hn
  have hsound : ∀ q, q ∈ sortPoints run.state.points → q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
    intro q hq
    simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort] at hq
    rw [hf] at hq
    exact hm q (by simpa using hq)
  cases he : run.tree with
  | none =>
    have he' := he
    dsimp only [run, p] at he'
    simp only [enumerateWith, he']
    refine ⟨hnodup, ?_, hsound⟩
    intro hdone
    have hsome := ht.2.1.mp hdone
    rw [he] at hsome
    cases hsome
  | some tree =>
    have he' := he
    dsimp only [run, p] at he'
    simp only [enumerateWith, he']
    have hdone : run.pending = [] := ht.2.1.mpr (by rw [he]; rfl)
    have hmem : ∀ q, q ∈ sortPoints run.state.points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
      intro q
      refine ⟨hsound q, ?_⟩
      intro hq
      simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort]
      rw [hf]
      exact List.mem_append.mpr (Or.inl (hc hdone q hq))
    refine ⟨?_, ?_⟩
    · exact sorted_points_eq b t _ _ hnodup (enumerate_nodup b t r)
        (fun q => (hmem q).trans (enumerate_point_spec b t r q).symm)
        (fun q hq => (hsound q hq).1) (sortPoints_sorted _) (enumerate_sorted b t r)
    · have hvalid := ht.2.2 tree he
      have hz : (Vector.replicate n (0 : Int)) = 0 := by ext i hi; simp
      rw [← hz] at hvalid
      exact certificate_accepts b t p (prepare_valid b t) r tree hvalid _ hnodup hmem (sortPoints_sorted _)

/-- Every resource count is bounded by its independently selected limit. -/
@[expose] def Within (budget : Budget) (counts : Counts) : Prop :=
  (∀ cap, budget.nodes = some cap → counts.nodes ≤ cap) ∧
  (∀ cap, budget.answers = some cap → counts.answers ≤ cap) ∧
  (∀ cap, budget.certificateNodes = some cap → counts.certificateNodes ≤ cap)

/-- Initially no query has consumed any resources. -/
theorem within_zero (budget : Budget) : Within budget {} := by
  exact ⟨fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _⟩

/-- The room check permits at most one additional resource unit. -/
theorem room_bound (limit : Option Nat) (used : Nat) (h : room limit used = true)
    (cap : Nat) (hc : limit = some cap) : used + 1 ≤ cap := by
  subst limit
  simp only [room, decide_eq_true_eq] at h
  omega

/-- Entering a node consumes the node allowance and, only in ball mode, a certificate allowance. -/
theorem within_node (budget : Budget) (counts : Counts) (save : Bool) (h : Within budget counts)
    (hg : ¬(!room budget.nodes counts.nodes || (save && !room budget.certificateNodes counts.certificateNodes)) = true) :
    Within budget { counts with
      nodes := counts.nodes + 1
      certificateNodes := counts.certificateNodes + (if save then 1 else 0) } := by
  have hn : room budget.nodes counts.nodes = true := by
    cases he : room budget.nodes counts.nodes <;> simp_all
  have ht : save = true → room budget.certificateNodes counts.certificateNodes = true := by
    intro hs
    cases he : room budget.certificateNodes counts.certificateNodes <;> simp_all
  refine ⟨fun cap hc => room_bound _ _ hn cap hc, h.2.1, ?_⟩
  intro cap hc
  cases hs : save with
  | false => simpa only [hs, Bool.false_eq_true, ite_false, Nat.add_zero] using h.2.2 cap hc
  | true => exact room_bound _ _ (ht hs) cap hc

/-- Storing a leaf consumes exactly one answer allowance. -/
theorem within_answer (budget : Budget) (counts : Counts) (h : Within budget counts)
    (ha : room budget.answers counts.answers = true) :
    Within budget { counts with answers := counts.answers + 1 } :=
  ⟨h.1, fun cap hc => room_bound _ _ ha cap hc, h.2.2⟩

/-- Siblings share the same resource counts; the child loop never resets an allowance. -/
theorem children_within (budget : Budget) (z : Vector Int n) (cost : Rat) (save : Bool)
    (k : Nat) (interval : Interval) (visit : Int → SearchState n m → Traversal n m)
    (hv : ∀ a s, Within budget s.counts → Within budget (visit a s).state.counts)
    (fuel : Nat) (cursor : Coefficients) (s : SearchState n m) (trees : List (Int × Tree))
    (hs : Within budget s.counts) :
    Within budget (traverseAux.children z cost save k interval visit fuel cursor s trees).state.counts := by
  induction fuel generalizing cursor s trees with
  | zero => exact hs
  | succ fuel ih =>
    cases he : cursor.next? with
    | none => simpa only [traverseAux.children, he] using hs
    | some step =>
      rcases step with ⟨a, cursor'⟩
      have hchild := hv a s hs
      simp only [traverseAux.children, he]
      by_cases hd : (visit a s).pending.isEmpty = true
      · simp only [ite_eq_left hd]
        exact ih cursor' (visit a s).state _ hchild
      · simp only [ite_eq_right hd]
        exact hchild

/-- Every traversal respects all three limits, including interrupted runs and optimization modes. -/
theorem traverse_within (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (budget : Budget)
    (mode : SearchMode) (residual : Rat) (k : Nat) (hk : k ≤ n) (z : Vector Int n)
    (cost : Rat) (s : SearchState n m) (hs : Within budget s.counts) :
    Within budget (traverseAux b t p budget mode residual k hk z cost s).state.counts := by
  induction k generalizing z cost s with
  | zero =>
    rw [traverseAux]
    simp only [Id.run, pure]
    split
    · exact hs
    · rename_i hg
      have hn := within_node budget s.counts (mode == .ball) hs hg
      split
      · exact hn
      · split
        · rename_i hsave
          simp only [ite_eq_left hsave] at hn
          split
          · exact hn
          · rename_i ha
            have hr : room budget.answers s.counts.answers = true := by
              cases he : room budget.answers s.counts.answers <;> simp_all
            exact within_answer budget _ hn hr
        · rename_i hsave
          simp only [ite_eq_right hsave] at hn
          split <;> exact hn
  | succ k ih =>
    rw [traverseAux]
    simp only [Id.run, pure]
    split
    · exact hs
    · rename_i hg
      have hn := within_node budget s.counts (mode == .ball) hs hg
      split
      · exact hn
      · apply children_within budget
        · intro a state hstate
          exact ih (by omega) _ _ state hstate
        · exact hn

/-- The resource counts exposed by every ball result stay within the requested limits. -/
theorem enumerateWith_within (b : Basis n m) (t : Vector Rat m) (r : Rat) (budget : Budget) :
    match enumerateWith budget b t r with
    | .complete _ _ counts | .incomplete _ _ counts => Within budget counts := by
  have h := traverse_within b t (prepare b t) budget .ball (prepare b t).residual.normSq n
    (Nat.le_refl n) 0 0 { radius := r } (within_zero budget)
  cases he : (traverse b t (prepare b t) budget .ball n (Nat.le_refl n) 0 0 { radius := r }).tree <;>
    simp only [enumerateWith, he] <;> exact h

/-- Optimization shares the first pass's resource consumption with the all-ties pass. -/
theorem optimize_within (b : Basis n m) (t : Vector Rat m) (p : Prepared b t) (budget : Budget)
    (mode : SearchMode) (seed : Point n m) :
    Within budget (optimize budget b t p mode seed).traversal.state.counts := by
  have h := traverse_within b t p budget mode p.residual.normSq n (Nat.le_refl n) 0 0
    { radius := seed.distanceSq, incumbent := some seed } (within_zero budget)
  dsimp only [optimize]
  split_ifs
  · exact h
  · exact traverse_within b t p budget .ball p.residual.normSq n (Nat.le_refl n) 0 0 _ h

/-- Both completed and interrupted optimization results retain the bounded traversal counts. -/
theorem result_within (budget : Budget) (run : OptimumRun n m) (mode : SearchMode)
    (h : Within budget run.traversal.state.counts) :
    match run.result mode with
    | .complete _ _ counts | .incomplete _ _ _ _ counts => Within budget counts := by
  cases hp : run.phase <;> cases ht : run.traversal.tree <;>
    simp only [OptimumRun.result, hp, ht] <;> exact h

/-- Closest-vector calls respect the separate node, answer and certificate limits. -/
theorem closestWith_within (b : Basis n m) (t : Vector Rat m) (budget : Budget) :
    match closestWith budget b t with
    | .complete _ _ counts | .incomplete _ _ _ _ counts => Within budget counts :=
  result_within budget _ .closest (optimize_within b t (prepare b t) budget .closest _)

/-- Shortest-vector calls respect every limit whenever their rank admits a nonzero candidate. -/
theorem shortestWith_within (b : Basis n m) (budget : Budget) :
    match shortestWith budget b with
    | none => True
    | some (.complete _ _ counts) | some (.incomplete _ _ _ _ counts) => Within budget counts := by
  unfold shortestWith
  cases hs : shortestSeed b with
  | none => trivial
  | some seed =>
    simp only [Option.map_some]
    have h := result_within budget _ .shortest (optimize_within b 0 (prepare b 0) budget .shortest seed)
    cases he : (optimize budget b 0 (prepare b 0) .shortest seed).result .shortest <;>
      simp only [he] at h ⊢ <;> exact h

end HexLatticeEnumMathlib
