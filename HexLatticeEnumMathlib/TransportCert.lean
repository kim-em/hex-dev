/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnumMathlib.Preprocess
import Mathlib.Tactic

public section
namespace HexLatticeEnumMathlib
open Hex.LatticeEnum
variable {n m : Nat} {b : Basis n m}

/-- Exhaustive working-basis trees accept their complete original-coordinate point lists. -/
theorem change_accepts (change : BasisChange b) (t : Vector Rat m) (r : Rat)
    (p : Prepared change.working t) (hp : p.Valid) (tree : Tree)
    (ht : Exhaustive change.working.rows t p.toData r n (Vector.replicate n 0) tree)
    (ps : List (Point n m)) (hps : ps = enumerate change.working t r) :
    checkEnumeration b.rows t r
      ⟨change.working.rows, change.forward, change.reverse, p.toData, tree, change.points t ps⟩ = true := by
  obtain ⟨result, hr, _⟩ := replay_accepts b.rows change.working.rows change.forward
    (change_identities change).1 p.toData t r n (Nat.le_refl n) (Vector.replicate n 0)
    tree ht tree.nodes (Nat.le_refl _)
  rw [suffix_rank] at hr
  have hspec := replay_spec b.rows change.working.rows change.forward p.toData t hp
    (change_identities change).1 r n (Nat.le_refl n) (Vector.replicate n 0) tree tree.nodes result
  rw [suffix_rank] at hspec
  obtain ⟨hn, hm⟩ := hspec hr
  have hmem : ∀ q, q ∈ sortPoints result.points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
    intro q
    simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort, hm]
    exact replay_root b change.working.rows change.forward change.reverse
      (change_identities change).1 (change_identities change).2 t r _ q
  have heq : sortPoints result.points = enumerate b t r := by
    apply sorted_points_eq b t _ _ ?_ (enumerate_nodup b t r)
      (fun q => (hmem q).trans (enumerate_point_spec b t r q).symm)
      (fun q hq => ((hmem q).mp hq).1) (sortPoints_sorted _) (enumerate_sorted b t r)
    unfold sortPoints
    rw [Hex.List.sort_eq]
    exact (List.mergeSort_perm _ _).symm.nodup hn
  have hd := (Data.check_iff p.toData change.working.rows t).mpr hp
  have he : change.points t ps = enumerate b t r := by
    rw [hps]
    exact change_enumerate change t r
  simp only [checkEnumeration, checkEnumerationWith, change.checked, hd, Bool.true_and, replay, hr, heq, he]
  rfl

/-- Native optimum tie certificates remain accepted after coordinate transport. -/
theorem change_optimum_check (change : BasisChange b) (t : Vector Rat m)
    (p : Prepared change.working t) (hp : p.Valid) (mode : SearchMode) (hmode : mode ≠ .ball)
    (seed : Point n m) (hseed : seed = point change.working t seed.coefficients)
    (heligible : Eligible mode seed) :
    let run := optimize {} change.working t p mode seed
    checkEnumeration b.rows t run.incumbent.distanceSq
      (change.optimumCertificate t (optimumCertificate change.working p run)).enumeration = true := by
  let run := optimize {} change.working t p mode seed
  obtain ⟨_, hphase, hball⟩ := optimize_spec change.working t p hp mode hmode seed hseed heligible
  obtain ⟨tree, ht⟩ := Option.isSome_iff_exists.mp hball.2.1
  have htree := optimize_tree change.working t p {} mode seed hphase tree ht
  have hz : (Vector.replicate n (0 : Int)) = 0 := by ext i hi; simp
  rw [← hz] at htree
  have hc := optimumCertificate_check change.working t p hp mode hmode seed hseed heligible
  let c := (optimumCertificate change.working p run).enumeration
  have hs := checkEnumerationWith_spec change.working t run.incumbent.distanceSq c c.tree.nodes hc
  have he : c.points = enumerate change.working t run.incumbent.distanceSq := by
    apply sorted_points_eq change.working t _ _ hs.1 (enumerate_nodup _ _ _)
      (fun q => (hs.2.1 q).trans (enumerate_point_spec _ _ _ q).symm)
      (fun q hq => ((hs.2.1 q).mp hq).1) hs.2.2 (enumerate_sorted _ _ _)
  have hcheck := change_accepts change t run.incumbent.distanceSq p hp tree htree c.points he
  simpa only [c, run, BasisChange.optimumCertificate, optimumCertificate, ht, Option.getD_some] using hcheck

/-- Coordinate transport preserves acceptance of a closest certificate when its ball passes replay. -/
theorem change_closest_accepts (change : BasisChange b) (t : Vector Rat m) (c : OptimumCertificate n m)
    (hc : checkClosest change.working.rows t c = true)
    (hb : checkEnumeration b.rows t c.candidate.distanceSq
      (change.optimumCertificate t c).enumeration = true) :
    checkClosest b.rows t (change.optimumCertificate t c) = true := by
  simp only [checkClosest, checkClosestWith, Bool.and_eq_true] at hc ⊢
  have hq : c.candidate = point change.working t c.candidate.coefficients := by
    exact decide_eq_true_eq.mp hc.1.1
  have hd := (change_point change t c.candidate hq).2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact decide_eq_true_eq.mpr rfl
  · simpa only [BasisChange.optimumCertificate, checkEnumeration, hd] using hb
  · simp only [BasisChange.optimumCertificate, BasisChange.points, sortPoints,
      Hex.List.sort_eq, List.all_eq_true, List.mem_mergeSort, List.mem_map, beq_iff_eq] at hc ⊢
    rintro _ ⟨q, hmem, rfl⟩
    have hr := (checkEnumeration_point_spec change.working t c.candidate.distanceSq c.enumeration hc.1.2 q).mp hmem
    rw [(change_point change t q hr.1).2, hd]
    exact hc.2 q hmem

/-- Every native closest certificate produced after checked preprocessing passes replay. -/
theorem change_closestCertificate_check (change : BasisChange b) (t : Vector Rat m) :
    checkClosest b.rows t (change.closestCertificate t) = true := by
  apply change_closest_accepts change t (closestCertificate change.working t)
    (closestCertificate_check change.working t)
  exact change_optimum_check change t (prepare change.working t) (prepare_valid _ _)
    .closest (by decide) (babai change.working t) rfl (Or.inl rfl)

/-- Coordinate transport preserves acceptance of a shortest certificate when its ball passes replay. -/
theorem change_shortest_accepts (change : BasisChange b) (c : OptimumCertificate n m)
    (hc : checkShortest change.working.rows c = true)
    (hb : checkEnumeration b.rows 0 c.candidate.distanceSq
      (change.optimumCertificate 0 c).enumeration = true) :
    checkShortest b.rows (change.optimumCertificate 0 c) = true := by
  have hz : (Vector.replicate m (0 : Int)) = 0 := by ext i hi; simp
  have ht : (Vector.replicate m (0 : Rat)) = 0 := by ext i hi; simp
  simp only [checkShortest, checkShortestWith, hz, ht, Bool.and_eq_true] at hc ⊢
  have hq : c.candidate = point change.working 0 c.candidate.coefficients :=
    decide_eq_true_eq.mp hc.1.1.2
  have hpoint := change_point change 0 c.candidate hq
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa only [BasisChange.optimumCertificate, hpoint.1] using hc.1.1.1
  · exact decide_eq_true_eq.mpr rfl
  · simpa only [BasisChange.optimumCertificate, checkEnumeration, hpoint.2] using hb
  · simp only [BasisChange.optimumCertificate, BasisChange.points, sortPoints,
      Hex.List.sort_eq, List.all_eq_true, List.mem_mergeSort, List.mem_map,
      Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc ⊢
    rintro _ ⟨q, hmem, rfl⟩
    have hr := (checkEnumeration_point_spec change.working 0 c.candidate.distanceSq c.enumeration hc.1.2 q).mp hmem
    have hp := change_point change 0 q hr.1
    rw [hp.1, hp.2, hpoint.2]
    exact hc.2 q hmem

/-- Every native shortest certificate produced after checked preprocessing passes replay. -/
theorem change_shortestCertificate_check (change : BasisChange b) (c : OptimumCertificate n m)
    (h : change.shortestCertificate = some c) : checkShortest b.rows c = true := by
  obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp h
  apply change_shortest_accepts change original (shortestCertificate_check change.working original ho)
  obtain ⟨seed, hs, rfl⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨hseed, heligible, _⟩ := shortestSeed_spec change.working seed hs
  exact change_optimum_check change 0 (prepare change.working 0) (prepare_valid _ _)
    .shortest (by decide) seed hseed (Or.inr heligible)

end HexLatticeEnumMathlib
