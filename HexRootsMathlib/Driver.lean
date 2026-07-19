/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.IsolateAll
public import HexRootsMathlib.Certificate

public section

/-!
# Soundness of the general isolation driver

This module instantiates the parametric loop kernel for every atom strategy.
It retains the full atom-or-cluster certificate type and packages coverage,
certificate counts, target precision, and output disjointness.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

namespace Certified

/-- A certificate's selected region lies in its stored square's closed
circumscribed disc. -/
theorem region_subset_closedDisc {p : Hex.ZPoly} (r : Hex.Certified p) :
    region r ⊆ DyadicSquare.closedDisc r.square := by
  cases r with
  | atom iso =>
      simp only [region, DyadicRootIsolation.region, Hex.Certified.square]
      split
      · exact DyadicSquare.closedSquare_subset_closedDisc iso.square
      -- The Pellet-selected region is definitionally the stored disc.
      · intro z hz
        exact hz
  -- A cluster's stored square is definitionally its enclosing disc's square.
  | cluster cl =>
      intro z hz
      exact hz

end Certified

/-- `isolateAll?` is the shared loop at its executable fuel value. -/
theorem isolateAll_loop {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work strategy = some rs) :
    ∃ fuel, Hex.isolateLoop p target strategy fuel work = some rs := by
  refine ⟨Hex.fuelFor p target
    (work.foldl (fun m c => min m c.prec)
      ((work[0]?.map (·.prec)).getD 0)), ?_⟩
  simpa [Hex.isolateAll?] using hrun

/-- Successful general isolation preserves every polynomial root covered by
its starting worklist. -/
theorem isolateAll_covers {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work strategy = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  obtain ⟨fuel, hloop⟩ := isolateAll_loop hrun
  exact isolateLoop_covers (certifier_preserves p strategy) hloop hzroot hz

/-- Every emitted result meets the target, carries its full semantic count,
and distinct indices have disjoint closed circumscribed discs. -/
theorem isolateAll_sound {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target work strategy = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec ∧ Certified.Sound r) ∧
      ∀ {i j : Nat}, (hi : i < rs.size) → (hj : j < rs.size) → i ≠ j →
        Disjoint (DyadicSquare.closedDisc rs[i].square)
          (DyadicSquare.closedDisc rs[j].square) := by
  obtain ⟨fuel, hloop⟩ := isolateAll_loop hrun
  have hready := (isolateLoop_ready_disjoint hloop).1
  refine ⟨fun r hr => ⟨hready r hr, Certified.sound r⟩, ?_⟩
  exact fun hi hj hij => isolateLoop_disjoint_of_ne hloop hi hj hij

/-- Starting from the Cauchy component, successful isolation with any
strategy covers every complex root. -/
theorem isolateAll_cauchy_covers (p : Hex.ZPoly)
    (hdegree : 0 < p.degree?.getD 0) {target : Int}
    {strategy : Hex.AtomStrategy} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target #[Hex.Component.cauchy p hdegree]
      strategy = some rs) {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) :
    z ∈ Results.region rs := by
  apply isolateAll_covers hrun hzroot
  exact ⟨Hex.Component.cauchy p hdegree, by simp,
    Component.isRoot_mem_cauchy p hdegree hzroot⟩

/-- Every complex root belongs to exactly one selected result region in a
successful Cauchy-started run. This remains valid when results include
Pellet clusters: uniqueness is between certificates, not between roots
inside one cluster. -/
theorem isolateAll_covers_once (p : Hex.ZPoly)
    (hdegree : 0 < p.degree?.getD 0) {target : Int}
    {strategy : Hex.AtomStrategy} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target #[Hex.Component.cauchy p hdegree]
      strategy = some rs) {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z) :
    ∃! i : Fin rs.size, z ∈ Certified.region rs[i] := by
  obtain ⟨r, hr, hzr⟩ := isolateAll_cauchy_covers p hdegree hrun hzroot
  obtain ⟨i, hiList, hir⟩ := List.getElem_of_mem hr
  have hi : i < rs.size := by simpa using hiList
  have hir' : rs[i] = r := by
    rw [← hir]
    exact (Array.getElem_toList hi).symm
  let fi : Fin rs.size := ⟨i, hi⟩
  have hzfi : z ∈ Certified.region rs[fi] := by
    change z ∈ Certified.region rs[i]
    rw [hir']
    exact hzr
  refine ⟨fi, hzfi, ?_⟩
  intro j hzj
  apply Fin.ext
  by_contra hij
  have hdisj := (isolateAll_sound hrun).2 fi.isLt j.isLt (Ne.symm hij)
  exact (Set.disjoint_left.mp hdisj)
    (Certified.region_subset_closedDisc rs[fi] hzfi)
    (Certified.region_subset_closedDisc rs[j] hzj)

/-- In a successful Cauchy-started run, the sum of the emitted certificate
counts is exactly the polynomial degree. Counts are with multiplicity, so a
Pellet cluster contributes its stored `k`, while an atom contributes one. -/
theorem isolateAll_count (p : Hex.ZPoly)
    (hdegree : 0 < p.degree?.getD 0) {target : Int}
    {strategy : Hex.AtomStrategy} {rs : Array (Hex.Certified p)}
    (hrun : Hex.isolateAll? p target #[Hex.Component.cauchy p hdegree]
      strategy = some rs) :
    ∑ i : Fin rs.size, Certified.count rs[i] = (toPolyℂ p).natDegree := by
  classical
  let q := toPolyℂ p
  have hparts :
      (∑ i : Fin rs.size,
        q.roots.filter fun z => z ∈ Certified.region rs[i]) = q.roots := by
    apply Multiset.ext.mpr
    intro z
    rw [Multiset.count_sum']
    by_cases hzroots : z ∈ q.roots
    · have hzroot : q.IsRoot z := by
        have hq : q ≠ 0 := by
          intro hzero
          have hnat : q.natDegree = 0 := by rw [hzero]; simp
          have hcast : q.natDegree = p.degree?.getD 0 := by
            simp only [q, natDegree_toPolyℂ]
          omega
        exact (mem_roots hq).mp hzroots
      obtain ⟨i, hi, hunique⟩ := isolateAll_covers_once p hdegree hrun hzroot
      rw [Finset.sum_eq_single i]
      · exact Multiset.count_filter_of_pos hi
      · intro j _ hji
        rw [Multiset.count_filter_of_neg]
        exact fun hj => hji (hunique j hj)
      · simp
    · rw [Multiset.count_eq_zero.mpr hzroots]
      apply Finset.sum_eq_zero
      intro i _
      apply Multiset.count_eq_zero.mpr
      intro hzfilter
      exact hzroots (Multiset.mem_filter.mp hzfilter).1
  have hcard := congrArg Multiset.card hparts
  rw [Multiset.card_sum] at hcard
  calc
    ∑ i : Fin rs.size, Certified.count rs[i] =
        ∑ i : Fin rs.size, Certified.rootCount rs[i] := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Certified.sound rs[i]).1.symm
    _ = ∑ i : Fin rs.size,
        (q.roots.filter fun z => z ∈ Certified.region rs[i]).card := by
      rfl
    _ = q.roots.card := hcard
    _ = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm

end

end HexRootsMathlib
