/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Glue
public import HexRootsMathlib.Component

public section

/-!
# Structural soundness of the isolation loop

The results in this module are parametric in the semantic meaning of a
successful certificate. They prove the coverage and output-geometry facts
that follow solely from the executable worklist transitions.
-/

namespace HexRootsMathlib

noncomputable section

/-- Every input square occurs in one of the guarded connected components. -/
theorem mem_glueCovered {sqs : Array Hex.DyadicSquare} {s : Hex.DyadicSquare}
    (hs : s ∈ sqs.toList) :
    ∃ c ∈ (Hex.glueCovered sqs).toList, s ∈ c.toList := by
  rw [Hex.glueCovered]
  split
  · rename_i h
    exact h s hs
  · exact ⟨#[s], by simpa using hs, by simp⟩

/-- One guarded subdivision round preserves every polynomial root covered by
the input component. -/
theorem isRoot_mem_refine1 {p : Hex.ZPoly} {c : Hex.Component} {z : ℂ}
    (hzroot : (toPolyℂ p).IsRoot z) (hz : z ∈ Component.region c) :
    ∃ d ∈ (c.refine1 p).toList, z ∈ Component.region d := by
  obtain ⟨s, hs, hzs⟩ := hz
  let survivors := (c.squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  obtain ⟨t, ht, hzt⟩ := isRoot_mem_survivors hzroot hs hzs
  change t ∈ survivors.toList at ht
  obtain ⟨ss, hss, htss⟩ := mem_glueCovered ht
  let d : Hex.Component := { squares := ss, candidateK := c.candidateK }
  refine ⟨d, ?_, ⟨t, htss, hzt⟩⟩
  rw [Hex.Component.refine1]
  change d ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := c.candidateK }).toList
  simp only [Array.toList_map, List.mem_map]
  exact ⟨ss, hss, rfl⟩

namespace Worklist

/-- Union of the closed-square regions retained by a worklist. -/
@[expose] def region (work : Array Hex.Component) : Set ℂ :=
  {z | ∃ c ∈ work.toList, z ∈ Component.region c}

end Worklist

namespace Results

/-- Union of the semantic regions of an array of certificates. -/
@[expose] def region {p : Hex.ZPoly} (rs : Array (Hex.Certified p)) : Set ℂ :=
  {z | ∃ r ∈ rs.toList, z ∈ Certified.region r}

end Results

namespace Certifier

/-- Semantic hypothesis consumed by the structural loop proof: every
successful certificate covers every polynomial root covered by its input
component. The `.nk` and general certificate developments instantiate this
separately. In particular, speculative recentring must use the executable
containment and same-count guards; it does not follow from geometric
containment of the input component in the returned region. -/
@[expose] def Preserves (p : Hex.ZPoly) (strategy : Hex.AtomStrategy) : Prop :=
  ∀ c r, Hex.Component.certify? p strategy c = some r →
    ∀ z, (toPolyℂ p).IsRoot z → z ∈ Component.region c →
      z ∈ Certified.region r

end Certifier

/-- The non-emitting transition preserves every covered polynomial root. -/
theorem isRoot_mem_next {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {work : Array Hex.Component} {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) :
    z ∈ Worklist.region (Hex.IsolationLoop.next p target
      (Hex.IsolationLoop.attempts p strategy work)) := by
  obtain ⟨c, hc, hzc⟩ := hz
  let tried := Hex.IsolationLoop.attempts p strategy work
  have ht : (c, Hex.Component.certify? p strategy c) ∈ tried := by
    apply Array.mem_map_of_mem
    exact Array.mem_toList_iff.mp hc
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem ht
  have hiRange : i ∈ Array.range tried.size := by simp [hi]
  rw [Worklist.region]
  change ∃ d ∈ (Hex.IsolationLoop.next p target tried).toList,
    z ∈ Component.region d
  rw [Hex.IsolationLoop.next]
  let step := Hex.IsolationLoop.step p target tried
  change ∃ d ∈ ((Array.range tried.size).flatMap step).toList,
    z ∈ Component.region d
  have hgetD : tried.getD i (⟨#[], 0⟩, none) =
      (c, Hex.Component.certify? p strategy c) := by
    calc
      _ = tried[i] :=
        (Array.getElem_eq_getD (⟨#[], 0⟩, none)).symm
      _ = _ := hget
  have hlocal : ∃ d, d ∈ step i ∧ z ∈ Component.region d := by
    dsimp only [step]
    rw [Hex.IsolationLoop.step, hgetD]
    cases htry : Hex.Component.certify? p strategy c with
    | none =>
        obtain ⟨d, hd, hzd⟩ := isRoot_mem_refine1 hzroot hzc
        exact ⟨d, Array.mem_toList_iff.mp hd, hzd⟩
    | some res =>
        dsimp only
        split
        · exact ⟨c, by simp, hzc⟩
        · split
          · have hzres := hcert c res htry z hzroot hzc
            exact ⟨res.toComponent, by simp,
              Certified.region_subset_toComponent res hzres⟩
          · obtain ⟨d, hd, hzd⟩ := isRoot_mem_refine1 hzroot hzc
            exact ⟨d, Array.mem_toList_iff.mp hd, hzd⟩
  obtain ⟨d, hd, hzd⟩ := hlocal
  exact ⟨d, Array.mem_toList_iff.mpr
    (Array.mem_flatMap_of_mem hiRange hd), hzd⟩

/-- A target-ready successful attempt whose disc meets no other successful
attempt holds its original component in the next worklist. -/
theorem mem_next_of_hold {p : Hex.ZPoly} {target : Int}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    {i : Nat} (hi : i < tried.size) {c : Hex.Component} {r : Hex.Certified p}
    (hget : tried[i] = (c, some r))
    (hready : target ≤ r.square.prec)
    (hdisjoint : Hex.IsolationLoop.overlaps tried i r = false) :
    c ∈ Hex.IsolationLoop.next p target tried := by
  rw [Hex.IsolationLoop.next]
  apply Array.mem_flatMap_of_mem (by simp [hi] : i ∈ Array.range tried.size)
  rw [Hex.IsolationLoop.step]
  have hgetD : tried.getD i (⟨#[], 0⟩, none) = (c, some r) := by
    calc
      _ = tried[i] := (Array.getElem_eq_getD (⟨#[], 0⟩, none)).symm
      _ = _ := hget
  rw [hgetD]
  simp [hready, hdisjoint]

/-- A non-held successful attempt whose doubled result is strictly finer
re-enters the next worklist as that doubled covering component. -/
theorem mem_next_of_adopt {p : Hex.ZPoly} {target : Int}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    {i : Nat} (hi : i < tried.size) {c : Hex.Component} {r : Hex.Certified p}
    (hget : tried[i] = (c, some r))
    (hcontinue : (decide (target ≤ r.square.prec) &&
      !Hex.IsolationLoop.overlaps tried i r) = false)
    (hfiner : c.prec < r.toComponent.prec) :
    r.toComponent ∈ Hex.IsolationLoop.next p target tried := by
  rw [Hex.IsolationLoop.next]
  apply Array.mem_flatMap_of_mem (by simp [hi] : i ∈ Array.range tried.size)
  rw [Hex.IsolationLoop.step]
  have hgetD : tried.getD i (⟨#[], 0⟩, none) = (c, some r) := by
    calc
      _ = tried[i] := (Array.getElem_eq_getD (⟨#[], 0⟩, none)).symm
      _ = _ := hget
  rw [hgetD]
  rw [Certified.toComponent_prec] at hfiner
  simp [hcontinue, hfiner]

/-- `allReady` means every emitted certificate meets the target precision. -/
theorem outputs_ready {p : Hex.ZPoly} {target : Int}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    (hready : Hex.IsolationLoop.allReady target tried) :
    ∀ r ∈ (Hex.IsolationLoop.outputs tried).toList,
      target ≤ r.square.prec := by
  intro r hr
  have hr' := Array.mem_toList_iff.mp hr
  obtain ⟨t, ht, htr⟩ := Array.mem_filterMap.mp hr'
  have htready := (Array.all_eq_true_iff_forall_mem.mp hready) t ht
  rw [Hex.IsolationLoop.outputs] at hr'
  cases t with
  | mk c o =>
      cases o with
      | none => simp at htr
      | some r' =>
          simp only at htr
          cases htr
          simpa using htready

/-- When every attempt succeeds, the emitted certificate regions cover every
polynomial root covered by the attempted worklist. -/
theorem isRoot_mem_outputs {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {work : Array Hex.Component} {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work)
    (hready : Hex.IsolationLoop.allReady target
      (Hex.IsolationLoop.attempts p strategy work)) :
    z ∈ Results.region (Hex.IsolationLoop.outputs
      (Hex.IsolationLoop.attempts p strategy work)) := by
  obtain ⟨c, hc, hzc⟩ := hz
  let tried := Hex.IsolationLoop.attempts p strategy work
  have ht : (c, Hex.Component.certify? p strategy c) ∈ tried := by
    apply Array.mem_map_of_mem
    exact Array.mem_toList_iff.mp hc
  have htready := (Array.all_eq_true_iff_forall_mem.mp hready) _ ht
  cases htry : Hex.Component.certify? p strategy c with
  | none => simp [htry] at htready
  | some r =>
      refine ⟨r, ?_, hcert c r htry z hzroot hzc⟩
      apply Array.mem_toList_iff.mpr
      rw [Hex.IsolationLoop.outputs, Array.mem_filterMap]
      exact ⟨(c, some r), by simpa [htry] using ht, rfl⟩

/-- Parametric coverage theorem for the fuel-based isolation loop. No
certificate analysis enters: the proof consumes only `Certifier.Preserves`
and follows the executable emitting and non-emitting branches. -/
theorem isolateLoop_covers {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {fuel : Nat} {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hloop : Hex.isolateLoop p target strategy fuel work = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.isolateLoop] at hloop
  | succ fuel ih =>
      rw [Hex.isolateLoop] at hloop
      split at hloop
      · rename_i hempty
        have hwork : work = #[] := Array.eq_empty_of_size_eq_zero
          (Array.isEmpty_iff_size_eq_zero.mp hempty)
        subst work
        simp [Worklist.region] at hz
      · rename_i hnonempty
        let tried := Hex.IsolationLoop.attempts p strategy work
        change (if Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried then
          some (Hex.IsolationLoop.outputs tried)
        else Hex.isolateLoop p target strategy fuel
          (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        split at hloop
        · rename_i hemit
          have hrs : rs = Hex.IsolationLoop.outputs tried := by
            exact Option.some.inj hloop.symm
          subst rs
          have hready : Hex.IsolationLoop.allReady target tried := by
            simp only [Bool.and_eq_true] at hemit
            exact hemit.1
          exact isRoot_mem_outputs hcert hzroot hz hready
        · exact ih hloop (isRoot_mem_next hcert hzroot hz)

/-- Every successful loop result meets the requested precision and passes the
executable pairwise-disjoint-disc test. -/
theorem isolateLoop_ready_disjoint {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {fuel : Nat} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hloop : Hex.isolateLoop p target strategy fuel work = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec) ∧
      Hex.pairwiseDisjoint (rs.map (·.square)) = true := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.isolateLoop] at hloop
  | succ fuel ih =>
      rw [Hex.isolateLoop] at hloop
      split at hloop
      · have hrs : rs = #[] := Option.some.inj hloop.symm
        subst rs
        simp [Hex.pairwiseDisjoint]
      · let tried := Hex.IsolationLoop.attempts p strategy work
        change (if Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried then
          some (Hex.IsolationLoop.outputs tried)
        else Hex.isolateLoop p target strategy fuel
          (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        split at hloop
        · rename_i hemit
          simp only [Bool.and_eq_true] at hemit
          have hrs : rs = Hex.IsolationLoop.outputs tried :=
            Option.some.inj hloop.symm
          subst rs
          exact ⟨outputs_ready hemit.1, by
            simpa [Hex.IsolationLoop.disjoint] using hemit.2⟩
        · exact ih hloop

/-- Distinct loop outputs have disjoint closed circumscribed discs. -/
theorem isolateLoop_disjoint {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {fuel : Nat} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hloop : Hex.isolateLoop p target strategy fuel work = some rs)
    {i j : Nat} (hi : i < rs.size) (hj : j < rs.size) (hij : i < j) :
    Disjoint (DyadicSquare.closedDisc rs[i].square)
      (DyadicSquare.closedDisc rs[j].square) := by
  have hpair := (isolateLoop_ready_disjoint hloop).2
  have hi' : i < (rs.map (·.square)).size := by simpa using hi
  have hj' : j < (rs.map (·.square)).size := by simpa using hj
  have hsem := DyadicSquare.closedDisc_disjoint_of_pairwiseDisjoint
    hpair hi' hj' hij
  simpa using hsem

/-- Any two differently indexed loop outputs have disjoint closed
circumscribed discs. -/
theorem isolateLoop_disjoint_of_ne {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {fuel : Nat} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hloop : Hex.isolateLoop p target strategy fuel work = some rs)
    {i j : Nat} (hi : i < rs.size) (hj : j < rs.size) (hij : i ≠ j) :
    Disjoint (DyadicSquare.closedDisc rs[i].square)
      (DyadicSquare.closedDisc rs[j].square) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact isolateLoop_disjoint hloop hi hj hij
  · exact (isolateLoop_disjoint hloop hj hi hji).symm

end

end HexRootsMathlib
