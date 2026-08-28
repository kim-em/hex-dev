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

/-- A globally normalized subdivision round preserves every polynomial root
covered by its input worklist. -/
theorem isRoot_mem_refineAll {p : Hex.ZPoly} {work : Array Hex.Component}
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) :
    z ∈ Worklist.region (Hex.Component.refineAll p work) := by
  obtain ⟨c, hc, s, hs, hzs⟩ := hz
  let squares := work.flatMap (·.squares)
  have hsquares : s ∈ squares.toList := by
    simp only [squares, Array.toList_flatMap, List.mem_flatMap]
    exact ⟨c, hc, hs⟩
  obtain ⟨t, ht, hzt⟩ := isRoot_mem_survivors hzroot hsquares hzs
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  change t ∈ survivors.toList at ht
  obtain ⟨ss, hss, htss⟩ := mem_glueCovered ht
  let d : Hex.Component := { squares := ss, candidateK := 1 }
  refine ⟨d, ?_, ⟨t, htss, hzt⟩⟩
  rw [Hex.Component.refineAll]
  change d ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList
  simp only [Array.toList_map, List.mem_map]
  exact ⟨ss, hss, rfl⟩

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
  split
  · let step := Hex.IsolationLoop.step p target tried
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
  · apply isRoot_mem_refineAll hzroot
    exact ⟨c, by
      apply Array.mem_toList_iff.mpr
      exact Array.mem_map_of_mem ht, hzc⟩

/-- The lineage-local transition used by single-atom refinement preserves
every covered polynomial root. -/
theorem isRoot_mem_nextLocal {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {work : Array Hex.Component} {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) :
    z ∈ Worklist.region (Hex.IsolationLoop.nextLocal p target
      (Hex.IsolationLoop.attempts p strategy work)) := by
  obtain ⟨c, hc, hzc⟩ := hz
  let tried := Hex.IsolationLoop.attempts p strategy work
  have ht : (c, Hex.Component.certify? p strategy c) ∈ tried := by
    apply Array.mem_map_of_mem
    exact Array.mem_toList_iff.mp hc
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem ht
  have hiRange : i ∈ Array.range tried.size := by simp [hi]
  rw [Worklist.region]
  change ∃ d ∈ (Hex.IsolationLoop.nextLocal p target tried).toList,
    z ∈ Component.region d
  rw [Hex.IsolationLoop.nextLocal]
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
    (hdepth : Hex.IsolationLoop.normalized p target tried = true)
    (hready : target ≤ r.square.prec)
    (hdisjoint : Hex.IsolationLoop.overlaps tried i r = false) :
    c ∈ Hex.IsolationLoop.next p target tried := by
  rw [Hex.IsolationLoop.next]
  simp only [hdepth, if_true]
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
    (hdepth : Hex.IsolationLoop.normalized p target tried = true)
    (hcontinue : (decide (target ≤ r.square.prec) &&
      !Hex.IsolationLoop.overlaps tried i r) = false)
    (hfiner : c.prec < r.toComponent.prec) :
    r.toComponent ∈ Hex.IsolationLoop.next p target tried := by
  rw [Hex.IsolationLoop.next]
  simp only [hdepth, if_true]
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

/-- Parametric coverage theorem for the single-atom refinement loop. -/
theorem refineLoop_covers {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {fuel : Nat} {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hloop : Hex.refineLoop p target strategy fuel work = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.refineLoop] at hloop
  | succ fuel ih =>
      rw [Hex.refineLoop] at hloop
      split at hloop
      · rename_i hempty
        have hwork : work = #[] := Array.eq_empty_of_size_eq_zero
          (Array.isEmpty_iff_size_eq_zero.mp hempty)
        subst work
        simp [Worklist.region] at hz
      · rename_i hnonempty
        let tried := Hex.IsolationLoop.attempts p strategy work
        change (if Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried &&
            Hex.IsolationLoop.allAtoms tried &&
            (Hex.IsolationLoop.outputs tried).size == 1 then
          some (Hex.IsolationLoop.outputs tried)
          else Hex.refineLoop p target strategy fuel
          (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        split at hloop
        · rename_i hemit
          have hrs : rs = Hex.IsolationLoop.outputs tried := by
            exact Option.some.inj hloop.symm
          subst rs
          have hready : Hex.IsolationLoop.allReady target tried := by
            simp only [Bool.and_eq_true] at hemit
            exact hemit.1.1.1
          exact isRoot_mem_outputs hcert hzroot hz hready
        · exact ih hloop (isRoot_mem_next hcert hzroot hz)

/-- A successful one-atom refinement loop meets its target and returns its
single atom certificate (hence a pairwise-disjoint result). -/
theorem refineLoop_ready_disjoint {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {fuel : Nat} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hloop : Hex.refineLoop p target strategy fuel work = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec) ∧
      Hex.pairwiseDisjoint (rs.map (·.square)) = true := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.refineLoop] at hloop
  | succ fuel ih =>
      rw [Hex.refineLoop] at hloop
      split at hloop
      · have hrs : rs = #[] := Option.some.inj hloop.symm
        subst rs
        simp [Hex.pairwiseDisjoint]
      · let tried := Hex.IsolationLoop.attempts p strategy work
        change (if Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried &&
            Hex.IsolationLoop.allAtoms tried &&
            (Hex.IsolationLoop.outputs tried).size == 1 then
          some (Hex.IsolationLoop.outputs tried)
          else Hex.refineLoop p target strategy fuel
          (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        split at hloop
        · rename_i hemit
          simp only [Bool.and_eq_true] at hemit
          have hrs : rs = Hex.IsolationLoop.outputs tried :=
            Option.some.inj hloop.symm
          subst rs
          exact ⟨outputs_ready hemit.1.1.1, by
            simpa [Hex.IsolationLoop.disjoint] using hemit.1.1.2⟩
        · exact ih hloop

/-- Coverage for the bounded lineage-local speculative refinement pass. -/
theorem refineFastLoop_covers {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {fuel : Nat} {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hloop : Hex.refineFastLoop p target strategy fuel work = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.refineFastLoop] at hloop
  | succ fuel ih =>
      rw [Hex.refineFastLoop] at hloop
      split at hloop
      · rename_i hempty
        have hwork : work = #[] := Array.eq_empty_of_size_eq_zero
          (Array.isEmpty_iff_size_eq_zero.mp hempty)
        subst work
        simp [Worklist.region] at hz
      · let tried := Hex.IsolationLoop.attempts p strategy work
        change (if Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried &&
            Hex.IsolationLoop.allAtoms tried &&
            (Hex.IsolationLoop.outputs tried).size == 1 then
          some (Hex.IsolationLoop.outputs tried)
          else Hex.refineFastLoop p target strategy fuel
            (Hex.IsolationLoop.nextLocal p target tried)) = some rs at hloop
        split at hloop
        · rename_i hemit
          have hrs : rs = Hex.IsolationLoop.outputs tried :=
            Option.some.inj hloop.symm
          subst rs
          have hready : Hex.IsolationLoop.allReady target tried := by
            simp only [Bool.and_eq_true] at hemit
            exact hemit.1.1.1
          exact isRoot_mem_outputs hcert hzroot hz hready
        · exact ih hloop (isRoot_mem_nextLocal hcert hzroot hz)

/-- A successful speculative refinement pass returns its single target-ready
atom certificate. -/
theorem refineFastLoop_ready_disjoint {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} {fuel : Nat} {work : Array Hex.Component}
    {rs : Array (Hex.Certified p)}
    (hloop : Hex.refineFastLoop p target strategy fuel work = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec) ∧
      Hex.pairwiseDisjoint (rs.map (·.square)) = true := by
  induction fuel generalizing work rs with
  | zero => simp [Hex.refineFastLoop] at hloop
  | succ fuel ih =>
      rw [Hex.refineFastLoop] at hloop
      split at hloop
      · have hrs : rs = #[] := Option.some.inj hloop.symm
        subst rs
        simp [Hex.pairwiseDisjoint]
      · let tried := Hex.IsolationLoop.attempts p strategy work
        change (if Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried &&
            Hex.IsolationLoop.allAtoms tried &&
            (Hex.IsolationLoop.outputs tried).size == 1 then
          some (Hex.IsolationLoop.outputs tried)
          else Hex.refineFastLoop p target strategy fuel
            (Hex.IsolationLoop.nextLocal p target tried)) = some rs at hloop
        split at hloop
        · rename_i hemit
          simp only [Bool.and_eq_true] at hemit
          have hrs : rs = Hex.IsolationLoop.outputs tried :=
            Option.some.inj hloop.symm
          subst rs
          exact ⟨outputs_ready hemit.1.1.1, by
            simpa [Hex.IsolationLoop.disjoint] using hemit.1.1.2⟩
        · exact ih hloop

/-- An option-valued list map that succeeds preserves length and maps
corresponding entries. -/
private theorem list_mapM_some_get {α β : Type*} {f : α → Option β}
    {xs : List α} {ys : List β} (hmap : xs.mapM f = some ys) :
    xs.length = ys.length ∧
      ∀ (i : Nat) (hi : i < xs.length) (hj : i < ys.length),
        f xs[i] = some ys[i] := by
  induction xs generalizing ys with
  | nil =>
      simp at hmap
      subst ys
      simp
  | cons x xs ih =>
      cases hfx : f x with
      | none => simp [hfx] at hmap
      | some y =>
          cases htail : xs.mapM f with
          | none => simp [hfx, htail] at hmap
          | some ys' =>
              have heq : some (y :: ys') = some ys := by
                simpa [hfx, htail] using hmap
              have hys : ys = y :: ys' := (Option.some.inj heq).symm
              subst ys
              obtain ⟨hlen, hget⟩ := ih htail
              constructor
              · simp [hlen]
              · intro i hi hj
                cases i with
                | zero => simpa using hfx
                | succ i =>
                    simp only [List.getElem_cons_succ]
                    exact hget i (by simpa using hi) (by simpa using hj)

/-- An option-valued array map that succeeds preserves size and maps
corresponding entries.  Shared plumbing for the isolation-loop soundness
proofs here and in `NKDriver`, `Isolate`, and `HexNumberFieldMathlib`. -/
theorem array_mapM_some_get {α β : Type*} {f : α → Option β}
    {xs : Array α} {ys : Array β} (hmap : xs.mapM f = some ys) :
    xs.size = ys.size ∧
      ∀ (i : Nat) (hi : i < xs.size) (hj : i < ys.size),
        f xs[i] = some ys[i] := by
  have hlist : xs.toList.mapM f = some ys.toList := by
    calc
      xs.toList.mapM f = Array.toList <$> xs.mapM f :=
        Array.toList_mapM.symm
      _ = some ys.toList := by rw [hmap]; rfl
  obtain ⟨hlen, hget⟩ := list_mapM_some_get hlist
  refine ⟨by simpa using hlen, ?_⟩
  intro i hi hj
  simpa only [← Array.getElem_toList] using hget i (by simpa using hi)
    (by simpa using hj)

/-- A successful bounded speculative atom refinement reaches the requested
precision. -/
theorem refineFastAtom_ready {p : Hex.ZPoly}
    {iso iso' : Hex.DyadicRootIsolation p} {target : Int}
    {strategy : Hex.AtomStrategy}
    (hrefine : Hex.refineFastAtom? iso target strategy = some iso') :
    target ≤ iso'.square.prec := by
  rw [Hex.refineFastAtom?] at hrefine
  cases hloop : Hex.refineFastLoop p target strategy Hex.fastRefineFuel
      #[⟨#[iso.square.doubled], 1⟩] with
  | none => simp [hloop] at hrefine
  | some rs =>
      simp only [hloop] at hrefine
      split at hrefine
      · rename_i hsize
        cases hget : rs[0]? with
        | none => simp [hget] at hrefine
        | some r =>
            cases r with
            | cluster cl => simp [hget] at hrefine
            | atom tau =>
                simp only [hget, Option.some.injEq] at hrefine
                subst tau
                have hzero : 0 < rs.size := by omega
                have hget0 : rs[0] = .atom iso' := by
                  rw [Array.getElem?_eq_getElem hzero] at hget
                  exact Option.some.inj hget
                have hready := (refineFastLoop_ready_disjoint hloop).1 rs[0]
                  (Array.getElem_mem_toList hzero)
                rw [hget0] at hready
                exact hready
      · simp at hrefine

/-- A successful internal atom refinement reaches the requested precision. -/
theorem refineAtom_ready {p : Hex.ZPoly} {iso iso' : Hex.DyadicRootIsolation p}
    {target : Int} {strategy : Hex.AtomStrategy}
    (hrefine : Hex.refineAtom? iso target strategy = some iso') :
    target ≤ iso'.square.prec := by
  rw [Hex.refineAtom?] at hrefine
  split at hrefine
  · rename_i hready
    have hiso : iso = iso' := Option.some.inj hrefine
    subst iso'
    exact hready
  · rename_i hnotReady
    let fuel := Hex.fuelFor p target iso.square.prec
    cases hloop : Hex.refineLoop p target strategy fuel
        #[⟨#[iso.square.doubled], 1⟩] with
    | none => simp [fuel, hloop] at hrefine
    | some rs =>
        simp only [fuel, hloop] at hrefine
        split at hrefine
        · rename_i hsize
          cases hget : rs[0]? with
          | none => simp [hget] at hrefine
          | some r =>
              cases r with
              | cluster cl => simp [hget] at hrefine
              | atom tau =>
                  simp only [hget, Option.some.injEq] at hrefine
                  subst tau
                  have hzero : 0 < rs.size := by omega
                  have hget0 : rs[0] = .atom iso' := by
                    rw [Array.getElem?_eq_getElem hzero] at hget
                    exact Option.some.inj hget
                  have hready := (refineLoop_ready_disjoint hloop).1 rs[0]
                    (Array.getElem_mem_toList hzero)
                  rw [hget0] at hready
                  exact hready
        · simp at hrefine

/-- Internal atom refinement preserves the atom's semantic root. -/
theorem refineAtom_preserves {p : Hex.ZPoly} {strategy : Hex.AtomStrategy}
    (hcert : Certifier.Preserves p strategy)
    {iso iso' : Hex.DyadicRootIsolation p} {target : Int}
    (hrefine : Hex.refineAtom? iso target strategy = some iso')
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Certified.region (.atom iso)) :
    z ∈ Certified.region (.atom iso') := by
  rw [Hex.refineAtom?] at hrefine
  split at hrefine
  · have hiso : iso = iso' := Option.some.inj hrefine
    simpa [hiso] using hz
  · let fuel := Hex.fuelFor p target iso.square.prec
    cases hloop : Hex.refineLoop p target strategy fuel
        #[⟨#[iso.square.doubled], 1⟩] with
    | none => simp [fuel, hloop] at hrefine
    | some rs =>
        simp only [fuel, hloop] at hrefine
        split at hrefine
        · rename_i hsize
          cases hget : rs[0]? with
          | none => simp [hget] at hrefine
          | some r =>
              cases r with
              | cluster cl => simp [hget] at hrefine
              | atom tau =>
                  simp only [hget, Option.some.injEq] at hrefine
                  subst tau
                  have hzstart : z ∈ Worklist.region
                      #[⟨#[iso.square.doubled], 1⟩] := by
                    refine ⟨⟨#[iso.square.doubled], 1⟩, by simp,
                      iso.square.doubled, by simp, ?_⟩
                    exact Certified.region_subset_doubled (.atom iso) hz
                  have hzrs := refineLoop_covers hcert hloop hzroot hzstart
                  obtain ⟨r, hr, hzr⟩ := hzrs
                  obtain ⟨i, hi, hri⟩ :=
                    Array.getElem_of_mem (Array.mem_toList_iff.mp hr)
                  have hi0 : i = 0 := by omega
                  subst i
                  have hr0 : r = rs[0] := hri.symm
                  have hrs0 : rs[0] = .atom iso' := by
                    have hzero : 0 < rs.size := by omega
                    rw [Array.getElem?_eq_getElem hzero] at hget
                    exact Option.some.inj hget
                  simpa [hr0, hrs0] using hzr
        · simp at hrefine

/-- The bounded speculative atom refinement preserves the atom's semantic
root whenever it succeeds. -/
theorem refineFastAtom_preserves {p : Hex.ZPoly}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {iso iso' : Hex.DyadicRootIsolation p} {target : Int}
    (hrefine : Hex.refineFastAtom? iso target strategy = some iso')
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Certified.region (.atom iso)) :
    z ∈ Certified.region (.atom iso') := by
  rw [Hex.refineFastAtom?] at hrefine
  cases hloop : Hex.refineFastLoop p target strategy Hex.fastRefineFuel
      #[⟨#[iso.square.doubled], 1⟩] with
  | none => simp [hloop] at hrefine
  | some rs =>
      simp only [hloop] at hrefine
      split at hrefine
      · rename_i hsize
        cases hget : rs[0]? with
        | none => simp [hget] at hrefine
        | some r =>
            cases r with
            | cluster cl => simp [hget] at hrefine
            | atom tau =>
                simp only [hget, Option.some.injEq] at hrefine
                subst tau
                have hzstart : z ∈ Worklist.region
                    #[⟨#[iso.square.doubled], 1⟩] := by
                  refine ⟨⟨#[iso.square.doubled], 1⟩, by simp,
                    iso.square.doubled, by simp, ?_⟩
                  exact Certified.region_subset_doubled (.atom iso) hz
                have hzrs := refineFastLoop_covers hcert hloop hzroot hzstart
                obtain ⟨r, hr, hzr⟩ := hzrs
                obtain ⟨i, hi, hri⟩ :=
                  Array.getElem_of_mem (Array.mem_toList_iff.mp hr)
                have hi0 : i = 0 := by omega
                subst i
                have hr0 : r = rs[0] := hri.symm
                have hrs0 : rs[0] = .atom iso' := by
                  have hzero : 0 < rs.size := by omega
                  rw [Array.getElem?_eq_getElem hzero] at hget
                  exact Option.some.inj hget
                simpa [hr0, hrs0] using hzr
      · simp at hrefine

/-- Refining one successful atom in the all-atoms finisher reaches the
requested precision, whether the bounded local pass succeeds or the complete
fallback is needed. -/
private theorem attemptReadyAtom {p : Hex.ZPoly} {c : Hex.Component}
    {iso iso' : Hex.DyadicRootIsolation p} {target : Int}
    {strategy : Hex.AtomStrategy}
    (hrefine : Hex.IsolationLoop.refineAttempt? target strategy
      (c, some (.atom iso)) = some iso') :
    target ≤ iso'.square.prec := by
  simp only [Hex.IsolationLoop.refineAttempt?] at hrefine
  split at hrefine
  · rename_i hready
    have hiso : iso = iso' := Option.some.inj hrefine
    simpa [hiso] using hready
  · cases hfast : Hex.refineFastAtom? iso target strategy with
    | none =>
      simp only [hfast, Option.orElse_none] at hrefine
      exact refineAtom_ready hrefine
    | some tau =>
      simp only [hfast, Option.orElse_some] at hrefine
      have htau : tau = iso' := Option.some.inj hrefine
      subst iso'
      exact refineFastAtom_ready hfast

/-- Every successful all-atoms refinement attempt reaches the requested
precision. -/
theorem refineAttempt_ready {p : Hex.ZPoly}
    {t : Hex.Component × Option (Hex.Certified p)}
    {iso' : Hex.DyadicRootIsolation p} {target : Int}
    {strategy : Hex.AtomStrategy}
    (hrefine : Hex.IsolationLoop.refineAttempt? target strategy t = some iso') :
    target ≤ iso'.square.prec := by
  obtain ⟨c, result⟩ := t
  cases result with
  | none => simp [Hex.IsolationLoop.refineAttempt?] at hrefine
  | some result =>
    cases result with
    | cluster cl => simp [Hex.IsolationLoop.refineAttempt?] at hrefine
    | atom iso => exact attemptReadyAtom hrefine

/-- Refining one successful atom in the all-atoms finisher preserves its
semantic root across both the bounded local pass and the complete fallback. -/
theorem refineAttempt_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {iso iso' : Hex.DyadicRootIsolation p} {target : Int}
    (hrefine : Hex.IsolationLoop.refineAttempt? target strategy
      (c, some (.atom iso)) = some iso')
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Certified.region (.atom iso)) :
    z ∈ Certified.region (.atom iso') := by
  simp only [Hex.IsolationLoop.refineAttempt?] at hrefine
  split at hrefine
  · have hiso : iso = iso' := Option.some.inj hrefine
    simpa [hiso] using hz
  · cases hfast : Hex.refineFastAtom? iso target strategy with
    | none =>
      simp only [hfast, Option.orElse_none] at hrefine
      exact refineAtom_preserves hcert hrefine hzroot hz
    | some tau =>
      simp only [hfast, Option.orElse_some] at hrefine
      have htau : tau = iso' := Option.some.inj hrefine
      subst iso'
      exact refineFastAtom_preserves hcert hfast hzroot hz

/-- The opportunistic all-atoms fast path returns atoms only. -/
theorem finishAllAtoms_atoms {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    {rs : Array (Hex.Certified p)}
    (hfinish : Hex.IsolationLoop.finishAllAtoms? p target strategy tried = some rs) :
    ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  unfold Hex.IsolationLoop.finishAllAtoms? at hfinish
  split at hfinish
  · cases hmap : tried.mapM
        (Hex.IsolationLoop.refineAttempt? target strategy) with
    | none =>
        rw [hmap] at hfinish
        simp at hfinish
    | some atoms =>
        rw [hmap] at hfinish
        dsimp only at hfinish
        split at hfinish
        · have hrs : rs = atoms.map Hex.Certified.atom :=
            Option.some.inj hfinish.symm
          subst rs
          intro r hr
          obtain ⟨iso, -, rfl⟩ :=
            Array.mem_map.mp (Array.mem_toList_iff.mp hr)
          exact ⟨iso, rfl⟩
        · simp at hfinish
  · simp at hfinish

/-- A successful all-atoms fast path meets the target and returns pairwise
disjoint atom discs. -/
theorem finishAllAtoms_ready_disjoint {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    {rs : Array (Hex.Certified p)}
    (hfinish : Hex.IsolationLoop.finishAllAtoms? p target strategy tried = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec) ∧
      Hex.pairwiseDisjoint (rs.map (·.square)) = true := by
  unfold Hex.IsolationLoop.finishAllAtoms? at hfinish
  split at hfinish
  · cases hmap : tried.mapM
        (Hex.IsolationLoop.refineAttempt? target strategy) with
    | none =>
        rw [hmap] at hfinish
        simp at hfinish
    | some atoms =>
        rw [hmap] at hfinish
        dsimp only at hfinish
        split at hfinish
        · rename_i hpair
          have hrs : rs = atoms.map Hex.Certified.atom :=
            Option.some.inj hfinish.symm
          subst rs
          constructor
          · intro r hr
            obtain ⟨iso, hiso, hr⟩ :=
              Array.mem_map.mp (Array.mem_toList_iff.mp hr)
            subst r
            obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem hiso
            have hsize := (array_mapM_some_get hmap).1
            have hiTried : i < tried.size := by omega
            have hmapGet := (array_mapM_some_get hmap).2 i hiTried hi
            rw [hget] at hmapGet
            exact refineAttempt_ready hmapGet
          · have harr :
                (atoms.map Hex.Certified.atom).map (·.square) =
                  atoms.map (·.square) := by
                apply Array.ext
                · simp
                · intro i hi₁ hi₂
                  simp only [Array.getElem_map]
                  rfl
            rw [harr]
            exact hpair
        · simp at hfinish
  · simp at hfinish

/-- The all-atoms fast path preserves every polynomial root covered by its
attempted worklist. -/
theorem finishAllAtoms_covers {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hfinish : Hex.IsolationLoop.finishAllAtoms? p target strategy
      (Hex.IsolationLoop.attempts p strategy work) = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  obtain ⟨c, hc, hzc⟩ := hz
  let tried := Hex.IsolationLoop.attempts p strategy work
  have ht : (c, Hex.Component.certify? p strategy c) ∈ tried := by
    apply Array.mem_map_of_mem
    exact Array.mem_toList_iff.mp hc
  change Hex.IsolationLoop.finishAllAtoms? p target strategy tried = some rs at hfinish
  unfold Hex.IsolationLoop.finishAllAtoms? at hfinish
  split at hfinish
  · rename_i hatoms
    have hguard : Hex.IsolationLoop.allAtoms tried = true ∧
        Hex.IsolationLoop.disjoint tried = true := by
      simpa only [Bool.and_eq_true] using hatoms
    have htAtom := (Array.all_eq_true_iff_forall_mem.mp hguard.1) _ ht
    cases htry : Hex.Component.certify? p strategy c with
    | none => simp [htry] at htAtom
    | some result =>
        cases result with
        | cluster cl => simp [htry] at htAtom
        | atom iso =>
            cases hmap : tried.mapM
                (Hex.IsolationLoop.refineAttempt? target strategy) with
            | none =>
                rw [hmap] at hfinish
                simp at hfinish
            | some atoms =>
                rw [hmap] at hfinish
                dsimp only at hfinish
                split at hfinish
                · have hrs : rs = atoms.map Hex.Certified.atom :=
                      Option.some.inj hfinish.symm
                  subst rs
                  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem ht
                  have hsize := (array_mapM_some_get hmap).1
                  have hiAtoms : i < atoms.size := by omega
                  have hmapGet := (array_mapM_some_get hmap).2 i hi hiAtoms
                  rw [hget] at hmapGet
                  simp only [htry] at hmapGet
                  have hziso : z ∈ Certified.region (.atom iso) :=
                    hcert c (.atom iso) htry z hzroot hzc
                  have hzrefined := refineAttempt_preserves hcert hmapGet hzroot hziso
                  refine ⟨.atom atoms[i], ?_, hzrefined⟩
                  apply Array.mem_toList_iff.mpr
                  apply Array.mem_map_of_mem
                  exact Array.getElem_mem hiAtoms
                · simp at hfinish
  · simp at hfinish

/-- A successful atom-only finish emits only atom certificates. -/
theorem finishAtoms_atoms {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    {rs : Array (Hex.Certified p)}
    (hfinish : Hex.IsolationLoop.finishAtoms? p target strategy tried = some rs) :
    ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  cases strategy with
  | nk => simp [Hex.IsolationLoop.finishAtoms?] at hfinish
  | pellet =>
      apply finishAllAtoms_atoms
      simpa [Hex.IsolationLoop.finishAtoms?] using hfinish
  | nkThenPellet =>
      apply finishAllAtoms_atoms
      simpa [Hex.IsolationLoop.finishAtoms?] using hfinish

/-- A successful atom-only finish meets the target precision and emits
pairwise-disjoint squares. -/
theorem finishAtoms_ready_disjoint {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    {rs : Array (Hex.Certified p)}
    (hfinish : Hex.IsolationLoop.finishAtoms? p target strategy tried = some rs) :
    (∀ r ∈ rs.toList, target ≤ r.square.prec) ∧
      Hex.pairwiseDisjoint (rs.map (·.square)) = true := by
  cases strategy with
  | nk => simp [Hex.IsolationLoop.finishAtoms?] at hfinish
  | pellet =>
      apply finishAllAtoms_ready_disjoint
      simpa [Hex.IsolationLoop.finishAtoms?] using hfinish
  | nkThenPellet =>
      apply finishAllAtoms_ready_disjoint
      simpa [Hex.IsolationLoop.finishAtoms?] using hfinish

/-- With a preserving certifier, a successful atom-only finish covers every
root covered by the input worklist. -/
theorem finishAtoms_covers {p : Hex.ZPoly} {target : Int}
    {strategy : Hex.AtomStrategy} (hcert : Certifier.Preserves p strategy)
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hfinish : Hex.IsolationLoop.finishAtoms? p target strategy
      (Hex.IsolationLoop.attempts p strategy work) = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs := by
  cases strategy with
  | nk => simp [Hex.IsolationLoop.finishAtoms?] at hfinish
  | pellet =>
      have hcore : Hex.IsolationLoop.finishAllAtoms? p target .pellet
          (Hex.IsolationLoop.attempts p .pellet work) = some rs := by
        simpa [Hex.IsolationLoop.finishAtoms?] using hfinish
      exact finishAllAtoms_covers hcert hcore hzroot hz
  | nkThenPellet =>
      have hcore : Hex.IsolationLoop.finishAllAtoms? p target .nkThenPellet
          (Hex.IsolationLoop.attempts p .nkThenPellet work) = some rs := by
        simpa [Hex.IsolationLoop.finishAtoms?] using hfinish
      exact finishAllAtoms_covers hcert hcore hzroot hz

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
      · let tried := Hex.IsolationLoop.attempts p strategy work
        change (match Hex.IsolationLoop.finishAtoms? p target strategy tried with
          | some out => some out
          | none =>
            if Hex.IsolationLoop.emitReady target strategy tried then
              some (Hex.IsolationLoop.outputs tried)
            else Hex.isolateLoop p target strategy fuel
              (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        cases hfinish : Hex.IsolationLoop.finishAtoms? p target strategy tried with
        | some out =>
            simp only [hfinish] at hloop
            have hrs : rs = out := Option.some.inj hloop.symm
            subst rs
            exact finishAtoms_covers hcert hfinish hzroot hz
        | none =>
            simp only [hfinish] at hloop
            split at hloop
            · rename_i hemit
              have hrs : rs = Hex.IsolationLoop.outputs tried :=
                Option.some.inj hloop.symm
              subst rs
              have hready : Hex.IsolationLoop.allReady target tried := by
                unfold Hex.IsolationLoop.emitReady at hemit
                simp only [Bool.and_eq_true] at hemit
                exact hemit.2.1
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
        change (match Hex.IsolationLoop.finishAtoms? p target strategy tried with
          | some out => some out
          | none =>
            if Hex.IsolationLoop.emitReady target strategy tried then
              some (Hex.IsolationLoop.outputs tried)
            else Hex.isolateLoop p target strategy fuel
              (Hex.IsolationLoop.next p target tried)) = some rs at hloop
        cases hfinish : Hex.IsolationLoop.finishAtoms? p target strategy tried with
        | some out =>
            simp only [hfinish] at hloop
            have hrs : rs = out := Option.some.inj hloop.symm
            subst rs
            exact finishAtoms_ready_disjoint hfinish
        | none =>
            simp only [hfinish] at hloop
            split at hloop
            · rename_i hemit
              unfold Hex.IsolationLoop.emitReady at hemit
              simp only [Bool.and_eq_true] at hemit
              have hrs : rs = Hex.IsolationLoop.outputs tried :=
                Option.some.inj hloop.symm
              subst rs
              exact ⟨outputs_ready hemit.2.1, by
                simpa [Hex.IsolationLoop.disjoint] using hemit.2.2⟩
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
