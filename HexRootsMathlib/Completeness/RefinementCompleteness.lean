/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.DriverCompleteness
public import HexRootsMathlib.Refinement
public import HexRootsMathlib.SimpleRoot

public section

/-!
# Completeness of one-atom refinement

An atom certifies one locally simple root, but its ambient polynomial may have
repeated roots elsewhere.  The refinement loop therefore carries a local
confinement invariant through its globally reglued prefix and uses general
Mahler separation only to identify every sufficiently fine survivor with the
represented root.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

namespace Worklist

/-- Every worklist square remains inside the starting atom neighborhood. -/
@[expose] def Within (work : Array Hex.Component)
    (outer : Hex.DyadicSquare) : Prop :=
  ∀ c ∈ work.toList, ∀ s ∈ c.squares.toList,
    DyadicSquare.closedSquare s ⊆ DyadicSquare.closedSquare outer

/-- A globally reglued subdivision round preserves confinement. -/
theorem refineAll_within {p : Hex.ZPoly} {work : Array Hex.Component}
    {outer : Hex.DyadicSquare} (hwithin : Within work outer) :
    Within (Hex.Component.refineAll p work) outer := by
  intro c hc u hu
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun t => !Hex.rootFree p t)
  rw [Hex.Component.refineAll] at hc
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  simp only [Array.toList_map, List.mem_map] at hc
  obtain ⟨component, hcomponent, rfl⟩ := hc
  have husurv : u ∈ survivors.toList :=
    mem_of_mem_glueCovered hcomponent hu
  have huchild : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList := by
    have husurv' :
        u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
          Hex.rootFree p u = false := by
      simpa [survivors] using husurv
    exact husurv'.1
  rw [Array.toList_flatMap, List.mem_flatMap] at huchild
  obtain ⟨s, hs, hus⟩ := huchild
  change s ∈ (Worklist.squares work).toList at hs
  rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hs
  obtain ⟨d, hd, hsd⟩ := hs
  exact (DyadicSquare.closedSquare_subset_of_mem_subdivide hus).trans
    (hwithin d hd s hsd)

/-- Every square emitted by `refineAll` failed the executable `T₀` test. -/
theorem refineAll_mem_not_rootFree {p : Hex.ZPoly}
    {work : Array Hex.Component} {c : Hex.Component}
    (hc : c ∈ (Hex.Component.refineAll p work).toList)
    {s : Hex.DyadicSquare} (hs : s ∈ c.squares.toList) :
    Hex.rootFree p s ≠ true := by
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  rw [Hex.Component.refineAll] at hc
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  simp only [Array.toList_map, List.mem_map] at hc
  obtain ⟨component, hcomponent, rfl⟩ := hc
  have hsurv : s ∈ survivors.toList :=
    mem_of_mem_glueCovered hcomponent hs
  have hdata : Hex.rootFree p s = false := by
    have : s ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p s = false := by simpa [survivors] using hsurv
    exact this.2
  simp [hdata]

end Worklist

/-- A retained separation-depth square confined to a refined atom's doubled
square has that atom's locally simple root as its sharp nearby root. -/
theorem nearRoot_of_outer {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) {s : Hex.DyadicSquare}
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    (hkeep : Hex.rootFree p s ≠ true)
    (hwithin : DyadicSquare.closedSquare s ⊆
      DyadicSquare.closedSquare rep.1.square.doubled) :
    NearRoot p s (RefinedIsolation.root rep) := by
  let z := RefinedIsolation.root rep
  let base := rep.1.square
  let outer := base.doubled
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  have hsize : 1 < p.size := rep.1.size_gt_one
  have hp : p ≠ 0 := RefinedIsolation.poly_ne_zero rep
  have hpℂ : toPolyℂ p ≠ 0 := toPolyℂ_ne_zero p (by
    exact Nat.ne_of_gt (by omega : 0 < p.size))
  have hzroot : (toPolyℂ p).IsRoot z := RefinedIsolation.isRoot rep
  have hsimple : (toPolyℂ p).derivative.eval z ≠ 0 :=
    (RefinedIsolation.root_spec rep).2.2.1
  obtain ⟨w, hw, hwnear⟩ :=
    exists_root_ne_of_depth hpℂ (by omega) hprec hkeep
  have hwroot : (toPolyℂ p).IsRoot w := (mem_roots hpℂ).1 hw
  have hM : 0 < M := by dsimp [M]; positivity
  have hpow : (2 : ℝ) ^ (-base.prec) ≤
      (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have := rep.property
    dsimp only [base]
    omega
  have hsqrt : √2 < (1449 / 1024 : ℝ) := by
    convert sqrt_two_lt_sqrt2Hi using 1
    norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
  have hbaseRadius : DyadicSquare.radius base < M := by
    calc
      DyadicSquare.radius base =
          (2 : ℝ) ^ (-base.prec) * √2 := DyadicSquare.radius_eq _
      _ < (2 : ℝ) ^ (-base.prec) * (1449 / 1024 : ℝ) :=
        mul_lt_mul_of_pos_left hsqrt
          (zpow_pos (by norm_num) _)
      _ ≤ M := by
        dsimp [M]
        exact mul_le_mul_of_nonneg_right hpow (by norm_num)
  have hzbase : ‖z - DyadicSquare.center base‖ ≤
      DyadicSquare.radius base := by
    have hz := RefinedIsolation.root_mem_closedDisc rep
    simpa [DyadicSquare.closedDisc, mem_closedBall, Complex.dist_eq] using hz
  have hsouter : DyadicSquare.center s ∈ DyadicSquare.closedSquare outer :=
    hwithin (DyadicSquare.center_mem_closedSquare s)
  have hcenterSup : supNorm
      (DyadicSquare.center s - DyadicSquare.center outer) ≤
      DyadicSquare.halfWidth outer := by
    simpa [DyadicSquare.closedSquare, supClosedBall, supDist] using hsouter
  have hcenterNorm : ‖DyadicSquare.center s - DyadicSquare.center outer‖ ≤
      √2 * DyadicSquare.halfWidth outer :=
    (Complex.norm_le_sqrt_two_mul_max _).trans
      (mul_le_mul_of_nonneg_left hcenterSup (Real.sqrt_nonneg _))
  have houterRadius :
      √2 * DyadicSquare.halfWidth outer < 2 * M := by
    rw [show DyadicSquare.halfWidth outer =
        2 * DyadicSquare.halfWidth base by
      exact DyadicSquare.doubled_halfWidth base]
    have hbaseEq : DyadicSquare.radius base =
        DyadicSquare.halfWidth base * √2 := rfl
    rw [hbaseEq] at hbaseRadius
    nlinarith
  have hzwUpper : ‖z - w‖ < 4 * M := by
    have htri : ‖z - w‖ ≤
        ‖z - DyadicSquare.center base‖ +
          ‖DyadicSquare.center s - DyadicSquare.center outer‖ +
            ‖w - DyadicSquare.center s‖ := by
      calc
        ‖z - w‖ = ‖(z - DyadicSquare.center base) -
            (DyadicSquare.center s - DyadicSquare.center outer) -
              (w - DyadicSquare.center s)‖ := by
          change ‖z - w‖ = ‖(z - DyadicSquare.center base) -
            (DyadicSquare.center s - DyadicSquare.center base) -
              (w - DyadicSquare.center s)‖
          ring_nf
        _ ≤ ‖(z - DyadicSquare.center base) -
              (DyadicSquare.center s - DyadicSquare.center outer)‖ +
            ‖w - DyadicSquare.center s‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    change ‖w - DyadicSquare.center s‖ < M / 32 at hwnear
    nlinarith [htri, hzbase, hbaseRadius, hcenterNorm, houterRadius]
  have hwz : w = z := by
    by_contra hne
    have hsep := mahlerPrec_separates p hp w z hwroot hzroot hne
    change M < ‖w - z‖ / 4 at hsep
    rw [norm_sub_rev] at hsep
    nlinarith
  subst w
  refine ⟨hw, ?_⟩
  exact root_near_of_simple hpℂ hsize hzroot hsimple
    hprec hkeep (by simpa [M, z] using hwnear)

/-- If every retained square is sharply near the same root and one survivor
actually contains that root, maximal gluing puts the root in every output
component. -/
theorem root_mem_glueCovered
    {squares component : Array Hex.DyadicSquare} {prec : Int} {z : ℂ}
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hnear : ∀ u ∈ squares.toList,
      ‖z - DyadicSquare.center u‖ ≤
        (65 / 32 : ℝ) * Dyadic.toReal u.radiusHi)
    (hcover : ∃ t ∈ squares.toList,
      z ∈ DyadicSquare.closedSquare t)
    (hc : component ∈ (Hex.glueCovered squares).toList) :
    z ∈ Component.region ⟨component, 1⟩ := by
  have hconnected := glueCovered_connected squares component hc
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil component.toList hconnected.1
  obtain ⟨t, ht, hzt⟩ := hcover
  obtain ⟨other, hother, htother⟩ := mem_glueCovered ht
  have hsAll : s ∈ squares.toList := mem_of_mem_glueCovered hc hs
  have hsPrec : s.prec = prec := hprec s hsAll
  have htPrec : t.prec = prec := hprec t ht
  have hwidth : DyadicSquare.halfWidth t =
      DyadicSquare.halfWidth s := by
    rw [DyadicSquare.halfWidth_eq, DyadicSquare.halfWidth_eq,
      hsPrec, htPrec]
  have hnearS := hnear s hsAll
  have hnearSup : supDist (DyadicSquare.center s) z ≤
      ‖z - DyadicSquare.center s‖ := by
    have hsnorm : supNorm (DyadicSquare.center s - z) ≤
        ‖DyadicSquare.center s - z‖ :=
      max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
    calc
      supDist (DyadicSquare.center s) z =
          supNorm (DyadicSquare.center s - z) := rfl
      _ ≤ ‖DyadicSquare.center s - z‖ := hsnorm
      _ = ‖z - DyadicSquare.center s‖ := by rw [norm_sub_rev]
  have hztSup : supDist z (DyadicSquare.center t) ≤
      DyadicSquare.halfWidth t := hzt
  have htri : supDist (DyadicSquare.center s) (DyadicSquare.center t) ≤
      supDist (DyadicSquare.center s) z +
        supDist z (DyadicSquare.center t) := by
    unfold supDist
    calc
      supNorm (DyadicSquare.center s - DyadicSquare.center t) =
          supNorm ((DyadicSquare.center s - z) +
            (z - DyadicSquare.center t)) := by ring_nf
      _ ≤ _ := supNorm_add_le _ _
  have hR : Dyadic.toReal s.radiusHi =
      DyadicSquare.halfWidth s * (1449 / 1024 : ℝ) := by
    rw [DyadicSquare.radiusHi_eq]
    norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
  have hh : 0 < DyadicSquare.halfWidth s := by
    rw [DyadicSquare.halfWidth_eq]
    positivity
  have hdist :
      supDist (DyadicSquare.center s) (DyadicSquare.center t) <
        4 * DyadicSquare.halfWidth s := by
    rw [hR] at hnearS
    rw [hwidth] at hztSup
    nlinarith
  have hedge : Glue.Edge s t :=
    DyadicSquare.adjacent_of_supDist_lt (hsPrec.trans htPrec.symm) hdist
  have heq : other = component := by
    by_contra hne
    have hno := glueCovered_separated squares component hc other hother
      (fun h => hne h.symm) s hs t htother
    exact hno.1 hedge
  subst other
  exact ⟨t, htother, hzt⟩

/-- Every component of a sufficiently fine confined refinement round contains
the represented simple root. -/
theorem refineAll_carries_root {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) {work : Array Hex.Component} {prec : Int}
    (hdepth : (Hex.separationDepth p : Int) ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hwithin : Worklist.Within work rep.1.square.doubled)
    (hcover : RefinedIsolation.root rep ∈ Worklist.region work)
    {c : Hex.Component} (hc : c ∈ (Hex.Component.refineAll p work).toList) :
    RefinedIsolation.root rep ∈ Component.region c := by
  let z := RefinedIsolation.root rep
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  obtain ⟨d, hd, s, hs, hzs⟩ := hcover
  have hsquares : s ∈ squares.toList := by
    change s ∈ (Worklist.squares work).toList
    rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap]
    exact ⟨d, hd, hs⟩
  obtain ⟨t, ht, hzt⟩ := isRoot_mem_survivors
    (RefinedIsolation.isRoot rep) hsquares hzs
  change t ∈ survivors.toList at ht
  rw [Hex.Component.refineAll] at hc
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  simp only [Array.toList_map, List.mem_map] at hc
  obtain ⟨component, hcomponent, rfl⟩ := hc
  apply root_mem_glueCovered (squares := survivors)
    (component := component) (prec := prec + 1)
    (z := RefinedIsolation.root rep)
  · intro u hu
    have hu' : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p u = false := by simpa [survivors] using hu
    rw [Array.toList_flatMap, List.mem_flatMap] at hu'
    obtain ⟨v, hv, huv⟩ := hu'.1
    change v ∈ (Worklist.squares work).toList at hv
    rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hv
    obtain ⟨e, he, hve⟩ := hv
    have hvprec := hprec e he v hve
    simp [Hex.DyadicSquare.subdivide] at huv
    rcases huv with rfl | rfl | rfl | rfl <;> simp [hvprec]
  · intro u hu
    have hu' : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p u = false := by simpa [survivors] using hu
    have hchild := hu'.1
    rw [Array.toList_flatMap, List.mem_flatMap] at hchild
    obtain ⟨v, hv, huv⟩ := hchild
    change v ∈ (Worklist.squares work).toList at hv
    rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hv
    obtain ⟨e, he, hve⟩ := hv
    have huwithin :=
      (DyadicSquare.closedSquare_subset_of_mem_subdivide huv).trans
        (hwithin e he v hve)
    have huprec : (Hex.separationDepth p : Int) ≤ u.prec := by
      have hvprec := hprec e he v hve
      simp [Hex.DyadicSquare.subdivide] at huv
      rcases huv with rfl | rfl | rfl | rfl <;> simp [hvprec] <;> omega
    have hkeep : Hex.rootFree p u ≠ true := by simp [hu'.2]
    exact (nearRoot_of_outer rep huprec hkeep huwithin).2
  · exact ⟨t, ht, hzt⟩
  · exact hcomponent

private theorem newtonCandidate_prec {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hsize : 1 < p.size) :
    s.prec ≤ (Hex.newtonSquare p s 1).doubled.prec := by
  simp [Hex.newtonSquare, Hex.TaylorShift.newtonSquare,
    Hex.TaylorShift.compute, Hex.taylor_size, show ¬p.size < 2 by omega]

/-- A checked NK base makes the mixed certifier return an atom without losing
stored precision. -/
private theorem certifyMixed_atom {p : Hex.ZPoly} {c : Hex.Component}
    (hsize : 1 < p.size)
    (hbase : Hex.nkWitness p (Hex.encSquare c.squares).doubled) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.Component.certify? p .nkThenPellet c = some (.atom iso) ∧
        (Hex.encSquare c.squares).doubled.prec ≤ iso.square.prec := by
  simp only [Hex.Component.certify?, Hex.nkWitness] at hbase ⊢
  split <;> rename_i hbase'
  · split <;> rename_i hins
    · split <;> rename_i hcand
      · refine ⟨⟨_, .nk hcand⟩, rfl, ?_⟩
        exact newtonCandidate_prec hsize
      · exact ⟨⟨_, .nk hbase'⟩, rfl, le_rfl⟩
    · exact ⟨⟨_, .nk hbase'⟩, rfl, le_rfl⟩
  · exact (hbase' hbase).elim

private theorem allAtoms_outputs {p : Hex.ZPoly}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    (h : Hex.IsolationLoop.allAtoms tried = true) :
    ∀ r ∈ (Hex.IsolationLoop.outputs tried).toList,
      ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  rw [Hex.IsolationLoop.allAtoms,
    Array.all_eq_true_iff_forall_mem] at h
  intro r hr
  obtain ⟨t, ht, htr⟩ :=
    Array.mem_filterMap.mp (Array.mem_toList_iff.mp hr)
  specialize h t ht
  rcases t with ⟨c, o⟩
  cases o with
  | none => simp at h
  | some result =>
      cases result with
      | atom iso =>
          simp only at htr
          exact ⟨iso, (Option.some.inj htr).symm⟩
      | cluster cl => simp at h

private theorem outputs_single_atom {p : Hex.ZPoly}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    (hatoms : Hex.IsolationLoop.allAtoms tried = true)
    (hsize : (Hex.IsolationLoop.outputs tried).size = 1) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.IsolationLoop.outputs tried = #[.atom iso] := by
  obtain ⟨r, hr⟩ := Array.size_eq_one_iff.mp hsize
  obtain ⟨iso, hiso⟩ := allAtoms_outputs hatoms r (by rw [hr]; simp)
  subst r
  exact ⟨iso, hr⟩

private theorem component_prec_eq {work : Array Hex.Component} {prec : Int}
    (hprec : Worklist.AtPrec work prec) {c : Hex.Component}
    (hc : c ∈ work.toList) {z : ℂ} (hzc : z ∈ Component.region c) :
    c.prec = prec := by
  obtain ⟨s, hs, hzs⟩ := hzc
  have hnonempty : 0 < c.squares.size := by
    have : 0 < c.squares.toList.length := List.length_pos_of_mem hs
    simpa using this
  have hzero : c.squares[0].prec = prec :=
    hprec c hc c.squares[0] (Array.getElem_mem_toList hnonempty)
  rw [Hex.Component.prec, Array.getElem?_eq_getElem hnonempty]
  simpa using hzero

private theorem normalized_false_of_root {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) {target prec : Int}
    {work : Array Hex.Component}
    (hprec : Worklist.AtPrec work prec)
    (hcover : RefinedIsolation.root rep ∈ Worklist.region work)
    (hlt : prec < Hex.completenessDepth p target) :
    Hex.IsolationLoop.normalized p target
      (Hex.IsolationLoop.attempts p .nkThenPellet work) = false := by
  obtain ⟨c, hc, hzc⟩ := hcover
  have hcprec := component_prec_eq hprec hc hzc
  rw [Hex.IsolationLoop.normalized, Array.all_eq_false']
  refine ⟨(c, Hex.Component.certify? p .nkThenPellet c), ?_, ?_⟩
  · rw [Hex.IsolationLoop.attempts]
    exact Array.mem_map_of_mem (Array.mem_toList_iff.mp hc)
  · simp only [hcprec, Bool.not_eq_true]
    simpa only [decide_eq_false_iff_not] using (not_le.mpr hlt)

/-- At the last normalized round, a confined one-atom worklist becomes one
component and that component returns a target-ready mixed-strategy atom. -/
theorem refineAll_success {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) {work : Array Hex.Component}
    {prec target : Int}
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hwithin : Worklist.Within work rep.1.square.doubled)
    (hcover : RefinedIsolation.root rep ∈ Worklist.region work) :
    ∃ c iso,
      Hex.Component.refineAll p work = #[c] ∧
        Hex.Component.certify? p .nkThenPellet c = some (.atom iso) ∧
          target ≤ iso.square.prec := by
  let final := Hex.Component.refineAll p work
  let z := RefinedIsolation.root rep
  have hzroot : (toPolyℂ p).IsRoot z := RefinedIsolation.isRoot rep
  have hcoverFinal : z ∈ Worklist.region final := by
    exact isRoot_mem_refineAll hzroot hcover
  obtain ⟨c₀, hc₀, hzc₀⟩ := hcoverFinal
  have hroot (c : Hex.Component) (hc : c ∈ final.toList) :
      z ∈ Component.region c := by
    apply refineAll_carries_root rep (by omega) hprec hwithin hcover
    exact hc
  have hall : ∀ c ∈ final.toList, c = c₀ := by
    intro c hc
    by_contra hne
    have hdistinct := refineAll_roots_ne hprec hc hc₀ hne
      (hroot c hc) hzc₀
    exact hdistinct rfl
  have hlist : final.toList = [c₀] := by
    have hnodup : final.toList.Nodup := refineAll_nodup p work
    cases hfinal : final.toList with
    | nil => simp [hfinal] at hc₀
    | cons c cs =>
        have hc : c = c₀ := hall c (by simp [hfinal])
        subst c
        have hcs : cs = [] := by
          by_contra hne
          obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil cs hne
          have hdFinal : d ∈ final.toList := by simp [hfinal, hd]
          have hdEq : d = c₀ := hall d hdFinal
          subst d
          rw [hfinal, List.nodup_cons] at hnodup
          exact hnodup.1 hd
        subst cs
        rfl
  have hfinal : final = #[c₀] := by
    apply Array.toList_inj.mp
    exact hlist
  have hc₀' : c₀ ∈ (Hex.Component.refineAll p work).toList := by
    simpa only [final] using hc₀
  have hwithinFinal : Worklist.Within final rep.1.square.doubled := by
    exact Worklist.refineAll_within hwithin
  have hnear : ∀ u ∈ c₀.squares.toList,
      ‖z - DyadicSquare.center u‖ ≤
        (65 / 32 : ℝ) * Dyadic.toReal u.radiusHi := by
    intro u hu
    have huprec : (Hex.separationDepth p : Int) ≤ u.prec := by
      have := refineAll_mem_prec hprec hc₀' hu
      omega
    have hkeep := Worklist.refineAll_mem_not_rootFree hc₀' hu
    have huwithin : DyadicSquare.closedSquare u ⊆
        DyadicSquare.closedSquare rep.1.square.doubled := by
      exact hwithinFinal c₀ (by simpa only [final] using hc₀) u hu
    exact (nearRoot_of_outer rep huprec hkeep huwithin).2
  have hnonempty : 0 < c₀.squares.size := by
    obtain ⟨u, hu, hzu⟩ := hzc₀
    have : 0 < c₀.squares.toList.length := List.length_pos_of_mem hu
    simpa using this
  have henc : prec + 1 - 2 ≤ (Hex.encSquare c₀.squares).prec := by
    apply DyadicSquare.encSquare_prec_of_near hnonempty
    · intro u hu
      exact refineAll_mem_prec hprec hc₀' hu
    · exact hnear
  let enc := Hex.encSquare c₀.squares
  let base := enc.doubled
  have hbasePrec : (Hex.separationDepth p : Int) ≤ base.prec := by
    change (Hex.separationDepth p : Int) ≤
      (Hex.encSquare c₀.squares).prec - 1
    omega
  have hzenc : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare c₀ hzc₀
  have hzsup : supNorm (z - DyadicSquare.center enc) ≤
      DyadicSquare.halfWidth enc := by
    simpa [DyadicSquare.closedSquare, supClosedBall, supDist] using hzenc
  have hcenter : supNorm (z - DyadicSquare.center base) ≤
      DyadicSquare.halfWidth base / 2 := by
    rw [show DyadicSquare.center base = DyadicSquare.center enc by rfl,
      show DyadicSquare.halfWidth base =
          2 * DyadicSquare.halfWidth enc by
        exact DyadicSquare.doubled_halfWidth enc]
    nlinarith
  have hsize : 1 < p.size := rep.1.size_gt_one
  have hbase : Hex.nkWitness p base :=
    NKData.witness_of_simple hsize (RefinedIsolation.poly_ne_zero rep)
      hzroot (RefinedIsolation.root_spec rep).2.2.1 hbasePrec hcenter
  obtain ⟨iso, hcert, hiso⟩ := certifyMixed_atom hsize
    (by simpa [base, enc] using hbase)
  have htargetBase : target ≤ (Hex.encSquare c₀.squares).doubled.prec := by
    change target ≤ (Hex.encSquare c₀.squares).prec - 1
    omega
  exact ⟨c₀, iso, by simpa only [final] using hfinal, hcert,
    htargetBase.trans hiso⟩

/-- Sufficient fuel carries a confined one-atom worklist through the globally
reglued prefix and emits its unique target-ready mixed-strategy atom. -/
theorem refineLoop_complete {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) {target prec : Int}
    {work : Array Hex.Component}
    (hprec : Worklist.AtPrec work prec)
    (hwithin : Worklist.Within work rep.1.square.doubled)
    (hcover : RefinedIsolation.root rep ∈ Worklist.region work)
    (hlt : prec < Hex.completenessDepth p target)
    {fuel : Nat}
    (hfuel : (Hex.completenessDepth p target - prec).toNat < fuel) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.refineLoop p target .nkThenPellet fuel work = some #[.atom iso] := by
  induction fuel generalizing prec work with
  | zero => omega
  | succ fuel ih =>
      let tried := Hex.IsolationLoop.attempts p .nkThenPellet work
      have hnormFalse :
          Hex.IsolationLoop.normalized p target tried = false := by
        simpa only [tried] using
          normalized_false_of_root rep hprec hcover hlt
      have hcover₀ := hcover
      obtain ⟨c, hc, hzc⟩ := hcover
      have hempty : work.isEmpty = false :=
        Array.isEmpty_eq_false_iff_exists_mem.mpr
          ⟨c, Array.mem_toList_iff.mp hc⟩
      have hmap : tried.map (·.1) = work := by
        simp [tried, Hex.IsolationLoop.attempts, Function.comp_def]
      have hnext : Hex.IsolationLoop.next p target tried =
          Hex.Component.refineAll p work := by
        simp [Hex.IsolationLoop.next, hnormFalse, hmap]
      have hprec' : Worklist.AtPrec
          (Hex.Component.refineAll p work) (prec + 1) := by
        intro d hd s hs
        exact refineAll_mem_prec hprec hd hs
      have hwithin' : Worklist.Within
          (Hex.Component.refineAll p work) rep.1.square.doubled :=
        Worklist.refineAll_within hwithin
      have hcover' : RefinedIsolation.root rep ∈
          Worklist.region (Hex.Component.refineAll p work) :=
        isRoot_mem_refineAll (RefinedIsolation.isRoot rep) hcover₀
      let emit :=
        Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried &&
            Hex.IsolationLoop.allAtoms tried &&
            (Hex.IsolationLoop.outputs tried).size == 1
      by_cases hemit : emit = true
      · dsimp only [emit] at hemit
        simp only [Bool.and_eq_true] at hemit
        obtain ⟨⟨⟨hready, hdisjoint⟩, hatoms⟩, hsize⟩ := hemit
        obtain ⟨iso, hout⟩ := outputs_single_atom hatoms (by simpa using hsize)
        refine ⟨iso, ?_⟩
        rw [Hex.refineLoop]
        simp [hempty, tried, hready, hdisjoint, hatoms, hout]
      · have hemitFalse : emit = false :=
          Bool.eq_false_of_not_eq_true hemit
        have hemitFalse' :
            (Hex.IsolationLoop.allReady target tried &&
              Hex.IsolationLoop.disjoint tried &&
              Hex.IsolationLoop.allAtoms tried &&
              (Hex.IsolationLoop.outputs tried).size == 1) = false := by
          simpa only [emit] using hemitFalse
        by_cases hlast : Hex.completenessDepth p target ≤ prec + 1
        · have heq : Hex.completenessDepth p target = prec + 1 := by omega
          have hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1 := by
            rw [← heq]
            simp [Hex.completenessDepth]
          have htarget : target + 5 ≤ prec + 1 := by
            rw [← heq]
            simp [Hex.completenessDepth]
          obtain ⟨d, iso, hfinal, hcert, hready⟩ :=
            refineAll_success rep hdepth htarget hprec hwithin hcover₀
          cases fuel with
          | zero =>
              rw [heq] at hfuel
              norm_num at hfuel
          | succ fuel' =>
              have hrec : Hex.refineLoop p target .nkThenPellet
                  (fuel' + 1) (Hex.Component.refineAll p work) =
                  some #[.atom iso] := by
                rw [hfinal, Hex.refineLoop]
                simp [Hex.IsolationLoop.attempts, hcert, hready,
                  Hex.IsolationLoop.allReady, Hex.IsolationLoop.disjoint,
                  Hex.IsolationLoop.allAtoms, Hex.IsolationLoop.outputs,
                  Hex.Certified.square, Hex.pairwiseDisjoint]
              refine ⟨iso, ?_⟩
              rw [Hex.refineLoop]
              simp only [hempty, Bool.false_eq_true, ↓reduceIte]
              rw [show
                (Hex.IsolationLoop.allReady target
                    (Hex.IsolationLoop.attempts p .nkThenPellet work) &&
                  Hex.IsolationLoop.disjoint
                    (Hex.IsolationLoop.attempts p .nkThenPellet work) &&
                  Hex.IsolationLoop.allAtoms
                    (Hex.IsolationLoop.attempts p .nkThenPellet work) &&
                  (Hex.IsolationLoop.outputs
                    (Hex.IsolationLoop.attempts p .nkThenPellet work)).size == 1) =
                    false by simpa only [tried] using hemitFalse']
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [show Hex.IsolationLoop.next p target
                (Hex.IsolationLoop.attempts p .nkThenPellet work) =
                  Hex.Component.refineAll p work by
                    simpa only [tried] using hnext, hrec]
        · have hlt' : prec + 1 < Hex.completenessDepth p target := by omega
          have hfuel' :
              (Hex.completenessDepth p target - (prec + 1)).toNat < fuel := by
            omega
          obtain ⟨iso, hrec⟩ := ih hprec' hwithin' hcover' hlt' hfuel'
          refine ⟨iso, ?_⟩
          rw [Hex.refineLoop]
          simp only [hempty, Bool.false_eq_true, ↓reduceIte]
          rw [show
            (Hex.IsolationLoop.allReady target
                (Hex.IsolationLoop.attempts p .nkThenPellet work) &&
              Hex.IsolationLoop.disjoint
                (Hex.IsolationLoop.attempts p .nkThenPellet work) &&
              Hex.IsolationLoop.allAtoms
                (Hex.IsolationLoop.attempts p .nkThenPellet work) &&
              (Hex.IsolationLoop.outputs
                (Hex.IsolationLoop.attempts p .nkThenPellet work)).size == 1) =
                false by simpa only [tried] using hemitFalse']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [show Hex.IsolationLoop.next p target
            (Hex.IsolationLoop.attempts p .nkThenPellet work) =
              Hex.Component.refineAll p work by
                simpa only [tried] using hnext, hrec]

namespace DyadicRootIsolation

/-- The globally reglued atom-refinement fallback is total for the mixed
strategy. -/
private theorem refineAtom_isSome_mixed {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) (target : Int) :
    (Hex.refineAtom? rep.1 target .nkThenPellet).isSome := by
  rw [Hex.refineAtom?]
  split
  · simp
  · rename_i hnotReady
    let start := rep.1.square.prec - 1
    let work : Array Hex.Component :=
      #[⟨#[rep.1.square.doubled], 1⟩]
    let fuel := Hex.fuelFor p target rep.1.square.prec
    have hprec : Worklist.AtPrec work start := by
      simp [Worklist.AtPrec, work, start]
    have hwithin : Worklist.Within work rep.1.square.doubled := by
      simp [Worklist.Within, work]
    have hcover : RefinedIsolation.root rep ∈ Worklist.region work := by
      refine ⟨⟨#[rep.1.square.doubled], 1⟩, by simp [work], ?_⟩
      refine ⟨rep.1.square.doubled, by simp, ?_⟩
      exact DyadicSquare.closedDisc_subset_doubled rep.1.square
        (RefinedIsolation.root_mem_closedDisc rep)
    have hlt : start < Hex.completenessDepth p target := by
      have htarget : rep.1.square.prec < target := by omega
      simp only [start, Hex.completenessDepth]
      omega
    have hdepthStop : Hex.completenessDepth p target ≤
        Hex.stopDepth p target := by
      simp [Hex.completenessDepth, Hex.stopDepth, Hex.stopSlack]
    have hbudget :
        (Hex.completenessDepth p target - start).toNat < fuel := by
      have hcompNonneg : 0 ≤
          Hex.completenessDepth p target - rep.1.square.prec := by
        dsimp only [start] at hlt
        omega
      have hfirst :
          (Hex.completenessDepth p target - start).toNat =
            (Hex.completenessDepth p target - rep.1.square.prec).toNat + 1 := by
        dsimp only [start]
        omega
      have hle :
          (Hex.completenessDepth p target - rep.1.square.prec).toNat ≤
            (Hex.stopDepth p target - rep.1.square.prec).toNat :=
        Int.toNat_le_toNat (sub_le_sub_right hdepthStop _)
      have htargetStop : target < Hex.stopDepth p target := by
        rw [Hex.stopDepth, Hex.stopSlack]
        have := le_max_left target (Hex.separationDepth p : Int)
        omega
      simp only [fuel, Hex.fuelFor]
      omega
    obtain ⟨iso, hloop⟩ := refineLoop_complete rep
      hprec hwithin hcover hlt hbudget
    simp [fuel, work, hloop]

/-- Raw refinement of an already separation-refined atom is total for the
mixed strategy. The bounded speculative pass may return first; otherwise the
globally reglued NK-complete loop discharges the fallback. Pure Pellet
completeness is deliberately not claimed here. -/
theorem refineTo?_isSome_mixed {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) (target : Int) :
    (rep.1.refineTo? target .nkThenPellet).isSome := by
  rw [Hex.DyadicRootIsolation.refineTo?]
  split
  · simp
  · cases hfast : Hex.refineFastAtom? rep.1 target .nkThenPellet with
    | some iso => simp
    | none =>
        simpa only [hfast] using refineAtom_isSome_mixed rep target

end DyadicRootIsolation

namespace RefinedIsolation

/-- Refined-level refinement is total for the default mixed strategy. -/
theorem refineTo?_isSome_mixed {p : Hex.ZPoly}
    (rep : Hex.RefinedIsolation p) (target : Int) :
    (rep.refineTo? target .nkThenPellet).isSome := by
  have hsome := DyadicRootIsolation.refineTo?_isSome_mixed rep
    (max target (Hex.mahlerPrec p : Int))
  cases hraw : rep.1.refineTo? (max target (Hex.mahlerPrec p : Int))
      .nkThenPellet with
  | none => simp [hraw] at hsome
  | some iso =>
      have hready := DyadicRootIsolation.refineTo_ready hraw
      have hprec : (Hex.mahlerPrec p : Int) ≤ iso.square.prec :=
        (le_max_right target (Hex.mahlerPrec p : Int)).trans hready
      let out : Hex.RefinedIsolation p := ⟨iso, hprec⟩
      have hroot : RefinedIsolation.root out = RefinedIsolation.root rep := by
        exact DyadicRootIsolation.refineTo_root rep.1
          (max target (Hex.mahlerPrec p : Int)) .nkThenPellet hraw
      have hinter : Hex.Intersects out rep :=
        (RefinedIsolation.intersects_iff_root_eq out rep).mpr hroot
      rw [Hex.RefinedIsolation.refineTo?]
      simp only [hraw, Option.bind_eq_bind, Option.bind_some]
      split
      · rename_i hprec'
        simp
      · rename_i hnot
        exact (hnot hprec).elim

end RefinedIsolation

end

end HexRootsMathlib
