/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.SurvivorComponent
public import HexRootsMathlib.Loop

public section

/-!
# Completeness of globally normalized isolation

This module carries root coverage and a common leaf precision through the
globally glued subdivision rounds used below `Hex.completenessDepth`.  The
resulting maximal components are genuinely root-bearing, closing the
rootless-halo gap left by root-wise coverage alone.
-/

namespace HexRootsMathlib

noncomputable section

namespace Worklist

/-- All squares stored by a component worklist. -/
@[expose] def squares (work : Array Hex.Component) : Array Hex.DyadicSquare :=
  work.flatMap (·.squares)

/-- Every worklist square has the same leaf precision. -/
@[expose] def AtPrec (work : Array Hex.Component) (prec : Int) : Prop :=
  ∀ c ∈ work.toList, ∀ s ∈ c.squares.toList, s.prec = prec

/-- Every polynomial root lies in a worklist square. -/
@[expose] def Covers (p : Hex.ZPoly) (work : Array Hex.Component) : Prop :=
  CoversRoots p (squares work)

end Worklist

@[simp] private theorem encSquare_singleton (s : Hex.DyadicSquare) :
    Hex.encSquare #[s] = s := by
  cases s with
  | mk re im prec =>
      rw [Hex.encSquare, Hex.boundingBox, ← Array.foldl_toList]
      simp only [List.foldl_cons, List.foldl_nil,
        Hex.SquareBounds.extend, Hex.DyadicSquare.bounds,
        Hex.DyadicSquare.halfWidth]
      congr 1
      · apply Dyadic.toReal_injective
        simp [Dyadic.toReal_shiftRight]
        ring
      · apply Dyadic.toReal_injective
        simp [Dyadic.toReal_shiftRight]
        ring
      · have hw : Hex.Dyadic.max
            ((re + Dyadic.ofIntWithPrec 1 prec -
                (re - Dyadic.ofIntWithPrec 1 prec)) >>> (1 : Int))
            ((im + Dyadic.ofIntWithPrec 1 prec -
                (im - Dyadic.ofIntWithPrec 1 prec)) >>> (1 : Int)) =
            Dyadic.ofIntWithPrec 1 prec := by
          apply Dyadic.toReal_injective
          simp [Dyadic.toReal_shiftRight]
          ring
        rw [hw]
        have ht : Int.trailingZeros (1 : Int) = 0 :=
          Int.trailingZeros_eq_zero_of_mod_eq (by norm_num)
        simp [Dyadic.ofIntWithPrec, ht, Hex.Dyadic.ceilLog2, Hex.ceilLog2]

private theorem discInside_prec {inner outer : Hex.DyadicSquare}
    (h : inner.discInside outer = true) : outer.prec ≤ inner.prec := by
  have hdata : outer.prec ≤ inner.prec ∧
      Hex.GaussDyadic.distSq inner.center outer.center ≤
        (2 : _root_.Dyadic) * .ofIntWithPrec 1 (2 * outer.prec) +
          2 * .ofIntWithPrec 1 (2 * inner.prec) -
          4 * .ofIntWithPrec 1 (outer.prec + inner.prec) := by
    simpa [Hex.DyadicSquare.discInside] using of_decide_eq_true h
  exact hdata.1

/-- A checked `k = 1` Pellet base makes the first individual attempt return
an atom, and speculative recentring cannot reduce its stored precision. -/
private theorem certifyPelletAt_one {p : Hex.ZPoly} {c : Hex.Component}
    (hbase : Hex.witness p (Hex.encSquare c.squares) 1) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.Component.certifyPelletAt? p c 1 = some (.atom iso) ∧
        (Hex.encSquare c.squares).prec ≤ iso.square.prec := by
  simp only [Hex.witness] at hbase
  simp only [Hex.Component.certifyPelletAt?, Nat.zero_lt_one, ↓reduceDIte, hbase]
  split <;> rename_i hins
  · split <;> rename_i hcand
    · refine ⟨_, rfl, ?_⟩
      exact discInside_prec hins
    · exact ⟨_, rfl, le_rfl⟩
  · exact ⟨_, rfl, le_rfl⟩

private theorem newtonCandidate_prec {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hsize : 1 < p.size) :
    s.prec ≤ (Hex.newtonSquare p s 1).doubled.prec := by
  simp [Hex.newtonSquare, Hex.taylor_size, show ¬p.size < 2 by omega]

/-- A checked NK base makes the NK-only prefix return an atom without losing
stored precision. -/
private theorem certifyNK_one {p : Hex.ZPoly} {c : Hex.Component}
    (hsize : 1 < p.size)
    (hbase : Hex.nkWitness p (Hex.encSquare c.squares).doubled) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.Component.certify? p .nk c = some (.atom iso) ∧
        (Hex.encSquare c.squares).doubled.prec ≤ iso.square.prec := by
  simp only [Hex.Component.certify?, Hex.nkWitness] at hbase ⊢
  split <;> rename_i hbase'
  · split <;> rename_i hins
    · split <;> rename_i hcand
      · refine ⟨⟨_, Or.inl hcand⟩, rfl, ?_⟩
        exact newtonCandidate_prec hsize
      · exact ⟨⟨_, Or.inl hbase'⟩, rfl, le_rfl⟩
    · exact ⟨⟨_, Or.inl hbase'⟩, rfl, le_rfl⟩
  · exact (hbase' hbase).elim

/-- The mixed strategy has the identical successful NK prefix. -/
private theorem certifyMixed_one {p : Hex.ZPoly} {c : Hex.Component}
    (hsize : 1 < p.size)
    (hbase : Hex.nkWitness p (Hex.encSquare c.squares).doubled) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.Component.certify? p .nkThenPellet c = some (.atom iso) ∧
        (Hex.encSquare c.squares).doubled.prec ≤ iso.square.prec := by
  simp only [Hex.Component.certify?, Hex.nkWitness] at hbase ⊢
  split <;> rename_i hbase'
  · split <;> rename_i hins
    · split <;> rename_i hcand
      · refine ⟨⟨_, Or.inl hcand⟩, rfl, ?_⟩
        exact newtonCandidate_prec hsize
      · exact ⟨⟨_, Or.inl hbase'⟩, rfl, le_rfl⟩
    · exact ⟨⟨_, Or.inl hbase'⟩, rfl, le_rfl⟩
  · exact (hbase' hbase).elim

/-- A member of a globally normalized round is one level finer than every
input square. -/
theorem refineAll_mem_prec {p : Hex.ZPoly} {work : Array Hex.Component}
    {prec : Int} (hprec : Worklist.AtPrec work prec)
    {c : Hex.Component} (hc : c ∈ (Hex.Component.refineAll p work).toList)
    {s : Hex.DyadicSquare} (hs : s ∈ c.squares.toList) :
    s.prec = prec + 1 := by
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  rw [Hex.Component.refineAll] at hc
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  simp only [Array.toList_map, List.mem_map] at hc
  obtain ⟨ss, hss, rfl⟩ := hc
  have hsurv : s ∈ survivors.toList := mem_of_mem_glueCovered hss hs
  have hchild : s ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList := by
    have hsurv' : s ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p s = false := by simpa [survivors] using hsurv
    exact hsurv'.1
  rw [Array.toList_flatMap, List.mem_flatMap] at hchild
  obtain ⟨u, hu, hsu⟩ := hchild
  change u ∈ (Worklist.squares work).toList at hu
  rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hu
  obtain ⟨d, hd, hud⟩ := hu
  have huprec := hprec d hd u hud
  simp [Hex.DyadicSquare.subdivide] at hsu
  rcases hsu with rfl | rfl | rfl | rfl <;> simp [huprec]

/-- Global subdivision preserves coverage of every complex root. -/
theorem refineAll_covers {p : Hex.ZPoly} {work : Array Hex.Component}
    (hcover : Worklist.Covers p work) :
    Worklist.Covers p (Hex.Component.refineAll p work) := by
  intro z hzroot
  obtain ⟨s, hs, hzs⟩ := hcover z hzroot
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  obtain ⟨t, ht, hzt⟩ := isRoot_mem_survivors hzroot hs hzs
  change t ∈ survivors.toList at ht
  obtain ⟨ss, hss, htss⟩ := mem_glueCovered ht
  refine ⟨t, ?_, hzt⟩
  rw [Worklist.squares, Hex.Component.refineAll,
    Array.toList_flatMap, List.mem_flatMap]
  let d : Hex.Component := { squares := ss, candidateK := 1 }
  refine ⟨d, ?_, htss⟩
  simp only [Array.toList_map, List.mem_map]
  exact ⟨ss, hss, rfl⟩

/-- A normalized round never duplicates an outer component. -/
theorem refineAll_nodup (p : Hex.ZPoly) (work : Array Hex.Component) :
    (Hex.Component.refineAll p work).toList.Nodup := by
  rw [Hex.Component.refineAll]
  rw [Array.toList_map]
  apply (glueCovered_nodup _).map
  intro a b h
  exact congrArg Hex.Component.squares h

/-- Distinct normalized components cannot designate the same root: squares
containing that root would be adjacent and hence glued together. -/
theorem refineAll_roots_ne {p : Hex.ZPoly} {work : Array Hex.Component}
    {prec : Int} (hprec : Worklist.AtPrec work prec)
    {c d : Hex.Component}
    (hc : c ∈ (Hex.Component.refineAll p work).toList)
    (hd : d ∈ (Hex.Component.refineAll p work).toList) (hcd : c ≠ d)
    {z w : ℂ} (hzc : z ∈ Component.region c)
    (hwd : w ∈ Component.region d) : z ≠ w := by
  obtain ⟨s, hs, hzs⟩ := hzc
  obtain ⟨t, ht, hwt⟩ := hwd
  have hsPrec := refineAll_mem_prec hprec hc hs
  have htPrec := refineAll_mem_prec hprec hd ht
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  rw [Hex.Component.refineAll] at hc hd
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  change d ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hd
  simp only [Array.toList_map, List.mem_map] at hc hd
  obtain ⟨component, hcomponent, rfl⟩ := hc
  obtain ⟨other, hother, rfl⟩ := hd
  have hcomponents : component ≠ other := by
    intro h
    subst other
    exact hcd rfl
  intro hzw
  subst w
  have hwidth : DyadicSquare.halfWidth t = DyadicSquare.halfWidth s := by
    rw [DyadicSquare.halfWidth_eq, DyadicSquare.halfWidth_eq, hsPrec, htPrec]
  have hzs' : supDist (DyadicSquare.center s) z ≤
      DyadicSquare.halfWidth s := by
    change supNorm (DyadicSquare.center s - z) ≤ DyadicSquare.halfWidth s
    change supNorm (z - DyadicSquare.center s) ≤ DyadicSquare.halfWidth s at hzs
    simpa [supNorm, abs_sub_comm] using hzs
  have hzt : supDist z (DyadicSquare.center t) ≤
      DyadicSquare.halfWidth t := hwt
  have htri : supDist (DyadicSquare.center s) (DyadicSquare.center t) ≤
      supDist (DyadicSquare.center s) z +
        supDist z (DyadicSquare.center t) := by
    unfold supDist
    calc
      supNorm (DyadicSquare.center s - DyadicSquare.center t) =
          supNorm ((DyadicSquare.center s - z) +
            (z - DyadicSquare.center t)) := by ring_nf
      _ ≤ _ := supNorm_add_le _ _
  have hwidthPos : 0 < DyadicSquare.halfWidth s := by
    rw [DyadicSquare.halfWidth_eq]
    positivity
  have hdist : supDist (DyadicSquare.center s) (DyadicSquare.center t) <
      4 * DyadicSquare.halfWidth s := by
    rw [hwidth] at hzt
    nlinarith
  have hedge : Glue.Edge s t :=
    DyadicSquare.adjacent_of_supDist_lt (hsPrec.trans htPrec.symm) hdist
  exact (glueCovered_separated survivors component hcomponent other hother
    hcomponents s hs t ht).1 hedge

/-- Every output component of a globally normalized separation-depth round
actually contains one polynomial root. -/
theorem refineAll_component_root {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    {c : Hex.Component} (hc : c ∈ (Hex.Component.refineAll p work).toList) :
    ∃ z, (toPolyℂ p).IsRoot z ∧ z ∈ Component.region c := by
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  rw [Hex.Component.refineAll] at hc
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  simp only [Array.toList_map, List.mem_map] at hc
  obtain ⟨component, hcomponent, rfl⟩ := hc
  have hsurvCover : CoversRoots p survivors := by
    intro z hzroot
    obtain ⟨s, hs, hzs⟩ := hcover z hzroot
    exact isRoot_mem_survivors hzroot hs hzs
  apply exists_root_mem_glueCovered (squares := survivors)
    (prec := prec + 1) hp hsize hsep hdepth
  · intro u hu
    have hu' : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p u = false := by simpa [survivors] using hu
    have hchild : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList := hu'.1
    rw [Array.toList_flatMap, List.mem_flatMap] at hchild
    obtain ⟨s, hs, hus⟩ := hchild
    change s ∈ (Worklist.squares work).toList at hs
    rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hs
    obtain ⟨d, hd, hsd⟩ := hs
    have hsprec := hprec d hd s hsd
    simp [Hex.DyadicSquare.subdivide] at hus
    rcases hus with rfl | rfl | rfl | rfl <;> simp [hsprec]
  · intro u hu hfree
    have hu' : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p u = false := by simpa [survivors] using hu
    rw [hfree] at hu'
    cases hu'.2
  · exact hsurvCover
  · exact hcomponent

/-- A root-bearing maximal survivor component has enough uniform recentring
margin on its quadrupled enclosing square for the executable Pellet witness.
Five leaf levels pay for the enclosing-square loss and quadrupling while the
implemented separation slack controls the remote-root tail. -/
theorem witness_quadrupled_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {prec : Int} {z : ℂ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hzroot : (toPolyℂ p).IsRoot z)
    (hzcomponent : z ∈ Component.region ⟨component, 1⟩) :
    Hex.witness p (Hex.encSquare component).doubled.doubled 1 := by
  let f := toPolyℂ p
  let enc := Hex.encSquare component
  let wide := enc.doubled.doubled
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  let N := Nat.max 2 (p.degree?.getD 0)
  let d := 3 * M
  have hM : 0 < M := by dsimp [M]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
  have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
  have hwidePrec : (Hex.separationDepth p : Int) ≤ wide.prec := by
    have hwidePrecEq : wide.prec = enc.prec - 2 := by
      simp [wide]
      omega
    rw [hwidePrecEq]
    dsimp [enc]
    omega
  have hzenc : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare ⟨component, 1⟩ hzcomponent
  have hzsup : supNorm (z - DyadicSquare.center enc) ≤
      DyadicSquare.halfWidth enc := by
    simpa [DyadicSquare.closedSquare, supClosedBall, supDist] using hzenc
  have hznorm : ‖z - DyadicSquare.center enc‖ ≤
      √2 * DyadicSquare.halfWidth enc := by
    exact (Complex.norm_le_sqrt_two_mul_max _).trans
      (mul_le_mul_of_nonneg_left hzsup (Real.sqrt_nonneg _))
  have hcenter : DyadicSquare.center wide = DyadicSquare.center enc := rfl
  have hwideWidth : DyadicSquare.halfWidth wide =
      4 * DyadicSquare.halfWidth enc := by
    dsimp [wide]
    rw [DyadicSquare.doubled_halfWidth, DyadicSquare.doubled_halfWidth]
    ring
  have hRhi : 0 < Dyadic.toReal wide.radiusHi := by
    rw [DyadicSquare.radiusHi_eq]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity)
      (by norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec])
  have ha : ‖z - DyadicSquare.center wide‖ <
      Dyadic.toReal wide.radiusHi / 4 := by
    rw [hcenter, DyadicSquare.radiusHi_eq, hwideWidth]
    have hsqrt := sqrt_two_lt_sqrt2Hi
    have hwidth : 0 < DyadicSquare.halfWidth enc := by
      rw [DyadicSquare.halfWidth_eq]
      positivity
    nlinarith
  obtain ⟨roots, hroots⟩ := Multiset.exists_cons_of_mem
    ((Polynomial.mem_roots hp).2 hzroot)
  have hrootsEq : f.roots = z ::ₘ roots := by simpa [f] using hroots
  have hsepC : f.Separable := by
    have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [show f = (HexPolyZMathlib.toPolyℚ p).map (algebraMap ℚ ℂ) by
      dsimp [f, HexPolyZMathlib.toPolyℚ]
      rw [Polynomial.map_map, hcomp]]
    exact hsep.map
  have hnodup : f.roots.Nodup := Polynomial.nodup_roots hsepC
  have hne : ∀ w ∈ roots, w ≠ z := by
    intro w hw heq
    subst w
    rw [hrootsEq] at hnodup
    exact (Multiset.nodup_cons.mp hnodup).1 hw
  have hremote : ∀ w ∈ roots, d ≤ ‖w - DyadicSquare.center wide‖ := by
    intro w hw
    have hwroot : f.IsRoot w := (Polynomial.mem_roots hp).1 (by
      rw [hrootsEq]
      exact Multiset.mem_cons_of_mem hw)
    have hsepzw := mahlerPrec_separates p hsep z w hzroot hwroot (hne w hw).symm
    have htri : ‖z - w‖ ≤ ‖z - DyadicSquare.center wide‖ +
        ‖w - DyadicSquare.center wide‖ := by
      calc
        ‖z - w‖ = ‖(z - DyadicSquare.center wide) -
            (w - DyadicSquare.center wide)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have hRsmall := NKData.radiusHi_mul_degree_le hwidePrec
    have htwo : (2 : ℝ) ≤ N := by exact_mod_cast Nat.le_max_left 2 _
    have hRi : Dyadic.toReal wide.radiusHi ≤ M / 512 := by
      have hRnonneg := hRhi.le
      have : 2 * Dyadic.toReal wide.radiusHi ≤ M / 256 := by
        calc
          _ = Dyadic.toReal wide.radiusHi * 2 := by ring
          _ ≤ Dyadic.toReal wide.radiusHi * (N : ℝ) :=
            mul_le_mul_of_nonneg_left htwo hRnonneg
          _ ≤ M / 256 := by simpa [N, M] using hRsmall
      nlinarith
    change M < ‖z - w‖ / 4 at hsepzw
    change 3 * M ≤ ‖w - DyadicSquare.center wide‖
    nlinarith
  have hcard : roots.card ≤ N := by
    have hdegree : roots.card + 1 = p.degree?.getD 0 := by
      calc
        roots.card + 1 = f.roots.card := by rw [hrootsEq]; simp
        _ = f.natDegree := (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
        _ = p.degree?.getD 0 := by simpa [f] using natDegree_toPolyℂ p
    exact (by omega : roots.card ≤ p.degree?.getD 0).trans (Nat.le_max_right _ _)
  apply witness_one_of_roots hp hsize hrootsEq hd hremote
  intro j hj
  let L := (2 : ℝ) ^ (j : Int)
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hLone : 1 ≤ L := by
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [L]
  have hLfour : L ≤ 4 := by
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [L]
  let rlo := Dyadic.toReal (wide.radiusLo <<< (j : Int))
  let rhi := Dyadic.toReal (wide.radiusHi <<< (j : Int))
  have hrhi : rhi = Dyadic.toReal wide.radiusHi * L := by
    simp [rhi, L, Dyadic.toReal_shiftLeft]
  have hrlo : rlo = (1448 / 1449 : ℝ) * rhi := by
    dsimp [rlo, rhi]
    rw [Dyadic.toReal_shiftLeft, Dyadic.toReal_shiftLeft,
      DyadicSquare.radiusLo_eq, DyadicSquare.radiusHi_eq]
    norm_num [Hex.sqrt2Lo, Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    ring
  have hRN := NKData.radiusHi_mul_degree_le hwidePrec
  have hcardReal : (roots.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hrootRN : Dyadic.toReal wide.radiusHi * (roots.card : ℝ) ≤ M / 256 :=
    (mul_le_mul_of_nonneg_left hcardReal hRhi.le).trans (by simpa [N, M] using hRN)
  have hsmall : (roots.card : ℝ) * (rhi / d) ≤ 1 / 192 := by
    rw [show (roots.card : ℝ) * (rhi / d) =
      (rhi * roots.card) / (3 * M) by dsimp [d]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 3 * M)).2
    rw [hrhi]
    nlinarith
  have hrhiPos : 0 < rhi := by rw [hrhi]; positivity
  have hxnonneg : 0 ≤ rhi / d := by positivity
  have hpow := NKData.one_add_pow_le hxnonneg
    roots.card (hsmall.trans (by norm_num))
  have htail : (1 + rhi / d) ^ roots.card - 1 ≤ 1 / 96 := by
    nlinarith
  have htailNonneg : 0 ≤ (1 + rhi / d) ^ roots.card - 1 := by
    have hone : 1 ≤ (1 + rhi / d) ^ roots.card := by
      apply one_le_pow₀
      nlinarith
    linarith
  rw [show Dyadic.toReal (wide.radiusLo <<< (j : Int)) = rlo by rfl,
    show Dyadic.toReal (wide.radiusHi <<< (j : Int)) = rhi by rfl,
    hrlo]
  have harhi : ‖z - DyadicSquare.center wide‖ ≤ rhi / 4 := by
    rw [hrhi]
    nlinarith
  have hcoef : 2 * rhi + 5 * ‖z - DyadicSquare.center wide‖ ≤
      (13 / 4 : ℝ) * rhi := by nlinarith
  have hprod :
      (2 * rhi + 5 * ‖z - DyadicSquare.center wide‖) *
          ((1 + rhi / d) ^ roots.card - 1) ≤
        ((13 / 4 : ℝ) * rhi) * (1 / 96) := by
    exact mul_le_mul hcoef htail htailNonneg (by positivity)
  change ‖z - GaussDyadic.toComplex wide.center‖ ≤ rhi / 4 at harhi
  change (2 * rhi + 5 * ‖z - GaussDyadic.toComplex wide.center‖) *
      ((1 + rhi / d) ^ roots.card - 1) ≤
    ((13 / 4 : ℝ) * rhi) * (1 / 96) at hprod
  nlinarith

/-- At the globally normalized completeness depth, the Pellet-only strategy's
first candidate is the root-bearing `k = 1` witness.  It therefore returns a
target-ready atom, whether or not the guarded speculative step is adopted. -/
theorem certify_pellet_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {prec target : Int} {z : ℂ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec)
    (htarget : target + 5 ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hzroot : (toPolyℂ p).IsRoot z)
    (hzcomponent : z ∈ Component.region ⟨component, 1⟩) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.Component.certify? p .pellet ⟨component, 1⟩ = some (.atom iso) ∧
        target ≤ iso.square.prec ∧ z ∈ Certified.region (.atom iso) := by
  let enc := Hex.encSquare component
  let wide := enc.doubled.doubled
  let wc : Hex.Component := ⟨#[wide], 1⟩
  have hwitness : Hex.witness p wide 1 := by
    simpa [enc, wide] using witness_quadrupled_of_glueCovered hp hsize hsep
      hdepth hprec hkeep hc hzroot hzcomponent
  have hwitness' : Hex.witness p (Hex.encSquare wc.squares) 1 := by
    simpa [wc] using hwitness
  obtain ⟨iso, hat, hisoPrec⟩ := certifyPelletAt_one hwitness'
  have hsearch : Hex.Component.certifyPellet? p wc = some (.atom iso) := by
    unfold Hex.Component.certifyPellet?
    simp [wc, Hex.Component.certifyPelletList?, hat]
  have hcert : Hex.Component.certify? p .pellet ⟨component, 1⟩ =
      some (.atom iso) := by
    simpa [Hex.Component.certify?, enc, wide, wc] using hsearch
  have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
  have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
  have hwideTarget : target ≤ wide.prec := by
    have hwidePrec : wide.prec = enc.prec - 2 := by
      simp [wide]
      omega
    rw [hwidePrec]
    dsimp [enc]
    omega
  have hisoTarget : target ≤ iso.square.prec := by
    apply hwideTarget.trans
    simpa [wc] using hisoPrec
  exact ⟨iso, hcert, hisoTarget,
    certifier_preserves_pellet p _ _ hcert z hzroot hzcomponent⟩

private theorem nkWitness_doubled_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {prec : Int} {z : ℂ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 3 ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hzroot : (toPolyℂ p).IsRoot z)
    (hzcomponent : z ∈ Component.region ⟨component, 1⟩) :
    Hex.nkWitness p (Hex.encSquare component).doubled := by
  let enc := Hex.encSquare component
  let base := enc.doubled
  have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
  have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
  have hbasePrec : (Hex.separationDepth p : Int) ≤ base.prec := by
    change (Hex.separationDepth p : Int) ≤ (Hex.encSquare component).prec - 1
    omega
  have hzenc : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare ⟨component, 1⟩ hzcomponent
  have hzsup : supNorm (z - DyadicSquare.center enc) ≤
      DyadicSquare.halfWidth enc := by
    simpa [DyadicSquare.closedSquare, supClosedBall, supDist] using hzenc
  have hcenter : supNorm (z - DyadicSquare.center base) ≤
      DyadicSquare.halfWidth base / 2 := by
    rw [show DyadicSquare.center base = DyadicSquare.center enc by rfl,
      show DyadicSquare.halfWidth base = 2 * DyadicSquare.halfWidth enc by
        exact DyadicSquare.doubled_halfWidth enc]
    nlinarith
  exact NKData.witness_at_separationDepth hsize hsep hzroot hbasePrec hcenter

/-- Every root-bearing maximal component at the normalized depth certifies as
a target-ready atom for each of the three executable atom strategies. -/
theorem certify_atom_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare} {prec target : Int} {z : ℂ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec)
    (htarget : target + 5 ≤ prec)
    (hprec : ∀ u ∈ squares.toList, u.prec = prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList)
    (hzroot : (toPolyℂ p).IsRoot z)
    (hzcomponent : z ∈ Component.region ⟨component, 1⟩)
    (strategy : Hex.AtomStrategy) :
    ∃ iso : Hex.DyadicRootIsolation p,
      Hex.Component.certify? p strategy ⟨component, 1⟩ = some (.atom iso) ∧
        target ≤ iso.square.prec ∧ z ∈ Certified.region (.atom iso) := by
  cases strategy with
  | pellet =>
      exact certify_pellet_of_glueCovered hp hsize hsep hdepth htarget hprec
        hkeep hc hzroot hzcomponent
  | nk =>
      have hbase : Hex.nkWitness p (Hex.encSquare component).doubled :=
        nkWitness_doubled_of_glueCovered hp hsize hsep
          (by omega) hprec hkeep hc hzroot hzcomponent
      obtain ⟨iso, hcert, hiso⟩ := certifyNK_one
        (c := (⟨component, 1⟩ : Hex.Component)) hsize hbase
      have htargetBase : target ≤ (Hex.encSquare component).doubled.prec := by
        have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
        have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
        change target ≤ (Hex.encSquare component).prec - 1
        omega
      exact ⟨iso, hcert, htargetBase.trans hiso,
        certifier_preserves_nk p _ _ hcert z hzroot hzcomponent⟩
  | nkThenPellet =>
      have hbase : Hex.nkWitness p (Hex.encSquare component).doubled :=
        nkWitness_doubled_of_glueCovered hp hsize hsep
          (by omega) hprec hkeep hc hzroot hzcomponent
      obtain ⟨iso, hcert, hiso⟩ := certifyMixed_one
        (c := (⟨component, 1⟩ : Hex.Component)) hsize hbase
      have htargetBase : target ≤ (Hex.encSquare component).doubled.prec := by
        have hleaf : (Hex.separationDepth p : Int) ≤ prec := by omega
        have henc := encSquare_prec_of_glueCovered hp hsize hsep hleaf hprec hkeep hc
        change target ≤ (Hex.encSquare component).prec - 1
        omega
      exact ⟨iso, hcert, htargetBase.trans hiso,
        certifier_preserves_nkThenPellet p _ _ hcert z hzroot hzcomponent⟩

/-- Every component produced by the last normalized round has a designated
root and succeeds as a target-ready atom under the selected strategy. -/
theorem refineAll_component_certifies {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy)
    {c : Hex.Component} (hc : c ∈ (Hex.Component.refineAll p work).toList) :
    ∃ z iso, (toPolyℂ p).IsRoot z ∧ z ∈ Component.region c ∧
      Hex.Component.certify? p strategy c = some (.atom iso) ∧
        target ≤ iso.square.prec ∧ z ∈ Certified.region (.atom iso) := by
  obtain ⟨z, hzroot, hzc⟩ := refineAll_component_root hp hsize hsep
    (by omega) hprec hcover hc
  let squares := Worklist.squares work
  let survivors := (squares.flatMap Hex.DyadicSquare.subdivide).filter
    (fun u => !Hex.rootFree p u)
  rw [Hex.Component.refineAll] at hc
  change c ∈ ((Hex.glueCovered survivors).map fun ss =>
    { squares := ss, candidateK := 1 }).toList at hc
  simp only [Array.toList_map, List.mem_map] at hc
  obtain ⟨component, hcomponent, rfl⟩ := hc
  have hsurvPrec : ∀ u ∈ survivors.toList, u.prec = prec + 1 := by
    intro u hu
    have hu' : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p u = false := by simpa [survivors] using hu
    rw [Array.toList_flatMap, List.mem_flatMap] at hu'
    obtain ⟨s, hs, hus⟩ := hu'.1
    change s ∈ (Worklist.squares work).toList at hs
    rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hs
    obtain ⟨d, hd, hsd⟩ := hs
    have hsprec := hprec d hd s hsd
    simp [Hex.DyadicSquare.subdivide] at hus
    rcases hus with rfl | rfl | rfl | rfl <;> simp [hsprec]
  have hsurvKeep : ∀ u ∈ survivors.toList, Hex.rootFree p u ≠ true := by
    intro u hu hfree
    have hu' : u ∈ (squares.flatMap Hex.DyadicSquare.subdivide).toList ∧
        Hex.rootFree p u = false := by simpa [survivors] using hu
    rw [hfree] at hu'
    cases hu'.2
  obtain ⟨iso, hcert, hiso, hziso⟩ := certify_atom_of_glueCovered hp hsize hsep
    hdepth htarget hsurvPrec hsurvKeep hcomponent hzroot hzc strategy
  exact ⟨z, iso, hzroot, hzc, hcert, hiso, hziso⟩

private theorem radius_lt_mahler_div {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec) :
    DyadicSquare.radius s <
      ((2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)) / 512 := by
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  let N := Nat.max 2 (p.degree?.getD 0)
  have hRN := NKData.radiusHi_mul_degree_le hprec
  have hRpos : 0 < Dyadic.toReal s.radiusHi := by
    rw [DyadicSquare.radiusHi_eq]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity)
      (by norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec])
  have htwo : (2 : ℝ) ≤ N := by exact_mod_cast Nat.le_max_left 2 _
  have hRi : Dyadic.toReal s.radiusHi ≤ M / 512 := by
    have : 2 * Dyadic.toReal s.radiusHi ≤ M / 256 := by
      calc
        _ = Dyadic.toReal s.radiusHi * 2 := by ring
        _ ≤ Dyadic.toReal s.radiusHi * (N : ℝ) :=
          mul_le_mul_of_nonneg_left htwo hRpos.le
        _ ≤ M / 256 := by simpa [N, M] using hRN
    nlinarith
  exact (DyadicSquare.radius_lt_radiusHi s).trans_le (by simpa [M] using hRi)

private theorem atomRegion_subset_disc {p : Hex.ZPoly}
    (iso : Hex.DyadicRootIsolation p) :
    Certified.region (.atom iso) ⊆ DyadicSquare.closedDisc iso.square := by
  rw [Certified.region, DyadicRootIsolation.region]
  split
  · exact DyadicSquare.closedSquare_subset_closedDisc iso.square
  · exact fun _ h => h

/-- Certificates of two distinct final normalized components have a negative
executable disc-intersection test. -/
theorem refineAll_certificates_disjoint {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hsepTarget : (Hex.separationDepth p : Int) ≤ target)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy)
    {c d : Hex.Component}
    (hc : c ∈ (Hex.Component.refineAll p work).toList)
    (hd : d ∈ (Hex.Component.refineAll p work).toList) (hcd : c ≠ d)
    {r q : Hex.Certified p}
    (hr : Hex.Component.certify? p strategy c = some r)
    (hq : Hex.Component.certify? p strategy d = some q) :
    r.square.discsMeet q.square = false := by
  obtain ⟨z, iso, hzroot, hzc, hciso, hisoPrec, hziso⟩ :=
    refineAll_component_certifies hp hsize hsep hdepth htarget hprec hcover
      strategy hc
  obtain ⟨w, tau, hwroot, hwd, hdtau, htauPrec, hwtau⟩ :=
    refineAll_component_certifies hp hsize hsep hdepth htarget hprec hcover
      strategy hd
  have hrEq : r = .atom iso := Option.some.inj (hr.symm.trans hciso)
  have hqEq : q = .atom tau := Option.some.inj (hq.symm.trans hdtau)
  subst r
  subst q
  have hzw : z ≠ w := refineAll_roots_ne hprec hc hd hcd hzc hwd
  have hrSmall := radius_lt_mahler_div (hsepTarget.trans hisoPrec)
  have hqSmall := radius_lt_mahler_div (hsepTarget.trans htauPrec)
  have hzdisc : z ∈ DyadicSquare.closedDisc iso.square :=
    atomRegion_subset_disc iso hziso
  have hwdisc : w ∈ DyadicSquare.closedDisc tau.square :=
    atomRegion_subset_disc tau hwtau
  have hfalse : iso.square.discsMeet tau.square = false := by
    cases hmeet : iso.square.discsMeet tau.square with
    | false => rfl
    | true =>
      exfalso
      have hcenters := DyadicSquare.dist_center_le_of_discsMeet hmeet
      have hzcenter : ‖z - DyadicSquare.center iso.square‖ ≤
          DyadicSquare.radius iso.square := by
        simpa [DyadicSquare.closedDisc, Metric.mem_closedBall, Complex.dist_eq] using hzdisc
      have hwcenter : ‖DyadicSquare.center tau.square - w‖ ≤
          DyadicSquare.radius tau.square := by
        have := hwdisc
        rw [DyadicSquare.closedDisc, Metric.mem_closedBall, Complex.dist_eq] at this
        simpa [norm_sub_rev] using this
      have hcenterNorm : ‖DyadicSquare.center iso.square -
          DyadicSquare.center tau.square‖ ≤
          DyadicSquare.radius iso.square + DyadicSquare.radius tau.square := by
        simpa [Complex.dist_eq] using hcenters
      have hrootUpper : ‖z - w‖ ≤
          2 * (DyadicSquare.radius iso.square + DyadicSquare.radius tau.square) := by
        calc
          ‖z - w‖ = ‖(z - DyadicSquare.center iso.square) +
              (DyadicSquare.center iso.square - DyadicSquare.center tau.square) +
              (DyadicSquare.center tau.square - w)‖ := by ring_nf
          _ ≤ ‖z - DyadicSquare.center iso.square‖ +
              ‖DyadicSquare.center iso.square - DyadicSquare.center tau.square‖ +
              ‖DyadicSquare.center tau.square - w‖ := by
            apply (norm_add_le _ _).trans
            gcongr
            exact norm_add_le _ _
          _ ≤ _ := by nlinarith
      have hsepzw := mahlerPrec_separates p hsep z w hzroot hwroot hzw
      change (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ) <
          ‖z - w‖ / 4 at hsepzw
      have hMpos : 0 < (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) *
          (1449 / 1024 : ℝ) := by positivity
      nlinarith
  simpa only [Hex.Certified.square] using hfalse

private theorem pairwiseDisjoint_of_pairwise {ss : Array Hex.DyadicSquare}
    (h : ss.toList.Pairwise fun s t => s.discsMeet t = false) :
    Hex.pairwiseDisjoint ss = true := by
  rw [Hex.pairwiseDisjoint, List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  by_cases hij : i < j
  · simp only [hij, ↓reduceIte]
    have hiSize : i < ss.size := List.mem_range.mp hi
    have hjSize : j < ss.size := List.mem_range.mp hj
    have hrel := List.pairwise_iff_getElem.mp h i j
      (by simpa using hiSize) (by simpa using hjSize) hij
    have hgeti : ss.getD i ⟨0, 0, 0⟩ = ss[i] :=
      (Array.getElem_eq_getD (Hex.DyadicSquare.mk 0 0 0)).symm
    have hgetj : ss.getD j ⟨0, 0, 0⟩ = ss[j] :=
      (Array.getElem_eq_getD (Hex.DyadicSquare.mk 0 0 0)).symm
    rw [hgeti, hgetj]
    simpa using hrel
  · simp [hij]

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

private theorem exists_covered_component {p : Hex.ZPoly}
    (hsize : 1 < p.size) {work : Array Hex.Component}
    (hcover : Worklist.Covers p work) :
    ∃ z c, (toPolyℂ p).IsRoot z ∧ c ∈ work.toList ∧
      z ∈ Component.region c := by
  have hdegree : p.degree? = some (p.size - 1) := by
    have hpos : 0 < p.size := by omega
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hpos]
  have hnat : 0 < (toPolyℂ p).natDegree := by
    rw [natDegree_toPolyℂ, hdegree]
    simp
    omega
  obtain ⟨z, hzroot⟩ := Complex.exists_root
    (Polynomial.natDegree_pos_iff_degree_pos.mp hnat)
  obtain ⟨s, hs, hzs⟩ := hcover z hzroot
  rw [Worklist.squares, Array.toList_flatMap, List.mem_flatMap] at hs
  obtain ⟨c, hc, hsc⟩ := hs
  exact ⟨z, c, hzroot, hc, ⟨s, hsc, hzs⟩⟩

private theorem normalized_false {p : Hex.ZPoly} {target prec : Int}
    {strategy : Hex.AtomStrategy} {work : Array Hex.Component}
    (hsize : 1 < p.size) (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (hlt : prec < Hex.completenessDepth p target) :
    Hex.IsolationLoop.normalized p target
      (Hex.IsolationLoop.attempts p strategy work) = false := by
  obtain ⟨z, c, hzroot, hc, hzc⟩ := exists_covered_component hsize hcover
  have hcprec := component_prec_eq hprec hc hzc
  rw [Hex.IsolationLoop.normalized, Array.all_eq_false']
  refine ⟨(c, Hex.Component.certify? p strategy c), ?_, ?_⟩
  · rw [Hex.IsolationLoop.attempts]
    exact Array.mem_map_of_mem (Array.mem_toList_iff.mp hc)
  · simp only [hcprec, Bool.not_eq_true]
    simpa only [decide_eq_false_iff_not] using (not_le.mpr hlt)

/-- The last normalized round has reached the executable depth guard. -/
theorem refineAll_normalized {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hnormal : Hex.completenessDepth p target ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy) :
    Hex.IsolationLoop.normalized p target
      (Hex.IsolationLoop.attempts p strategy (Hex.Component.refineAll p work)) = true := by
  rw [Hex.IsolationLoop.normalized, Array.all_eq_true_iff_forall_mem]
  intro t ht
  rw [Hex.IsolationLoop.attempts] at ht
  obtain ⟨c, hc, rfl⟩ := Array.mem_map.mp ht
  obtain ⟨z, iso, hzroot, hzc, hcert, hiso, hziso⟩ :=
    refineAll_component_certifies hp hsize hsep hdepth htarget hprec hcover
      strategy (Array.mem_toList_iff.mpr hc)
  have hcprec : c.prec = prec + 1 := by
    apply component_prec_eq
      (work := Hex.Component.refineAll p work) (prec := prec + 1)
    · intro d hd s hs
      exact refineAll_mem_prec hprec hd hs
    · exact Array.mem_toList_iff.mpr hc
    · exact hzc
  simpa only [hcprec, decide_eq_true_eq] using hnormal

/-- Every attempt on the final normalized worklist succeeds at target
precision. -/
theorem refineAll_allReady {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy) :
    Hex.IsolationLoop.allReady target
      (Hex.IsolationLoop.attempts p strategy (Hex.Component.refineAll p work)) = true := by
  rw [Hex.IsolationLoop.allReady, Array.all_eq_true_iff_forall_mem]
  intro t ht
  rw [Hex.IsolationLoop.attempts] at ht
  obtain ⟨c, hc, rfl⟩ := Array.mem_map.mp ht
  obtain ⟨z, iso, hzroot, hzc, hcert, hiso, hziso⟩ :=
    refineAll_component_certifies hp hsize hsep hdepth htarget hprec hcover
      strategy (Array.mem_toList_iff.mpr hc)
  simp only [hcert]
  simpa only [Hex.Certified.square, decide_eq_true_eq] using hiso

/-- Successful attempts on the final normalized worklist pass the exact
pairwise disc-disjointness check. -/
theorem refineAll_disjoint {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hsepTarget : (Hex.separationDepth p : Int) ≤ target)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy) :
    Hex.IsolationLoop.disjoint
      (Hex.IsolationLoop.attempts p strategy (Hex.Component.refineAll p work)) = true := by
  let final := Hex.Component.refineAll p work
  let tried := Hex.IsolationLoop.attempts p strategy final
  have hpairs : final.toList.Pairwise fun c d =>
      ∀ r, Hex.Component.certify? p strategy c = some r →
        ∀ q, Hex.Component.certify? p strategy d = some q →
          r.square.discsMeet q.square = false := by
    apply (refineAll_nodup p work).imp_of_mem
    intro c d hc hd hcd r hr q hq
    exact refineAll_certificates_disjoint hp hsize hsep hdepth htarget
      hsepTarget hprec hcover strategy hc hd hcd hr hq
  have htried : tried.toList.Pairwise fun a b =>
      ∀ r, a.2 = some r → ∀ q, b.2 = some q →
        r.square.discsMeet q.square = false := by
    dsimp only [tried]
    rw [Hex.IsolationLoop.attempts, Array.toList_map,
      List.pairwise_map]
    exact hpairs
  have houtputs : (Hex.IsolationLoop.outputs tried).toList.Pairwise fun r q =>
      r.square.discsMeet q.square = false := by
    rw [Hex.IsolationLoop.outputs, Array.toList_filterMap,
      List.pairwise_filterMap]
    exact htried
  rw [Hex.IsolationLoop.disjoint]
  apply pairwiseDisjoint_of_pairwise
  simpa only [tried, final, Array.toList_map, List.pairwise_map] using houtputs

/-- Every successful attempt in the final normalized round is an atom. -/
theorem refineAll_outputs_atoms {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy) :
    ∀ r ∈ (Hex.IsolationLoop.outputs (Hex.IsolationLoop.attempts p strategy
        (Hex.Component.refineAll p work))).toList,
      ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  intro r hr
  have hr' := Array.mem_toList_iff.mp hr
  obtain ⟨t, ht, htr⟩ := Array.mem_filterMap.mp hr'
  rcases t with ⟨c, o⟩
  change (c, o) ∈ Hex.IsolationLoop.attempts p strategy
    (Hex.Component.refineAll p work) at ht
  rw [Hex.IsolationLoop.attempts] at ht
  obtain ⟨d, hd, hdo⟩ := Array.mem_map.mp ht
  have hdc : d = c := congrArg Prod.fst hdo
  subst d
  have hocert : o = Hex.Component.certify? p strategy c :=
    (congrArg Prod.snd hdo).symm
  obtain ⟨z, iso, hzroot, hzc, hcert, hiso, hziso⟩ :=
    refineAll_component_certifies hp hsize hsep hdepth htarget hprec hcover
      strategy (Array.mem_toList_iff.mpr hd)
  rw [hocert, hcert] at htr
  exact ⟨iso, Option.some.inj htr |>.symm⟩

/-- The executable early-emission guard exposes precisely the fact needed by
the all-atoms driver: every successful result is an atom. -/
private theorem allAtoms_outputs {p : Hex.ZPoly}
    {tried : Array (Hex.Component × Option (Hex.Certified p))}
    (h : Hex.IsolationLoop.allAtoms tried = true) :
    ∀ r ∈ (Hex.IsolationLoop.outputs tried).toList,
      ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  rw [Hex.IsolationLoop.allAtoms,
    Array.all_eq_true_iff_forall_mem] at h
  intro r hr
  specialize h r (Array.mem_toList_iff.mp hr)
  cases r with
  | atom iso => exact ⟨iso, rfl⟩
  | cluster c => simp at h

/-- Once the last global round has been formed, one positive fuel step emits
its target-ready, pairwise-disjoint atom certificates. -/
theorem isolateLoop_refineAll_success {p : Hex.ZPoly}
    {work : Array Hex.Component} {prec target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1)
    (htarget : target + 5 ≤ prec + 1)
    (hsepTarget : (Hex.separationDepth p : Int) ≤ target)
    (hnormal : Hex.completenessDepth p target ≤ prec + 1)
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (strategy : Hex.AtomStrategy) (fuel : Nat) :
    ∃ rs, Hex.isolateLoop p target strategy (fuel + 1)
        (Hex.Component.refineAll p work) = some rs ∧
      ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  let final := Hex.Component.refineAll p work
  let tried := Hex.IsolationLoop.attempts p strategy final
  have hnorm := refineAll_normalized hp hsize hsep hdepth htarget hnormal
    hprec hcover strategy
  have hready := refineAll_allReady hp hsize hsep hdepth htarget
    hprec hcover strategy
  have hdisjoint := refineAll_disjoint hp hsize hsep hdepth htarget hsepTarget
    hprec hcover strategy
  by_cases hempty : final.isEmpty = true
  · refine ⟨#[], ?_, by simp⟩
    rw [Hex.isolateLoop]
    simp [final, hempty]
  · refine ⟨Hex.IsolationLoop.outputs tried, ?_, ?_⟩
    · rw [Hex.isolateLoop]
      simp [final, hempty, tried, hnorm, hready, hdisjoint]
    · simpa only [tried, final] using refineAll_outputs_atoms hp hsize hsep
        hdepth htarget hprec hcover strategy

/-- Sufficient fuel carries any globally normalized worklist to the fixed
completeness depth and then emits atoms. -/
theorem isolateLoop_complete_of_fuel {p : Hex.ZPoly}
    {target prec : Int} {strategy : Hex.AtomStrategy}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hsepTarget : (Hex.separationDepth p : Int) ≤ target)
    {work : Array Hex.Component}
    (hprec : Worklist.AtPrec work prec)
    (hcover : Worklist.Covers p work)
    (hlt : prec < Hex.completenessDepth p target)
    {fuel : Nat}
    (hfuel : (Hex.completenessDepth p target - prec).toNat < fuel) :
    ∃ rs, Hex.isolateLoop p target strategy fuel work = some rs ∧
      ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  induction fuel generalizing prec work with
  | zero => omega
  | succ fuel ih =>
      let tried := Hex.IsolationLoop.attempts p strategy work
      have hnormFalse : Hex.IsolationLoop.normalized p target tried = false := by
        simpa only [tried] using normalized_false hsize hprec hcover hlt
      obtain ⟨z, c, hzroot, hc, hzc⟩ := exists_covered_component hsize hcover
      have hempty : work.isEmpty = false :=
        Array.isEmpty_eq_false_iff_exists_mem.mpr
          ⟨c, Array.mem_toList_iff.mp hc⟩
      have hnext : Hex.IsolationLoop.next p target tried =
          Hex.Component.refineAll p work := by
        change (if Hex.IsolationLoop.normalized p target tried then
          (Array.range tried.size).flatMap
            (Hex.IsolationLoop.step p target tried)
        else Hex.Component.refineAll p (tried.map (·.1))) = _
        rw [hnormFalse]
        simp [tried, Hex.IsolationLoop.attempts, Function.comp_def]
      have hprec' : Worklist.AtPrec (Hex.Component.refineAll p work) (prec + 1) := by
        intro d hd s hs
        exact refineAll_mem_prec hprec hd hs
      have hcover' : Worklist.Covers p (Hex.Component.refineAll p work) :=
        refineAll_covers hcover
      by_cases hearly : (Hex.IsolationLoop.allAtoms tried &&
          (Hex.IsolationLoop.allReady target tried &&
            Hex.IsolationLoop.disjoint tried)) = true
      · have hearly' := hearly
        simp only [Bool.and_eq_true] at hearly'
        refine ⟨Hex.IsolationLoop.outputs tried, ?_,
          allAtoms_outputs hearly'.1⟩
        rw [Hex.isolateLoop]
        simp [hempty, tried, hnormFalse, hearly]
      · by_cases hlast : Hex.completenessDepth p target ≤ prec + 1
        · have heq : Hex.completenessDepth p target = prec + 1 := by omega
          have hdepth : (Hex.separationDepth p : Int) + 5 ≤ prec + 1 := by
            rw [← heq]
            simp [Hex.completenessDepth]
          have htarget : target + 5 ≤ prec + 1 := by
            rw [← heq]
            simp [Hex.completenessDepth]
          cases fuel with
          | zero =>
              rw [heq] at hfuel
              norm_num at hfuel
          | succ fuel' =>
              obtain ⟨rs, hrec, hatoms⟩ := isolateLoop_refineAll_success
                hp hsize hsep hdepth htarget hsepTarget (by omega) hprec hcover
                strategy fuel'
              refine ⟨rs, ?_, hatoms⟩
              rw [Hex.isolateLoop]
              simp [hempty, tried, hnormFalse, hearly, hnext, hrec]
        · have hlt' : prec + 1 < Hex.completenessDepth p target := by omega
          have hfuel' : (Hex.completenessDepth p target - (prec + 1)).toNat < fuel := by
            omega
          obtain ⟨rs, hrec, hatoms⟩ := ih hprec' hcover' hlt' hfuel'
          refine ⟨rs, ?_, hatoms⟩
          rw [Hex.isolateLoop]
          simp [hempty, tried, hnormFalse, hearly, hnext, hrec]

/-- The executable `fuelFor` budget is sufficient for a Cauchy-started run,
for every atom strategy. -/
theorem isolateAll_cauchy_complete {p : Hex.ZPoly} {target : Int}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hsepTarget : (Hex.separationDepth p : Int) ≤ target)
    (strategy : Hex.AtomStrategy) (hd : 0 < p.degree?.getD 0) :
    ∃ rs, Hex.isolateAll? p target
        #[Hex.Component.cauchy p hd] strategy = some rs ∧
      ∀ r ∈ rs.toList, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso := by
  let work := #[Hex.Component.cauchy p hd]
  let start : Int := -(Hex.cauchyExp p : Int)
  have hprec : Worklist.AtPrec work start := by
    intro c hc s hs
    simp [work] at hc
    subst c
    simp [Hex.Component.cauchy] at hs
    subst s
    rfl
  have hcover : Worklist.Covers p work := by
    intro z hzroot
    obtain ⟨s, hs, hzs⟩ := Component.isRoot_mem_cauchy p hd hzroot
    refine ⟨s, ?_, hzs⟩
    simpa [Worklist.squares, work] using hs
  have hlt : start < Hex.completenessDepth p target := by
    simp [start, Hex.completenessDepth]
    omega
  have hfuel : (Hex.completenessDepth p target - start).toNat <
      Hex.fuelFor p target start := by
    have hcs : Hex.completenessDepth p target ≤ Hex.stopDepth p target := by
      simp [Hex.completenessDepth, Hex.stopDepth, Hex.stopSlack]
    have hmono : (Hex.completenessDepth p target - start).toNat ≤
        (Hex.stopDepth p target - start).toNat :=
      Int.toNat_le_toNat (sub_le_sub_right hcs start)
    rw [Hex.fuelFor]
    omega
  obtain ⟨rs, hloop, hatoms⟩ := isolateLoop_complete_of_fuel hp hsize hsep
    hsepTarget hprec hcover hlt hfuel
  refine ⟨rs, ?_, hatoms⟩
  simpa [Hex.isolateAll?, work, start, Hex.Component.cauchy,
    Hex.Component.prec] using hloop

private theorem list_mapM_atoms {p : Hex.ZPoly}
    (xs : List (Hex.Certified p))
    (h : ∀ r ∈ xs, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso) :
    ∃ ys, xs.mapM Hex.Certified.asAtom? = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons r xs ih =>
      obtain ⟨iso, rfl⟩ := h r (by simp)
      obtain ⟨ys, hys⟩ := ih (fun q hq => h q (by simp [hq]))
      exact ⟨iso :: ys, by simp [Hex.Certified.asAtom?, hys]⟩

private theorem array_mapM_atoms {p : Hex.ZPoly}
    (xs : Array (Hex.Certified p))
    (h : ∀ r ∈ xs.toList, ∃ iso : Hex.DyadicRootIsolation p, r = .atom iso) :
    ∃ ys, xs.mapM Hex.Certified.asAtom? = some ys := by
  obtain ⟨ys, hys⟩ := list_mapM_atoms xs.toList h
  cases harray : xs.mapM Hex.Certified.asAtom? with
  | none =>
      have hrel := Array.toList_mapM
        (xs := xs) (f := Hex.Certified.asAtom?)
      rw [harray, hys] at hrel
      simp at hrel
  | some atoms => exact ⟨atoms, rfl⟩

/-- Every nonzero squarefree executable polynomial is successfully isolated
by each atom strategy. Nonzero constants take the explicit empty-output
branch; positive-degree inputs use the complete Cauchy-started driver. -/
theorem isolate_exists (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int) (strategy : Hex.AtomStrategy) :
    ∃ atoms, Hex.isolate p h atomPrec strategy = some atoms := by
  have hpSize : p.size ≠ 0 := by
    intro hsize0
    apply hp
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)]
    rfl
  by_cases hd : 0 < p.degree?.getD 0
  · have hdegree : p.degree? = some (p.size - 1) := by
      simp [Hex.DensePoly.degree?, hpSize]
    have hsize : 1 < p.size := by
      rw [hdegree] at hd
      simp at hd
      omega
    have hpℂ : toPolyℂ p ≠ 0 := by
      intro hzero
      have hnat := natDegree_toPolyℂ p
      rw [hzero, Polynomial.natDegree_zero, hdegree] at hnat
      simp at hnat
      omega
    let target := max atomPrec (Hex.separationDepth p : Int)
    obtain ⟨rs, hall, hatoms⟩ := isolateAll_cauchy_complete hpℂ hsize
      (HexRootsMathlib.HasOnlySimpleRoots.separable h hp)
      (le_max_right _ _) strategy hd
    obtain ⟨atoms, hmap⟩ := array_mapM_atoms rs hatoms
    refine ⟨atoms, ?_⟩
    rw [Hex.isolate, dif_pos hd]
    change (Hex.isolateAll? p target #[Hex.Component.cauchy p hd] strategy).bind
      (fun rs => rs.mapM Hex.Certified.asAtom?) = some atoms
    rw [hall]
    exact hmap
  · refine ⟨#[], ?_⟩
    rw [Hex.isolate, dif_neg hd]
    simp [hpSize]

/-- Boolean `isSome` form of full driver completeness. -/
theorem isolate_isSome (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int) (strategy : Hex.AtomStrategy) :
    (Hex.isolate p h atomPrec strategy).isSome = true := by
  obtain ⟨atoms, hatoms⟩ := isolate_exists p h hp atomPrec strategy
  rw [hatoms]
  rfl

end

end HexRootsMathlib
