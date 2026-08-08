/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.NKCertify
public import HexRootsMathlib.Pellet

public section

/-!
# General certificate soundness

This module combines the Newton--Kantorovich and Pellet certificate forms and
tracks the same-count containment guards used by speculative certification.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

namespace ZPoly

/-- Reflection changes the complex polynomial only by composition with
`-X` and a nonzero sign used to restore a positive leading coefficient. -/
theorem toPolyℂ_negRoots {p : Hex.ZPoly} (hprim : Hex.ZPoly.Primitive p) :
    ∃ u : ℂ, u ≠ 0 ∧
      toPolyℂ p.negRoots = Polynomial.C u * (toPolyℂ p).comp (-Polynomial.X) := by
  rw [Hex.ZPoly.negRoots_eq_reflect hprim]
  unfold Hex.ZPoly.normalizePrimitiveSign
  split
  · refine ⟨-1, by norm_num, ?_⟩
    simp [toPolyℂ, HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_dilate, Polynomial.map_comp]
  · refine ⟨1, by norm_num, ?_⟩
    simp [toPolyℂ, HexPolyZMathlib.toPolynomial_dilate,
      Polynomial.map_comp]

/-- A root reflects to a root of the normalized reflected polynomial. -/
theorem isRoot_negRoots {p : Hex.ZPoly} {z : ℂ}
    (hprim : Hex.ZPoly.Primitive p) (hz : (toPolyℂ p).IsRoot z) :
    (toPolyℂ p.negRoots).IsRoot (-z) := by
  obtain ⟨u, hu, hpoly⟩ := toPolyℂ_negRoots hprim
  change (toPolyℂ p.negRoots).eval (-z) = 0
  rw [hpoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_X, neg_neg]
  exact mul_eq_zero.mpr (Or.inr hz)

/-- Leading-sign normalization changes the complex polynomial only by a
nonzero scalar. -/
theorem toPolyℂ_normalizePrimitiveSign (p : Hex.ZPoly) :
    ∃ u : ℂ, u ≠ 0 ∧
      toPolyℂ (Hex.ZPoly.normalizePrimitiveSign p) =
        Polynomial.C u * toPolyℂ p := by
  unfold Hex.ZPoly.normalizePrimitiveSign
  split
  · refine ⟨-1, by norm_num, ?_⟩
    simp [toPolyℂ, HexPolyMathlib.toPolynomial_scale]
  · refine ⟨1, by norm_num, ?_⟩
    simp

end ZPoly

namespace DyadicSquare

@[simp] theorem center_neg (s : Hex.DyadicSquare) :
    center s.neg = -center s := by
  apply Complex.ext <;>
    simp [Hex.DyadicSquare.neg, center, Hex.DyadicSquare.center,
      GaussDyadic.toComplex]

@[simp] theorem radius_neg (s : Hex.DyadicSquare) :
    radius s.neg = radius s := by
  simp [radius_eq, Hex.DyadicSquare.neg]

@[simp] theorem openSquare_neg {s : Hex.DyadicSquare} {z : ℂ} :
    -z ∈ openSquare s.neg ↔ z ∈ openSquare s := by
  change supDist (-z) (center s.neg) < halfWidth s.neg ↔
    supDist z (center s) < halfWidth s
  rw [center_neg]
  have hwidth : halfWidth s.neg = halfWidth s := by
    simp [halfWidth_eq, Hex.DyadicSquare.neg]
  rw [hwidth]
  unfold supDist
  rw [show -z - -center s = -(z - center s) by ring]
  simp [supNorm, abs_sub_comm]

@[simp] theorem closedSquare_neg {s : Hex.DyadicSquare} {z : ℂ} :
    -z ∈ closedSquare s.neg ↔ z ∈ closedSquare s := by
  change supDist (-z) (center s.neg) ≤ halfWidth s.neg ↔
    supDist z (center s) ≤ halfWidth s
  rw [center_neg]
  have hwidth : halfWidth s.neg = halfWidth s := by
    simp [halfWidth_eq, Hex.DyadicSquare.neg]
  rw [hwidth]
  unfold supDist
  rw [show -z - -center s = -(z - center s) by ring]
  simp [supNorm, abs_sub_comm]

@[simp] theorem disc_neg {s : Hex.DyadicSquare} {z : ℂ} :
    -z ∈ disc s.neg ↔ z ∈ disc s := by
  change dist (-z) (center s.neg) < radius s.neg ↔
    dist z (center s) < radius s
  rw [center_neg, radius_neg, dist_neg_neg]

@[simp] theorem closedDisc_neg {s : Hex.DyadicSquare} {z : ℂ} :
    -z ∈ closedDisc s.neg ↔ z ∈ closedDisc s := by
  change dist (-z) (center s.neg) ≤ radius s.neg ↔
    dist z (center s) ≤ radius s
  rw [center_neg, radius_neg, dist_neg_neg]

end DyadicSquare

namespace DyadicRootIsolation

/-- The open counterpart of an atom's selected certified region. -/
@[expose] def openRegion {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) : Set ℂ :=
  if iso.witness.isNK then
    DyadicSquare.openSquare iso.square
  else
    DyadicSquare.disc iso.square

/-- The selected open atom region lies in its closed counterpart. -/
theorem openRegion_subset_region {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) :
    openRegion iso ⊆ region iso := by
  simp only [openRegion, region]
  split
  · intro z hz
    rw [NKData.mem_closedSquare_iff]
    exact ((NKData.mem_openSquare_iff iso.square z).mp hz).le
  · exact Metric.ball_subset_closedBall

/-- Every atom contains an interior simple root, unique in its selected
closed certified region. If both witnesses hold, this follows from the NK
witness because that is the executable region-selection rule. -/
theorem sound {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p) :
    ∃ z, (toPolyℂ p).eval z = 0 ∧ z ∈ openRegion iso ∧
      (toPolyℂ p).derivative.eval z ≠ 0 ∧
      ∀ w, (toPolyℂ p).eval w = 0 → w ∈ region iso → w = z := by
  rcases iso with ⟨s, certificate⟩
  induction certificate with
  | nk h =>
      simpa [openRegion, region, Hex.AtomCertificate.isNK] using NKData.sound h
  | pellet h =>
      simpa [openRegion, region, Hex.AtomCertificate.isNK] using
        PelletWitness.sound h
  | @neg p s hprim certificate ih =>
      obtain ⟨z, hzroot, hzopen, hzderiv, hzunique⟩ := ih
      obtain ⟨u, hu, hpoly⟩ := ZPoly.toPolyℂ_negRoots hprim
      have heval (w : ℂ) :
          (toPolyℂ p.negRoots).eval w = u * (toPolyℂ p).eval (-w) := by
        rw [hpoly]
        simp
      have hderiv (w : ℂ) :
          (toPolyℂ p.negRoots).derivative.eval w =
            -u * (toPolyℂ p).derivative.eval (-w) := by
        rw [hpoly]
        simp [Polynomial.derivative_comp]
      refine ⟨-z, ?_, ?_, ?_, ?_⟩
      · rw [heval]
        simp [hzroot]
      · simp only [openRegion, Hex.AtomCertificate.isNK]
        rw [openRegion] at hzopen
        by_cases hkind : certificate.isNK = true
        · simp only [hkind, if_true] at hzopen ⊢
          exact DyadicSquare.openSquare_neg.mpr hzopen
        · simp only [hkind] at hzopen ⊢
          exact DyadicSquare.disc_neg.mpr hzopen
      · rw [hderiv, neg_neg]
        exact mul_ne_zero (neg_ne_zero.mpr hu) hzderiv
      · intro w hwroot hwregion
        have hsourceRoot : (toPolyℂ p).eval (-w) = 0 := by
          rw [heval] at hwroot
          exact (mul_eq_zero.mp hwroot).resolve_left hu
        have hsourceRegion : -w ∈
            DyadicRootIsolation.region ⟨s, certificate⟩ := by
          simp only [region, Hex.AtomCertificate.isNK] at hwregion ⊢
          by_cases hkind : certificate.isNK = true
          · simp only [hkind, if_true] at hwregion ⊢
            have hiff := DyadicSquare.closedSquare_neg (s := s) (z := -w)
            simp only [neg_neg] at hiff
            exact hiff.mp hwregion
          · simp [hkind] at hwregion ⊢
            have hiff := DyadicSquare.closedDisc_neg (s := s) (z := -w)
            simp only [neg_neg] at hiff
            exact hiff.mp hwregion
        have hneg : -w = z := hzunique (-w) hsourceRoot hsourceRegion
        exact neg_eq_iff_eq_neg.mp hneg
  | @normalize p s certificate ih =>
      obtain ⟨z, hzroot, hzopen, hzderiv, hzunique⟩ := ih
      obtain ⟨u, hu, hpoly⟩ := ZPoly.toPolyℂ_normalizePrimitiveSign p
      have heval (w : ℂ) :
          (toPolyℂ (Hex.ZPoly.normalizePrimitiveSign p)).eval w =
            u * (toPolyℂ p).eval w := by
        rw [hpoly]
        simp
      have hderiv (w : ℂ) :
          (toPolyℂ (Hex.ZPoly.normalizePrimitiveSign p)).derivative.eval w =
            u * (toPolyℂ p).derivative.eval w := by
        rw [hpoly]
        simp
      refine ⟨z, ?_, ?_, ?_, ?_⟩
      · rw [heval]
        exact mul_eq_zero.mpr (Or.inr hzroot)
      · simpa [openRegion, Hex.AtomCertificate.isNK] using hzopen
      · rw [hderiv]
        exact mul_ne_zero hu hzderiv
      · intro w hwroot hwregion
        have hsourceRoot : (toPolyℂ p).eval w = 0 := by
          rw [heval] at hwroot
          exact (mul_eq_zero.mp hwroot).resolve_left hu
        apply hzunique w hsourceRoot
        convert hwregion using 1
        ext q
        by_cases hkind : certificate.isNK = true <;>
          simp [region, Hex.AtomCertificate.isNK, hkind]

end DyadicRootIsolation

namespace Certified

/-- Number of roots of `q` in an arbitrary set, counted with multiplicity. -/
@[expose] noncomputable def rootsIn (q : ℂ[X]) (S : Set ℂ) : Nat := by
  classical
  exact (q.roots.filter fun w => w ∈ S).card

end Certified

private theorem uniqueSimple_rootCount {q : ℂ[X]} {S : Set ℂ} {z : ℂ}
    (hzroot : q.eval z = 0) (hzmem : z ∈ S)
    (hzderiv : q.derivative.eval z ≠ 0)
    (hunique : ∀ w, q.eval w = 0 → w ∈ S → w = z) :
    Certified.rootsIn q S = 1 := by
  classical
  have hq : q ≠ 0 := by
    intro hzero
    apply hzderiv
    rw [hzero]
    simp
  have hzroots : z ∈ q.roots := (mem_roots hq).mpr hzroot
  have hcountPos : 0 < q.roots.count z := Multiset.count_pos.mpr hzroots
  have hcountLe : q.roots.count z ≤ 1 := by
    by_contra hnot
    have hmultiple : 1 < q.rootMultiplicity z := by
      rw [← count_roots]
      omega
    exact hzderiv ((one_lt_rootMultiplicity_iff_isRoot hq).mp hmultiple).2
  have hcount : q.roots.count z = 1 := by omega
  have heq : q.roots.filter (fun w => w ∈ S) = {z} := by
    apply Multiset.ext.mpr
    intro a
    by_cases haz : a = z
    · subst a
      rw [Multiset.count_filter_of_pos hzmem, hcount]
      simp
    · have hanot : a ∉ q.roots.filter (fun w => w ∈ S) := by
        intro ha
        obtain ⟨haroots, haS⟩ := Multiset.mem_filter.mp ha
        have haroot : q.eval a = 0 := (mem_roots hq).mp haroots
        exact haz (hunique a haroot haS)
      rw [Multiset.count_eq_zero.mpr hanot]
      simp [haz]
  rw [Certified.rootsIn, heq]
  simp

private theorem pellet_closed_count {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {k : Nat} (hk : 0 < k) (h : Hex.witness p s k) :
    Certified.rootsIn (toPolyℂ p) (DyadicSquare.closedDisc s) = k := by
  classical
  let q := toPolyℂ p
  have hcount := PelletWitness.roots h
  have hq : q ≠ 0 := by
    intro hzero
    change rootsInDisc q (DyadicSquare.center s) (DyadicSquare.radius s) = k at hcount
    rw [hzero] at hcount
    simp [rootsInDisc] at hcount
    omega
  have heq : q.roots.filter (fun z => z ∈ DyadicSquare.closedDisc s) =
      q.roots.filter (fun z => z ∈ DyadicSquare.disc s) := by
    apply Multiset.filter_congr
    intro z hz
    have hzroot : q.eval z = 0 := (mem_roots hq).mp hz
    constructor
    · intro hzclosed
      rw [DyadicSquare.closedDisc, Metric.mem_closedBall] at hzclosed
      rw [DyadicSquare.disc, Metric.mem_ball]
      apply lt_of_le_of_ne hzclosed
      intro hzeq
      exact (PelletWitness.boundary h (mem_sphere.mpr hzeq)) hzroot
    · intro hzopen
      change z ∈ Metric.ball (DyadicSquare.center s) (DyadicSquare.radius s) at hzopen
      change z ∈ Metric.closedBall (DyadicSquare.center s) (DyadicSquare.radius s)
      exact Metric.ball_subset_closedBall hzopen
  change (q.roots.filter fun z => z ∈ DyadicSquare.closedDisc s).card = k
  rw [heq, ← Multiset.countP_eq_card_filter]
  exact PelletWitness.roots h

namespace Certified

/-- The number of polynomial roots in a certificate's selected closed
region, counted with multiplicity. -/
@[expose] noncomputable def rootCount {p : Hex.ZPoly} (r : Hex.Certified p) : Nat :=
  rootsIn (toPolyℂ p) (region r)

/-- Uniform semantic contract for both certificate constructors. Every
certificate has its stored multiplicity count in the selected closed region;
atoms additionally have an interior simple root unique there, while clusters
exclude roots from their disc boundary. -/
@[expose] def Sound {p : Hex.ZPoly} (r : Hex.Certified p) : Prop :=
  rootCount r = count r ∧
    match r with
    | .atom iso =>
        ∃ z, (toPolyℂ p).eval z = 0 ∧
          z ∈ DyadicRootIsolation.openRegion iso ∧
          (toPolyℂ p).derivative.eval z ≠ 0 ∧
          ∀ w, (toPolyℂ p).eval w = 0 →
            w ∈ DyadicRootIsolation.region iso → w = z
    | .cluster cl =>
        ∀ z, z ∈ sphere (DyadicSquare.center (Hex.encSquare cl.squares))
          (DyadicSquare.radius (Hex.encSquare cl.squares)) →
          (toPolyℂ p).eval z ≠ 0

/-- Every certificate is semantically sound by construction. -/
theorem sound {p : Hex.ZPoly} (r : Hex.Certified p) : Sound r := by
  cases r with
  | atom iso =>
      rw [Sound]
      obtain ⟨z, hzroot, hzopen, hzderiv, hzunique⟩ :=
        DyadicRootIsolation.sound iso
      have hzregion : z ∈ DyadicRootIsolation.region iso :=
        DyadicRootIsolation.openRegion_subset_region iso hzopen
      refine ⟨?_, ⟨z, hzroot, hzopen, hzderiv, hzunique⟩⟩
      simpa only [rootCount, region, count] using
        uniqueSimple_rootCount hzroot hzregion hzderiv hzunique
  | cluster cl =>
      rw [Sound]
      refine ⟨?_, fun _ hz => DyadicRootCluster.boundary cl hz⟩
      simpa only [rootCount, region, count] using
        pellet_closed_count cl.k_pos cl.witness

end Certified

/-- Equal positive Pellet counts on nested closed discs force every root in
the outer disc into the inner disc. Strict Pellet inequalities exclude both
boundaries, so the open-disc counts also count roots in the closed discs. -/
theorem root_mem_nestedPellet {p : Hex.ZPoly} {inner outer : Hex.DyadicSquare}
    {k : ℕ} (hk : 0 < k) (hinner : Hex.witness p inner k)
    (houter : Hex.witness p outer k)
    (hsubset : DyadicSquare.closedDisc inner ⊆ DyadicSquare.closedDisc outer)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hzouter : z ∈ DyadicSquare.closedDisc outer) :
    z ∈ DyadicSquare.closedDisc inner := by
  classical
  let q := toPolyℂ p
  have hq : q ≠ 0 := by
    intro hzero
    have hcount := PelletWitness.roots houter
    change rootsInDisc q (DyadicSquare.center outer)
      (DyadicSquare.radius outer) = k at hcount
    rw [hzero] at hcount
    simp [rootsInDisc] at hcount
    omega
  have filter_closed_eq_open (s : Hex.DyadicSquare) (hw : Hex.witness p s k) :
      q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc s) =
        q.roots.filter (fun a => a ∈ DyadicSquare.disc s) := by
    apply Multiset.filter_congr
    intro a ha
    have haroot : q.eval a = 0 := (mem_roots hq).mp ha
    constructor
    · intro haclosed
      rw [DyadicSquare.closedDisc, Metric.mem_closedBall] at haclosed
      rw [DyadicSquare.disc, Metric.mem_ball]
      apply lt_of_le_of_ne haclosed
      intro hae
      have hasphere : a ∈ sphere (DyadicSquare.center s)
          (DyadicSquare.radius s) := by
        rw [mem_sphere]
        exact hae
      exact (PelletWitness.boundary hw hasphere) haroot
    · intro ha
      exact Metric.ball_subset_closedBall ha
  have hcardInner :
      (q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc inner)).card = k := by
    rw [filter_closed_eq_open inner hinner, ← Multiset.countP_eq_card_filter]
    exact PelletWitness.roots hinner
  have hcardOuter :
      (q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc outer)).card = k := by
    rw [filter_closed_eq_open outer houter, ← Multiset.countP_eq_card_filter]
    exact PelletWitness.roots houter
  have hle : q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc inner) ≤
      q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc outer) :=
    Multiset.monotone_filter_right q.roots (fun _ ha => hsubset ha)
  have heq : q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc inner) =
      q.roots.filter (fun a => a ∈ DyadicSquare.closedDisc outer) :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcardInner, hcardOuter])
  have hzmem : z ∈ q.roots := (mem_roots hq).mpr hzroot
  have hzfilter : z ∈ q.roots.filter
      (fun a => a ∈ DyadicSquare.closedDisc outer) :=
    Multiset.mem_filter.mpr ⟨hzmem, hzouter⟩
  rw [← heq] at hzfilter
  exact (Multiset.mem_filter.mp hzfilter).2

/-- A root in a `k = 1` Pellet disc belongs to the atom's selected semantic
region even when the same square also happens to carry an NK witness (in
which case `DyadicRootIsolation.region` selects the closed square). -/
theorem pelletAtom_mem_region {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.witness p s 1) {z : ℂ}
    (hzdisc : z ∈ DyadicSquare.closedDisc s) :
    z ∈ Certified.region (.atom ⟨s, .pellet h⟩) := by
  simpa [Certified.region, DyadicRootIsolation.region,
    Hex.AtomCertificate.isNK] using hzdisc

private theorem basePellet_mem {p : Hex.ZPoly} {c : Hex.Component} {k : Nat}
    (hk : 0 < k) (hw : Hex.witness p (Hex.encSquare c.squares) k)
    {z : ℂ}
    (hzsquare : z ∈ DyadicSquare.closedSquare (Hex.encSquare c.squares)) :
    let cl : Hex.DyadicRootCluster p := ⟨c.squares, k, hk, hw⟩
    z ∈ Certified.region
      (if hk1 : k = 1 then .atom (cl.atomize hk1) else .cluster cl) := by
  dsimp only
  split <;> rename_i hk1
  · subst k
    exact pelletAtom_mem_region hw
      (DyadicSquare.closedSquare_subset_closedDisc _ hzsquare)
  · exact DyadicSquare.closedSquare_subset_closedDisc _ hzsquare

private theorem candidatePellet_mem {p : Hex.ZPoly} {c : Hex.Component} {k : Nat}
    {cand : Hex.DyadicSquare}
    (hk : 0 < k) (hw : Hex.witness p (Hex.encSquare c.squares) k)
    (hins : (Hex.encSquare #[cand]).discInside (Hex.encSquare c.squares) = true)
    (hw' : Hex.witness p (Hex.encSquare #[cand]) k)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hzbase : z ∈ DyadicSquare.closedDisc (Hex.encSquare c.squares)) :
    let cl : Hex.DyadicRootCluster p :=
      ⟨#[cand], k, hk, hw'⟩
    z ∈ Certified.region
      (if hk1 : k = 1 then .atom (cl.atomize hk1) else .cluster cl) := by
  dsimp only
  have hzcand : z ∈ DyadicSquare.closedDisc (Hex.encSquare #[cand]) :=
    root_mem_nestedPellet hk hw' hw
      (DyadicSquare.closedDisc_subset_of_discInside hins) hzroot hzbase
  split <;> rename_i hk1
  · subst k
    exact pelletAtom_mem_region hw' hzcand
  · exact hzcand

/-- Each cached-shift Pellet attempt preserves every polynomial root covered
    by the input component. -/
theorem certifyPelletAtShift_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {shift : Hex.TaylorShift p (Hex.encSquare c.squares).center} {k : Nat}
    {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletAtShift? p c shift k = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  let enc := Hex.encSquare c.squares
  have hzsquare : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare c hz
  have hzbase : z ∈ DyadicSquare.closedDisc enc :=
    DyadicSquare.closedSquare_subset_closedDisc enc hzsquare
  unfold Hex.Component.certifyPelletAtShift? at hcert
  dsimp only at hcert
  split at hcert <;> rename_i hk
  · split at hcert <;> rename_i hw
    · have hw₀ : Hex.witness p enc k := by
        simpa [Hex.witness] using hw
      let cl : Hex.DyadicRootCluster p := ⟨c.squares, k, hk, hw₀⟩
      let base : Hex.Certified p :=
        if hk1 : k = 1 then .atom (cl.atomize hk1) else .cluster cl
      let cand := Hex.TaylorShift.newtonSquare enc shift k
      split at hcert <;> rename_i hins
      · split at hcert <;> rename_i hw'
        · have hw₀' : Hex.witness p (Hex.encSquare #[cand]) k := by
            simpa [Hex.witness, cand] using hw'
          let cl' : Hex.DyadicRootCluster p := ⟨#[cand], k, hk, hw₀'⟩
          split at hcert <;> rename_i hk1
          · have hr : r = .atom (cl'.atomize hk1) :=
              (Option.some.inj hcert).symm
            subst r
            simpa only [dif_pos hk1] using
              candidatePellet_mem hk hw₀ hins hw₀' hzroot hzbase
          · have hr : r = .cluster cl' := (Option.some.inj hcert).symm
            subst r
            simpa only [dif_neg hk1] using
              candidatePellet_mem hk hw₀ hins hw₀' hzroot hzbase
        · have hr : r = base := (Option.some.inj hcert).symm
          subst r
          exact basePellet_mem hk hw₀ hzsquare
      · have hr : r = base := (Option.some.inj hcert).symm
        subst r
        exact basePellet_mem hk hw₀ hzsquare
    · simp at hcert
  · simp at hcert

/-- One exact cached-shift Pellet attempt preserves every covered root. -/
theorem certifyPelletExactAt_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {shift : Hex.TaylorShift p (Hex.encSquare c.squares).center} {k : Nat}
    {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletExactAt? p c shift k = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  let enc := Hex.encSquare c.squares
  have hzsquare : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare c hz
  have hzbase : z ∈ DyadicSquare.closedDisc enc :=
    DyadicSquare.closedSquare_subset_closedDisc enc hzsquare
  unfold Hex.Component.certifyPelletExactAt? at hcert
  dsimp only at hcert
  split at hcert <;> rename_i hk
  · split at hcert <;> rename_i hw
    · have hw₀ : Hex.witness p enc k := by
        exact Hex.TaylorShift.witnessCheck_implies enc shift k hw
      let cl : Hex.DyadicRootCluster p := ⟨c.squares, k, hk, hw₀⟩
      let base : Hex.Certified p :=
        if hk1 : k = 1 then .atom (cl.atomize hk1) else .cluster cl
      let cand := Hex.TaylorShift.newtonSquare enc shift k
      split at hcert <;> rename_i hins
      · split at hcert <;> rename_i hw'
        · let shift' := Hex.TaylorShift.compute p (Hex.encSquare #[cand]).center
          have hw₀' : Hex.witness p (Hex.encSquare #[cand]) k := by
            exact Hex.TaylorShift.witnessCheck_implies
              (Hex.encSquare #[cand]) shift' k hw'
          let cl' : Hex.DyadicRootCluster p := ⟨#[cand], k, hk, hw₀'⟩
          split at hcert <;> rename_i hk1
          · have hr : r = .atom (cl'.atomize hk1) :=
              (Option.some.inj hcert).symm
            subst r
            simpa only [dif_pos hk1] using
              candidatePellet_mem hk hw₀ hins hw₀' hzroot hzbase
          · have hr : r = .cluster cl' := (Option.some.inj hcert).symm
            subst r
            simpa only [dif_neg hk1] using
              candidatePellet_mem hk hw₀ hins hw₀' hzroot hzbase
        · have hr : r = base := (Option.some.inj hcert).symm
          subst r
          exact basePellet_mem hk hw₀ hzsquare
      · have hr : r = base := (Option.some.inj hcert).symm
        subst r
        exact basePellet_mem hk hw₀ hzsquare
    · simp at hcert
  · simp at hcert

/-- A direct soft all-count result preserves every root in the input
component. -/
theorem certifyPelletSoft_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {shift : Hex.TaylorShift p (Hex.encSquare c.squares).center}
    {ks : List Nat} {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletSoft? p c shift ks = some r)
    {z : ℂ}
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  let enc := Hex.encSquare c.squares
  have hzsquare : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare c hz
  unfold Hex.Component.certifyPelletSoft? at hcert
  dsimp only at hcert
  split at hcert
  · split at hcert <;> rename_i hcand
    · cases hcert
    · rename_i k
      have hpublic : Hex.softRefinementCandidate? p enc ks = some k := by
        rw [← shift.softRefinementCandidate?_eq enc ks]
        exact hcand
      have hs := Hex.softRefinementCandidate?_sound hpublic
      have hw : Hex.witness p enc k := by
        unfold Hex.witness Hex.witnessCheck
        have hs' : Hex.softWitnessCheck p enc k = true := by
          simpa only [enc] using hs.2
        have hsCached :
            (Hex.TaylorShift.compute p enc.center).softWitnessCheck enc k = true := by
          rw [Hex.TaylorShift.softWitnessCheck_eq]
          exact hs'
        by_cases hprec : enc.prec < 32 <;>
          simp [Hex.TaylorShift.combinedWitnessCheck, hprec, hsCached]
      let cl : Hex.DyadicRootCluster p := ⟨c.squares, k, hs.1, hw⟩
      by_cases hk1 : k = 1
      · rw [dif_pos hk1] at hcert
        have hr : r = .atom (cl.atomize hk1) := (Option.some.inj hcert).symm
        subst r
        simpa only [dif_pos hk1] using
          basePellet_mem hs.1 hw hzsquare
      · rw [dif_neg hk1] at hcert
        have hr : r = .cluster cl := (Option.some.inj hcert).symm
        subst r
        simpa only [dif_neg hk1] using
          basePellet_mem hs.1 hw hzsquare
  · simp at hcert

/-- The public one-count wrapper has the cached attempt's preservation
    property. -/
theorem certifyPelletAt_preserves {p : Hex.ZPoly} {c : Hex.Component} {k : Nat}
    {r : Hex.Certified p} (hcert : Hex.Component.certifyPelletAt? p c k = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  unfold Hex.Component.certifyPelletAt? at hcert
  exact certifyPelletAtShift_preserves hcert hzroot hz

/-- Searching an exact list with one cached shift preserves every polynomial
root covered by the input component. -/
theorem certifyPelletExactList_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {shift : Hex.TaylorShift p (Hex.encSquare c.squares).center}
    (ks : List Nat) {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletExactList? p c shift ks = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  induction ks with
  | nil => simp [Hex.Component.certifyPelletExactList?] at hcert
  | cons k ks ih =>
      rw [Hex.Component.certifyPelletExactList?] at hcert
      cases hat : Hex.Component.certifyPelletExactAt? p c shift k with
      | none =>
          simp only [hat, Option.orElse_none] at hcert
          exact ih hcert
      | some r' =>
          simp only [hat, Option.orElse_some] at hcert
          have hr : r' = r := Option.some.inj hcert
          subst r'
          exact certifyPelletExactAt_preserves hat hzroot hz

/-- The soft-first, exact-fallback cached list search preserves every covered
root. -/
theorem certifyPelletListShift_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {shift : Hex.TaylorShift p (Hex.encSquare c.squares).center}
    (ks : List Nat) {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletListShift? p c shift ks = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  unfold Hex.Component.certifyPelletListShift? at hcert
  cases hsoft : Hex.Component.certifyPelletSoft? p c shift ks with
  | some r' =>
      rw [hsoft] at hcert
      cases r' with
      | atom iso =>
          exact certifyPelletAtShift_preserves hcert hzroot hz
      | cluster cl =>
          exact certifyPelletAtShift_preserves hcert hzroot hz
  | none =>
      rw [hsoft] at hcert
      exact certifyPelletExactList_preserves ks hcert hzroot hz

/-- The public candidate-count search inherits the cached implementation's
    preservation property. -/
theorem certifyPelletList_preserves {p : Hex.ZPoly} {c : Hex.Component}
    (ks : List Nat) {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletList? p c ks = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  unfold Hex.Component.certifyPelletList? at hcert
  exact certifyPelletListShift_preserves ks hcert hzroot hz

/-- Pellet candidate search with a caller-supplied shift preserves every root
    covered by the input component. -/
theorem certifyPelletShift_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {shift : Hex.TaylorShift p (Hex.encSquare c.squares).center}
    {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPelletShift? p c shift = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  unfold Hex.Component.certifyPelletShift? at hcert
  exact certifyPelletListShift_preserves _ hcert hzroot hz

/-- The public Pellet search inherits the caller-supplied shift
    implementation's preservation property. -/
theorem certifyPellet_preserves {p : Hex.ZPoly} {c : Hex.Component}
    {r : Hex.Certified p}
    (hcert : Hex.Component.certifyPellet? p c = some r)
    {z : ℂ} (hzroot : (toPolyℂ p).eval z = 0)
    (hz : z ∈ Component.region c) : z ∈ Certified.region r := by
  unfold Hex.Component.certifyPellet? at hcert
  exact certifyPelletList_preserves _ hcert hzroot hz

/-- The input component lies in the central quarter of the widened Pellet
component used by `certify?`. -/
private theorem mem_widePellet {c : Hex.Component} {z : ℂ}
    (hz : z ∈ Component.region c) :
    z ∈ Component.region
      (⟨#[(Hex.encSquare c.squares).doubled.doubled], c.candidateK⟩ :
        Hex.Component) := by
  refine ⟨(Hex.encSquare c.squares).doubled.doubled, by simp, ?_⟩
  exact DyadicSquare.closedSquare_subset_doubled _
    (Component.region_subset_doubledEnc c hz)

/-- Pellet-only component certification preserves every input-component
root, including through the speculative same-count recentring branch. -/
theorem certifier_preserves_pellet (p : Hex.ZPoly) :
    Certifier.Preserves p .pellet := by
  intro c r hcert z hzroot hz
  simp only [Hex.Component.certify?] at hcert
  exact certifyPelletShift_preserves hcert hzroot (mem_widePellet hz)

/-- A combined-strategy result is an NK result from the common leading
branch, or the result of falling through to the Pellet search. -/
theorem certify_nkThenPellet_cases {p : Hex.ZPoly} {c : Hex.Component}
    {r : Hex.Certified p}
    (hcert : Hex.Component.certify? p .nkThenPellet c = some r) :
    let base := (Hex.encSquare c.squares).doubled
    let cand := (Hex.newtonSquare p base 1).doubled
    (∃ (_hbase : Hex.nkWitness p base) (_hinside : cand.squareInside base = true)
        (hcand : Hex.nkWitness p cand),
        r = .atom ⟨cand, .nk hcand⟩) ∨
      (∃ hbase : Hex.nkWitness p base,
        r = .atom ⟨base, .nk hbase⟩) ∨
      ∃ shift,
        Hex.Component.certifyPelletShift? p
          ⟨#[(Hex.encSquare c.squares).doubled.doubled], c.candidateK⟩ shift = some r := by
  simp only [Hex.Component.certify?, Hex.nkWitness,
    Hex.TaylorShift.nkWitnessCheck_eq, Hex.TaylorShift.newtonSquare_eq] at hcert ⊢
  split at hcert <;> rename_i hbase
  · split at hcert <;> rename_i hinside
    · split at hcert <;> rename_i hcand
      · left
        exact ⟨hbase, hinside, hcand, Option.some.inj hcert.symm⟩
      · right; left
        exact ⟨hbase, Option.some.inj hcert.symm⟩
    · right; left
      exact ⟨hbase, Option.some.inj hcert.symm⟩
  · right; right
    exact ⟨_, hcert⟩

/-- The default combined strategy preserves every input-component root in
both its NK prefix and its Pellet fallback. -/
theorem certifier_preserves_nkThenPellet (p : Hex.ZPoly) :
    Certifier.Preserves p .nkThenPellet := by
  intro c r hcert z hzroot hz
  rcases certify_nkThenPellet_cases hcert with h | h | h
  · obtain ⟨hbase, hinside, hcand, rfl⟩ := h
    rw [nkAtom_region hcand]
    apply nkRoot_mem_nested hcand hbase
      (DyadicSquare.closedSquare_subset_of_squareInside hinside) hzroot
    exact Component.region_subset_doubledEnc c hz
  · obtain ⟨hbase, rfl⟩ := h
    rw [nkAtom_region hbase]
    exact Component.region_subset_doubledEnc c hz
  · obtain ⟨shift, h⟩ := h
    exact certifyPelletShift_preserves h hzroot (mem_widePellet hz)

/-- Every component certification strategy preserves each covered root. -/
theorem certifier_preserves (p : Hex.ZPoly) (strategy : Hex.AtomStrategy) :
    Certifier.Preserves p strategy := by
  cases strategy with
  | nk => exact certifier_preserves_nk p
  | pellet => exact certifier_preserves_pellet p
  | nkThenPellet => exact certifier_preserves_nkThenPellet p

/-- Every successful executable component certification satisfies the
uniform certificate contract. The equality hypothesis identifies the
executable result; semantic soundness itself is structural because each
`Certified` constructor already stores its checked witness. -/
theorem certify_sound {p : Hex.ZPoly} {strategy : Hex.AtomStrategy}
    {c : Hex.Component} {r : Hex.Certified p}
    (_hcert : Hex.Component.certify? p strategy c = some r) : Certified.Sound r :=
  Certified.sound r

end

end HexRootsMathlib
