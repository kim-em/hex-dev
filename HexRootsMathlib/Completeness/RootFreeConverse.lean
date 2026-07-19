/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.NKDepth
public import HexRootsMathlib.Completeness.PelletDyadic
public import HexRootsMathlib.Glue

public section

/-!
# Quantitative converse for the executable T-zero test

Failure of `Hex.rootFree` can only occur near a polynomial root.  This module
first proves the exact root-product criterion and then packages a convenient
degree-scaled proximity contrapositive for survivor-component analysis.
-/

open Finset Polynomial

namespace HexRootsMathlib

noncomputable section

/-- A factor-two exact-norm margin at coefficient zero absorbs both Gaussian
dyadic coefficient bounds and makes the executable Pellet check succeed. -/
theorem pelletAt_zero_of_slack {p : Hex.ZPoly} {c : Hex.GaussDyadic}
    {rlo rhi : _root_.Dyadic} (hsize : 0 < p.size)
    (hrhi : 0 ≤ Dyadic.toReal rhi)
    (hslack :
      2 * (∑ i ∈ (Finset.range p.size).erase 0,
          ‖((toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))).coeff i‖ *
            Dyadic.toReal rhi ^ i) <
        ‖((toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))).coeff 0‖) :
    Hex.pelletAt (Hex.taylor p c) 0 rlo rhi = true := by
  let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))
  let S := ∑ i ∈ (Finset.range p.size).erase 0,
    ‖q.coeff i‖ * Dyadic.toReal rhi ^ i
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have htail :
      (∑ i ∈ (Finset.range p.size).erase 0,
          Dyadic.toReal
              (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) *
            Dyadic.toReal rhi ^ i) ≤ √2 * S := by
    calc
      _ ≤ ∑ i ∈ (Finset.range p.size).erase 0,
          (√2 * ‖q.coeff i‖) * Dyadic.toReal rhi ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        have hcoeff :
            Dyadic.toReal
                (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) ≤
              √2 * ‖q.coeff i‖ := by
          dsimp [q]
          rw [show ((toPolyℂ p).comp
              (X + C (GaussDyadic.toComplex c))).coeff i =
                GaussDyadic.toComplex ((Hex.taylor p c).getD i (0, 0)) by
            exact (taylor_coeff p c i).symm]
          exact GaussDyadic.hi_le_sqrt_two_mul_norm _
        gcongr
      _ = √2 * S := by
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hlo0 : 0 ≤ Dyadic.toReal
      (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 0 (0, 0))) := by
    rw [GaussDyadic.toReal_lo]
    positivity
  have hmain : ‖q.coeff 0‖ ≤
      √2 * Dyadic.toReal
        (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 0 (0, 0))) := by
    dsimp [q]
    rw [show ((toPolyℂ p).comp
        (X + C (GaussDyadic.toComplex c))).coeff 0 =
          GaussDyadic.toComplex ((Hex.taylor p c).getD 0 (0, 0)) by
      exact (taylor_coeff p c 0).symm]
    exact GaussDyadic.norm_le_sqrt_two_mul_lo _
  have hsqrt : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hstrict : √2 * S <
      Dyadic.toReal (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 0 (0, 0))) := by
    dsimp [q, S] at hslack ⊢
    nlinarith
  apply pelletAt_of_bound (by simpa only [Hex.taylor_size] using hsize)
  simpa only [Hex.taylor_size, pow_zero, mul_one] using htail.trans_lt hstrict

/-- After splitting off one root, the coefficient-zero tail is controlled by
the weighted mass of the normalized remote-root product. -/
private theorem pellet_zero_normalized_slack {g : ℂ[X]} {a : ℂ} {n : ℕ}
    {R E : ℝ} (_hn : 0 < n) (hR : 0 ≤ R) (hdeg : g.natDegree < n)
    (hg0 : g.coeff 0 = 1) (hmass : coeffMass g n R ≤ 1 + E)
    (hmargin : 2 * (R + (R + ‖a‖) * E) < ‖a‖) :
    2 * (∑ i ∈ (Finset.range (n + 1)).erase 0,
        ‖((X - C a) * g).coeff i‖ * R ^ i) <
      ‖((X - C a) * g).coeff 0‖ := by
  let h := (X - C a) * g
  have hfactor : 0 ≤ R + ‖a‖ := add_nonneg hR (norm_nonneg a)
  have htotal : coeffMass h (n + 1) R ≤ (R + ‖a‖) * (1 + E) :=
    (coeffMass_X_sub_C_mul_le hR hdeg).trans
      (mul_le_mul_of_nonneg_left hmass hfactor)
  have hzero : ‖h.coeff 0‖ = ‖a‖ := by
    dsimp [h]
    simp [mul_coeff_zero, hg0]
  have hzeroMem : 0 ∈ Finset.range (n + 1) := by simp
  have hdecomp :
      (∑ i ∈ (Finset.range (n + 1)).erase 0,
          ‖h.coeff i‖ * R ^ i) + ‖h.coeff 0‖ = coeffMass h (n + 1) R := by
    unfold coeffMass
    simpa only [pow_zero, mul_one] using
      (Finset.sum_erase_add (Finset.range (n + 1))
        (fun i => ‖h.coeff i‖ * R ^ i) hzeroMem)
  change 2 * (∑ i ∈ (Finset.range (n + 1)).erase 0,
      ‖h.coeff i‖ * R ^ i) < ‖h.coeff 0‖
  rw [hzero] at hdecomp ⊢
  nlinarith

/-- If one root is separated from all the others and is far enough from the
centre relative to the test radius, the actual executable T-zero test
succeeds.  The contrapositive gives the constant-radius survivor bound used
by the glue argument. -/
theorem rootFree_one_root_of_margin {p : Hex.ZPoly} {sq : Hex.DyadicSquare}
    {z : ℂ} {roots : Multiset ℂ} {d : ℝ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hroots : (toPolyℂ p).roots = z ::ₘ roots) (hd : 0 < d)
    (hremote : ∀ w ∈ roots, d ≤ ‖w - DyadicSquare.center sq‖)
    (hmargin :
      let R := Dyadic.toReal sq.radiusHi
      let E := (1 + R / d) ^ roots.card - 1
      2 * (R + (R + ‖z - DyadicSquare.center sq‖) * E) <
        ‖z - DyadicSquare.center sq‖) :
    Hex.rootFree p sq = true := by
  let q := (toPolyℂ p).comp (X + C (DyadicSquare.center sq))
  let t := roots.map fun w => w - DyadicSquare.center sq
  let a := z - DyadicSquare.center sq
  let g := remotePoly (t.map Inv.inv)
  let h := (X - C a) * g
  let K := q.leadingCoeff * (t.map Neg.neg).prod
  let R := Dyadic.toReal sq.radiusHi
  let E := (1 + R / d) ^ t.card - 1
  have hq : q ≠ 0 := (comp_X_add_C_ne_zero_iff (p := toPolyℂ p)
    (t := DyadicSquare.center sq)).2 hp
  have hqroots : q.roots = a ::ₘ t := by
    have htranslate : q.roots = (toPolyℂ p).roots.map
        fun w => w - DyadicSquare.center sq := by
      dsimp [q]
      convert roots_comp_C_mul_X_add_C (toPolyℂ p) 1
        (DyadicSquare.center sq) isUnit_one using 1 <;> simp
    rw [htranslate, hroots]
    simp [a, t]
  have hremote' : ∀ w ∈ t, d ≤ ‖w‖ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    exact hremote u hu
  have ht0 : ∀ w ∈ t, w ≠ 0 := by
    intro w hw hw0
    subst w
    simpa using (hd.trans_le (hremote' 0 hw)).ne'
  have hnorm := normalize_root_product t ht0
  have hfactor : q = C K * h := by
    calc
      q = C q.leadingCoeff * (q.roots.map fun w => X - C w).prod :=
        (IsAlgClosed.splits q).eq_prod_roots
      _ = C q.leadingCoeff *
          ((X - C a) * (t.map fun w => X - C w).prod) := by
        rw [hqroots]
        simp
      _ = C (q.leadingCoeff * (t.map Neg.neg).prod) *
          ((X - C a) * remotePoly (t.map Inv.inv)) := by
        rw [← hnorm, map_mul]
        ring
      _ = C K * h := rfl
  have hK : K ≠ 0 := by
    apply mul_ne_zero (leadingCoeff_ne_zero.mpr hq)
    apply Multiset.prod_ne_zero
    intro hw
    obtain ⟨u, hu, hzero⟩ := Multiset.mem_map.mp hw
    have : -u ≠ 0 := by simpa using ht0 u hu
    exact this hzero
  have hR : 0 ≤ R := by
    dsimp [R]
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt2Hi : 0 ≤ Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_nonneg (by rw [DyadicSquare.halfWidth_eq]; positivity) hsqrt2Hi
  have hgdeg : g.natDegree < t.card + 1 := by
    dsimp [g]
    simpa using Nat.lt_succ_of_le (natDegree_remotePoly_le (t.map Inv.inv))
  have hgdom :
      2 * (∑ i ∈ (Finset.range (t.card + 2)).erase 0,
          ‖h.coeff i‖ * R ^ i) < ‖h.coeff 0‖ := by
    apply pellet_zero_normalized_slack (n := t.card + 1)
      (E := (1 + R / d) ^ t.card - 1) (by omega) hR hgdeg
    · exact coeff_remotePoly_zero _
    · dsimp [g]
      calc
        coeffMass (remotePoly (t.map Inv.inv)) (t.card + 1) R ≤
            (1 + R / d) ^ t.card :=
          coeffMass_remotePoly_le hd hR hremote'
        _ = 1 + ((1 + R / d) ^ t.card - 1) := by ring
    · simpa [a, t, R, E] using hmargin
  have hsizeEq : p.size = t.card + 2 := by
    calc
      p.size = (toPolyℂ p).natDegree + 1 := by
        rw [natDegree_toPolyℂ]
        have hpdeg : p.degree? = some (p.size - 1) := by
          simp [Hex.DensePoly.degree?, Nat.ne_of_gt (by omega : 0 < p.size)]
        rw [hpdeg, Option.getD_some]
        omega
      _ = roots.card + 2 := by
        rw [natDegree_eq_of_roots hroots]
      _ = t.card + 2 := by simp [t]
  apply pelletAt_zero_of_slack (by omega : 0 < p.size) hR
  change 2 * (∑ i ∈ (Finset.range p.size).erase 0,
      ‖q.coeff i‖ * R ^ i) < ‖q.coeff 0‖
  rw [hfactor, hsizeEq]
  simp only [coeff_C_mul, norm_mul]
  calc
    2 * (∑ i ∈ (Finset.range (t.card + 2)).erase 0,
        (‖K‖ * ‖h.coeff i‖) * R ^ i) =
        ‖K‖ * (2 * ∑ i ∈ (Finset.range (t.card + 2)).erase 0,
          ‖h.coeff i‖ * R ^ i) := by
      rw [Finset.mul_sum]
      calc
        (∑ i ∈ (Finset.range (t.card + 2)).erase 0,
            2 * (‖K‖ * ‖h.coeff i‖ * R ^ i)) =
            ∑ i ∈ (Finset.range (t.card + 2)).erase 0,
              ‖K‖ * (2 * (‖h.coeff i‖ * R ^ i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ‖K‖ * (2 * ∑ i ∈ (Finset.range (t.card + 2)).erase 0,
            ‖h.coeff i‖ * R ^ i) := by
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
    _ < ‖K‖ * ‖h.coeff 0‖ :=
      mul_lt_mul_of_pos_left hgdom (norm_pos_iff.mpr hK)

/-- If every root is remote enough that the normalized positive-degree tail
has mass below one half, the actual executable `rootFree` test succeeds. -/
theorem rootFree_of_roots {p : Hex.ZPoly} {s : Hex.DyadicSquare} {d : ℝ}
    (hp : toPolyℂ p ≠ 0) (hsize : 0 < p.size) (hd : 0 < d)
    (hremote : ∀ z ∈ (toPolyℂ p).roots,
      d ≤ ‖z - DyadicSquare.center s‖)
    (htail :
      2 * ((1 + Dyadic.toReal s.radiusHi / d) ^ (toPolyℂ p).roots.card - 1) < 1) :
    Hex.rootFree p s = true := by
  let q := (toPolyℂ p).comp (X + C (DyadicSquare.center s))
  let roots := (toPolyℂ p).roots.map fun z => z - DyadicSquare.center s
  let R := Dyadic.toReal s.radiusHi
  let E := (1 + R / d) ^ roots.card - 1
  have hq : q ≠ 0 := (comp_X_add_C_ne_zero_iff (p := toPolyℂ p)
    (t := DyadicSquare.center s)).2 hp
  have hqroots : q.roots = roots := by
    dsimp [q, roots]
    convert roots_comp_C_mul_X_add_C (toPolyℂ p) 1
      (DyadicSquare.center s) isUnit_one using 1 <;> simp
  have hremote' : ∀ z ∈ roots, d ≤ ‖z‖ := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    exact hremote w hw
  have hq0 : q.coeff 0 ≠ 0 := by
    intro hzero
    have hzroot : q.IsRoot 0 := by simpa [Polynomial.IsRoot,
      coeff_zero_eq_eval_zero] using hzero
    have hzmem : 0 ∈ roots := by rw [← hqroots]; exact (mem_roots hq).2 hzroot
    exact (hd.trans_le (hremote' 0 hzmem)).ne' (by simp)
  have hfactor := C_coeff_zero_mul_remotePoly q hq hq0
  rw [hqroots] at hfactor
  have hR : 0 ≤ R := by
    dsimp [R]
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt2Hi : 0 ≤ Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_nonneg (by rw [DyadicSquare.halfWidth_eq]; positivity) hsqrt2Hi
  have hdegree : p.size = roots.card + 1 := by
    calc
      p.size = (toPolyℂ p).natDegree + 1 := by
        rw [natDegree_toPolyℂ]
        have hpdeg : p.degree? = some (p.size - 1) := by
          simp [Hex.DensePoly.degree?, Nat.ne_of_gt hsize]
        rw [hpdeg, Option.getD_some]
        omega
      _ = (toPolyℂ p).roots.card + 1 := by
        rw [(IsAlgClosed.splits (toPolyℂ p)).natDegree_eq_card_roots]
      _ = roots.card + 1 := by simp [roots]
  have htailNorm :
      (∑ i ∈ (Finset.range p.size).erase 0, ‖q.coeff i‖ * R ^ i) ≤
        ‖q.coeff 0‖ * E := by
    rw [hdegree]
    calc
      _ = ‖q.coeff 0‖ *
          (∑ i ∈ (Finset.range (roots.card + 1)).erase 0,
            ‖(remotePoly (roots.map Inv.inv)).coeff i‖ * R ^ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hcoeff : q.coeff i = q.coeff 0 *
            (remotePoly (roots.map Inv.inv)).coeff i := by
          have hc := congrArg (fun u : ℂ[X] => u.coeff i) hfactor
          simpa only [coeff_C_mul] using hc.symm
        rw [hcoeff, norm_mul]
        ring
      _ ≤ ‖q.coeff 0‖ * E := by
        gcongr
        exact remotePoly_tail_le hd hR hremote'
  apply pelletAt_zero_of_slack hsize hR
  change 2 * (∑ i ∈ (Finset.range p.size).erase 0, ‖q.coeff i‖ * R ^ i) <
    ‖q.coeff 0‖
  have hq0norm : 0 < ‖q.coeff 0‖ := norm_pos_iff.2 hq0
  have hE : 2 * E < 1 := by simpa [E, R, roots] using htail
  nlinarith [mul_le_mul_of_nonneg_left htailNorm (by norm_num : (0 : ℝ) ≤ 2)]

/-- A square retained by the T-zero filter lies within eight degree-scaled
upper radii of an actual root. -/
theorem exists_root_ne_of_not_rootFree {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsize : 0 < p.size)
    (hkeep : Hex.rootFree p s ≠ true) :
    ∃ z ∈ (toPolyℂ p).roots,
      ‖z - DyadicSquare.center s‖ <
        8 * (Nat.max 2 (p.degree?.getD 0) : ℝ) * Dyadic.toReal s.radiusHi := by
  let roots := (toPolyℂ p).roots
  let N := Nat.max 2 (p.degree?.getD 0)
  let R := Dyadic.toReal s.radiusHi
  let d := 8 * (N : ℝ) * R
  have hR : 0 < R := by
    dsimp [R]
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt2Hi : 0 < Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity) hsqrt2Hi
  have hN : 0 < (N : ℝ) := by
    have hNnat : 0 < N :=
      (by omega : 0 < 2).trans_le (by dsimp [N]; exact Nat.le_max_left _ _)
    exact_mod_cast hNnat
  have hd : 0 < d := by dsimp [d]; positivity
  have hcard : roots.card ≤ N := by
    have hcardDegree : roots.card = p.degree?.getD 0 := by
      dsimp [roots]
      rw [← (IsAlgClosed.splits (toPolyℂ p)).natDegree_eq_card_roots,
        natDegree_toPolyℂ]
    rw [hcardDegree]
    exact Nat.le_max_right _ _
  by_contra hnone
  have hremote : ∀ z ∈ roots, d ≤ ‖z - DyadicSquare.center s‖ := by
    intro z hz
    apply le_of_not_gt
    intro hlt
    apply hnone
    exact ⟨z, hz, by simpa [d, N, R] using hlt⟩
  have hratio : R / d = 1 / (8 * (N : ℝ)) := by
    dsimp [d]
    field_simp
  have hsmall : (roots.card : ℝ) * (R / d) ≤ 1 / 8 := by
    rw [hratio]
    rw [show (roots.card : ℝ) * (1 / (8 * (N : ℝ))) =
      (roots.card : ℝ) / (8 * (N : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 8 * (N : ℝ))).2
    have hcardReal : (roots.card : ℝ) ≤ N := by exact_mod_cast hcard
    nlinarith
  have hpow := NKData.one_add_pow_le (by positivity : 0 ≤ R / d) roots.card
    (hsmall.trans (by norm_num))
  have htail : 2 * ((1 + R / d) ^ roots.card - 1) < 1 := by
    nlinarith
  apply hkeep
  apply rootFree_of_roots hp hsize hd
  · simpa [roots] using hremote
  · simpa [roots, R] using htail

/-- At `separationDepth`, every retained square is extremely close to one
root on the Mahler separation scale. -/
theorem exists_root_ne_of_depth {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsize : 0 < p.size)
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    (hkeep : Hex.rootFree p s ≠ true) :
    ∃ z ∈ (toPolyℂ p).roots,
      ‖z - DyadicSquare.center s‖ <
        ((2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)) / 32 := by
  obtain ⟨z, hz, hnear⟩ := exists_root_ne_of_not_rootFree hp hsize hkeep
  refine ⟨z, hz, hnear.trans_le ?_⟩
  have hradius := NKData.radiusHi_mul_degree_le hprec
  nlinarith

/-- At separation depth the remote-root tail is already negligible, so a
square retained by T-zero is within `65/32` executable radii of one root. The
`1/384` tail at the implemented depth leaves enough room for enclosing a
whole component with a loss of at most two precision levels. -/
theorem exists_root_le_radius_of_not_rootFree {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    (hkeep : Hex.rootFree p s ≠ true) :
    ∃ z ∈ (toPolyℂ p).roots,
      ‖z - DyadicSquare.center s‖ ≤ (65 / 32 : ℝ) * Dyadic.toReal s.radiusHi := by
  let f := toPolyℂ p
  let c := DyadicSquare.center s
  let R := Dyadic.toReal s.radiusHi
  let N := Nat.max 2 (p.degree?.getD 0)
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  let d := 3 * M
  obtain ⟨z, hz, hzc⟩ := exists_root_ne_of_depth hp (by omega) hprec hkeep
  obtain ⟨roots, hroots⟩ := Multiset.exists_cons_of_mem hz
  have hrootsEq : f.roots = z ::ₘ roots := by simpa [f] using hroots
  have hsepC : f.Separable := by
    have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [show f = (HexPolyZMathlib.toPolyℚ p).map (algebraMap ℚ ℂ) by
      dsimp [f, HexPolyZMathlib.toPolyℚ]
      rw [Polynomial.map_map, hcomp]]
    exact hsep.map
  have hnodup : f.roots.Nodup := nodup_roots hsepC
  have hne : ∀ w ∈ roots, w ≠ z := by
    intro w hw heq
    subst w
    rw [hrootsEq] at hnodup
    exact (Multiset.nodup_cons.mp hnodup).1 hw
  have hM : 0 < M := by dsimp [M]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hR : 0 < R := by
    dsimp [R]
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt2Hi : 0 < Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity) hsqrt2Hi
  have hremote : ∀ w ∈ roots, d ≤ ‖w - c‖ := by
    intro w hw
    have hwroot : f.IsRoot w := (mem_roots hp).1 (by
      rw [hrootsEq]
      exact Multiset.mem_cons_of_mem hw)
    have hzroot : f.IsRoot z := (mem_roots hp).1 (by simpa [f] using hz)
    have hsepzw := mahlerPrec_separates p hsep z w hzroot hwroot (hne w hw).symm
    have htri : ‖z - w‖ ≤ ‖z - c‖ + ‖w - c‖ := by
      calc
        ‖z - w‖ = ‖(z - c) - (w - c)‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖w - c‖ := norm_sub_le _ _
    change M < ‖z - w‖ / 4 at hsepzw
    change ‖z - c‖ < M / 32 at hzc
    dsimp [d]
    nlinarith
  have hcard : roots.card ≤ N := by
    have hdegree : roots.card + 1 = p.degree?.getD 0 := by
      calc
        roots.card + 1 = f.roots.card := by rw [hrootsEq]; simp
        _ = f.natDegree := (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
        _ = p.degree?.getD 0 := by simpa [f] using natDegree_toPolyℂ p
    have : roots.card ≤ p.degree?.getD 0 := by omega
    exact this.trans (Nat.le_max_right _ _)
  have hRN : R * (N : ℝ) ≤ M / 256 := by
    simpa [R, N, M] using NKData.radiusHi_mul_degree_le hprec
  have hsmall : (roots.card : ℝ) * (R / d) ≤ 1 / 768 := by
    have hcardReal : (roots.card : ℝ) ≤ N := by exact_mod_cast hcard
    have hRN' : R * (roots.card : ℝ) ≤ M / 256 :=
      (mul_le_mul_of_nonneg_left hcardReal hR.le).trans hRN
    dsimp [d]
    rw [show (roots.card : ℝ) * (R / (3 * M)) =
      (R * roots.card) / (3 * M) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 3 * M)).2
    nlinarith
  have hpow := NKData.one_add_pow_le (by positivity : 0 ≤ R / d)
    roots.card (hsmall.trans (by norm_num))
  have hE : (1 + R / d) ^ roots.card - 1 ≤ 1 / 384 := by
    nlinarith
  by_contra hnone
  have hfar : (65 / 32 : ℝ) * R < ‖z - c‖ := by
    apply lt_of_not_ge
    intro hle
    apply hnone
    exact ⟨z, by simpa [f] using hz, by simpa [R, c] using hle⟩
  apply hkeep
  apply rootFree_one_root_of_margin hp hsize hrootsEq hd hremote
  dsimp [R, d, c] at hE hfar ⊢
  have hEnonneg : 0 ≤ (1 + Dyadic.toReal s.radiusHi / (3 * M)) ^ roots.card - 1 := by
    have : 1 ≤ (1 + Dyadic.toReal s.radiusHi / (3 * M)) ^ roots.card := by
      apply one_le_pow₀
      have : 0 ≤ Dyadic.toReal s.radiusHi / (3 * M) := by positivity
      linarith
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hE
    (add_nonneg hR.le (norm_nonneg (z - DyadicSquare.center s)))]

/-- Convenient looser strict form of the sharp `65/32` survivor bound. -/
theorem exists_root_lt_three_radius_of_not_rootFree {p : Hex.ZPoly}
    {s : Hex.DyadicSquare} (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    (hkeep : Hex.rootFree p s ≠ true) :
    ∃ z ∈ (toPolyℂ p).roots,
      ‖z - DyadicSquare.center s‖ < 3 * Dyadic.toReal s.radiusHi := by
  obtain ⟨z, hz, hnear⟩ :=
    exists_root_le_radius_of_not_rootFree
      hp hsize hsep hprec hkeep
  refine ⟨z, hz, hnear.trans_lt ?_⟩
  have hR : 0 < Dyadic.toReal s.radiusHi := by
    rw [DyadicSquare.radiusHi_eq]
    have : 0 < Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity) this
  nlinarith

namespace DyadicSquare

/-- Executable edge adjacency is exactly one grid step in the sup metric. -/
theorem supDist_center_eq_of_adjacent {s t : Hex.DyadicSquare}
    (hadj : Hex.DyadicSquare.adjacent s t = true) :
    s.prec = t.prec ∧
      supDist (center s) (center t) = 2 * halfWidth s := by
  rw [Hex.DyadicSquare.adjacent] at hadj
  split at hadj <;> rename_i hprec
  · let twoH : _root_.Dyadic := .ofIntWithPrec 1 (s.prec - 1)
    change ((decide (Hex.Dyadic.abs (s.re - t.re) = twoH) &&
        decide (Hex.Dyadic.abs (s.im - t.im) = 0)) ||
      (decide (Hex.Dyadic.abs (s.re - t.re) = 0) &&
        decide (Hex.Dyadic.abs (s.im - t.im) = twoH))) = true at hadj
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
    have htwo : Dyadic.toReal twoH = 2 * halfWidth s := by
      dsimp [twoH]
      rw [Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul, halfWidth_eq,
        show -(s.prec - 1) = 1 + -s.prec by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    constructor
    · exact hprec
    · rcases hadj with ⟨hre, him⟩ | ⟨hre, him⟩
      · have hreR := congrArg Dyadic.toReal hre
        have himR := congrArg Dyadic.toReal him
        simp only [Dyadic.toReal_abs, htwo, Dyadic.toReal_zero] at hreR himR
        rw [supDist, supNorm]
        simp only [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Complex.sub_re, Complex.sub_im]
        rw [← Dyadic.toReal_sub, ← Dyadic.toReal_sub, hreR, himR]
        rw [max_eq_left]
        rw [halfWidth_eq]
        positivity
      · have hreR := congrArg Dyadic.toReal hre
        have himR := congrArg Dyadic.toReal him
        simp only [Dyadic.toReal_abs, htwo, Dyadic.toReal_zero] at hreR himR
        rw [supDist, supNorm]
        simp only [center, Hex.DyadicSquare.center, GaussDyadic.toComplex,
          Complex.sub_re, Complex.sub_im]
        rw [← Dyadic.toReal_sub, ← Dyadic.toReal_sub, hreR, himR]
        rw [max_eq_right]
        rw [halfWidth_eq]
        positivity
  · simp at hadj

end DyadicSquare

/-- Adjacent retained squares at separation depth have the same nearby root,
with the sharp degree-independent bound on both centres. -/
theorem exists_common_nearRoot_of_adjacent {p : Hex.ZPoly}
    {s t : Hex.DyadicSquare} (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    (hs : Hex.rootFree p s ≠ true) (ht : Hex.rootFree p t ≠ true)
    (hadj : Hex.DyadicSquare.adjacent s t = true) :
    ∃ z ∈ (toPolyℂ p).roots,
      ‖z - DyadicSquare.center s‖ ≤
          (65 / 32 : ℝ) * Dyadic.toReal s.radiusHi ∧
        ‖z - DyadicSquare.center t‖ ≤
          (65 / 32 : ℝ) * Dyadic.toReal t.radiusHi := by
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  have hadjData := DyadicSquare.supDist_center_eq_of_adjacent hadj
  have htprec : (Hex.separationDepth p : Int) ≤ t.prec := by
    rw [← hadjData.1]
    exact hprec
  obtain ⟨z, hz, hzs⟩ :=
    exists_root_le_radius_of_not_rootFree hp hsize hsep hprec hs
  obtain ⟨w, hw, hwt⟩ :=
    exists_root_le_radius_of_not_rootFree hp hsize hsep htprec ht
  have hradiusEq : Dyadic.toReal t.radiusHi = Dyadic.toReal s.radiusHi := by
    rw [DyadicSquare.radiusHi_eq, DyadicSquare.radiusHi_eq,
      DyadicSquare.halfWidth_eq, DyadicSquare.halfWidth_eq, ← hadjData.1]
  have hcenterSup : supNorm (DyadicSquare.center s - DyadicSquare.center t) =
      2 * DyadicSquare.halfWidth s := by
    simpa [supDist] using hadjData.2
  have hcenterNorm : ‖DyadicSquare.center s - DyadicSquare.center t‖ <
      2 * Dyadic.toReal s.radiusHi := by
    have hnorm := Complex.norm_le_sqrt_two_mul_max
      (DyadicSquare.center s - DyadicSquare.center t)
    change ‖DyadicSquare.center s - DyadicSquare.center t‖ ≤
      √2 * supNorm (DyadicSquare.center s - DyadicSquare.center t) at hnorm
    rw [hcenterSup] at hnorm
    have hradius : √2 * DyadicSquare.halfWidth s <
        Dyadic.toReal s.radiusHi := by
      simpa only [DyadicSquare.radius, mul_comm] using
        DyadicSquare.radius_lt_radiusHi s
    nlinarith [Real.sqrt_nonneg 2]
  have hRpos : 0 < Dyadic.toReal s.radiusHi := by
    rw [DyadicSquare.radiusHi_eq]
    have : 0 < Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity) this
  have hzwUpper : ‖z - w‖ < 8 * Dyadic.toReal s.radiusHi := by
    have htri : ‖z - w‖ ≤ ‖z - DyadicSquare.center s‖ +
        ‖DyadicSquare.center s - DyadicSquare.center t‖ +
          ‖w - DyadicSquare.center t‖ := by
      calc
        ‖z - w‖ = ‖(z - DyadicSquare.center s) +
            (DyadicSquare.center s - DyadicSquare.center t) -
              (w - DyadicSquare.center t)‖ := by ring_nf
        _ ≤ ‖(z - DyadicSquare.center s) +
              (DyadicSquare.center s - DyadicSquare.center t)‖ +
            ‖w - DyadicSquare.center t‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    rw [hradiusEq] at hwt
    nlinarith
  have hRsmall : 8 * Dyadic.toReal s.radiusHi ≤ M / 64 := by
    have hradius := NKData.radiusHi_mul_degree_le hprec
    have htwo : (2 : ℝ) ≤ Nat.max 2 (p.degree?.getD 0) := by
      exact_mod_cast Nat.le_max_left 2 (p.degree?.getD 0)
    have hRnonneg : 0 ≤ Dyadic.toReal s.radiusHi := by
      rw [DyadicSquare.radiusHi_eq]
      have : 0 ≤ Dyadic.toReal Hex.sqrt2Hi := by
        norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
      exact mul_nonneg (by rw [DyadicSquare.halfWidth_eq]; positivity) this
    have : 2 * Dyadic.toReal s.radiusHi ≤ M / 256 := by
      calc
        _ = Dyadic.toReal s.radiusHi * 2 := by ring
        _ ≤ Dyadic.toReal s.radiusHi *
            (Nat.max 2 (p.degree?.getD 0) : ℝ) :=
          mul_le_mul_of_nonneg_left htwo hRnonneg
        _ ≤ M / 256 := by simpa [M] using hradius
    nlinarith
  have hzw : z = w := by
    by_contra hne
    have hsepzw := mahlerPrec_separates p hsep z w
      ((mem_roots hp).1 hz) ((mem_roots hp).1 hw) hne
    change M < ‖z - w‖ / 4 at hsepzw
    have hM : 0 < M := by dsimp [M]; positivity
    nlinarith
  subst w
  exact ⟨z, hz, hzs, hwt⟩

/-- A root is in the degree-independent proximity neighborhood of a retained
square. -/
@[expose] def NearRoot (p : Hex.ZPoly) (s : Hex.DyadicSquare) (z : ℂ) : Prop :=
  z ∈ (toPolyℂ p).roots ∧
    ‖z - DyadicSquare.center s‖ ≤
      (65 / 32 : ℝ) * Dyadic.toReal s.radiusHi

/-- Mahler separation makes the nearby root of a separation-depth square
unique. -/
theorem nearRoot_unique {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    {z w : ℂ} (hz : NearRoot p s z) (hw : NearRoot p s w) : z = w := by
  by_contra hne
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  have hzw : ‖z - w‖ < 6 * Dyadic.toReal s.radiusHi := by
    have htri : ‖z - w‖ ≤ ‖z - DyadicSquare.center s‖ +
        ‖w - DyadicSquare.center s‖ := by
      calc
        ‖z - w‖ = ‖(z - DyadicSquare.center s) -
            (w - DyadicSquare.center s)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    exact htri.trans_lt (by
      have hz' := hz.2
      have hw' := hw.2
      have hRpos : 0 < Dyadic.toReal s.radiusHi := by
        rw [DyadicSquare.radiusHi_eq]
        have : 0 < Dyadic.toReal Hex.sqrt2Hi := by
          norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
        exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity) this
      nlinarith)
  have hRsmall : 6 * Dyadic.toReal s.radiusHi ≤ M / 64 := by
    have hradius := NKData.radiusHi_mul_degree_le hprec
    have htwo : (2 : ℝ) ≤ Nat.max 2 (p.degree?.getD 0) := by
      exact_mod_cast Nat.le_max_left 2 (p.degree?.getD 0)
    have hRnonneg : 0 ≤ Dyadic.toReal s.radiusHi := by
      rw [DyadicSquare.radiusHi_eq]
      have : 0 ≤ Dyadic.toReal Hex.sqrt2Hi := by
        norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
      exact mul_nonneg (by rw [DyadicSquare.halfWidth_eq]; positivity) this
    have : 2 * Dyadic.toReal s.radiusHi ≤ M / 256 := by
      calc
        _ = Dyadic.toReal s.radiusHi * 2 := by ring
        _ ≤ Dyadic.toReal s.radiusHi *
            (Nat.max 2 (p.degree?.getD 0) : ℝ) :=
          mul_le_mul_of_nonneg_left htwo hRnonneg
        _ ≤ M / 256 := by simpa [M] using hradius
    nlinarith
  have hsepzw := mahlerPrec_separates p hsep z w
    ((mem_roots hp).1 hz.1) ((mem_roots hp).1 hw.1) hne
  change M < ‖z - w‖ / 4 at hsepzw
  have hM : 0 < M := by dsimp [M]; positivity
  nlinarith

/-- Crossing one retained adjacency edge preserves the semantic nearby root. -/
theorem nearRoot_iff_of_edge {p : Hex.ZPoly} {s t : Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hprec : ∀ u, u = s ∨ u = t →
      (Hex.separationDepth p : Int) ≤ u.prec)
    (hkeep : ∀ u, u = s ∨ u = t → Hex.rootFree p u ≠ true)
    (hedge : Glue.Edge s t) (z : ℂ) :
    NearRoot p s z ↔ NearRoot p t z := by
  obtain ⟨w, hw, hws, hwt⟩ := exists_common_nearRoot_of_adjacent
    hp hsize hsep (hprec s (Or.inl rfl)) (hkeep s (Or.inl rfl))
      (hkeep t (Or.inr rfl)) hedge
  have hwS : NearRoot p s w := ⟨hw, hws⟩
  have hwT : NearRoot p t w := ⟨hw, hwt⟩
  constructor
  · intro hz
    rw [nearRoot_unique hp hsep (hprec s (Or.inl rfl)) hz hwS]
    exact hwT
  · intro hz
    rw [nearRoot_unique hp hsep (hprec t (Or.inr rfl)) hz hwT]
    exact hwS

/-- Nearby-root semantics is constant on a connected retained component. -/
theorem nearRoot_iff_of_connected {p : Hex.ZPoly}
    {component : List Hex.DyadicSquare} {s t : Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hconnected : Glue.Connected component)
    (hprec : ∀ u ∈ component, (Hex.separationDepth p : Int) ≤ u.prec)
    (hkeep : ∀ u ∈ component, Hex.rootFree p u ≠ true)
    (hs : s ∈ component) (ht : t ∈ component) (z : ℂ) :
    NearRoot p s z ↔ NearRoot p t z := by
  apply hconnected.2 (fun u => NearRoot p u z)
    (fun a ha b hb hab => ?_) s hs t ht
  rcases hab with hab | hba
  · exact nearRoot_iff_of_edge hp hsize hsep
      (fun u hu => hu.elim (fun h => h ▸ hprec a ha)
        (fun h => h ▸ hprec b hb))
      (fun u hu => hu.elim (fun h => h ▸ hkeep a ha)
        (fun h => h ▸ hkeep b hb)) hab z
  · exact (nearRoot_iff_of_edge hp hsize hsep
      (fun u hu => hu.elim (fun h => h ▸ hprec b hb)
        (fun h => h ▸ hprec a ha))
      (fun u hu => hu.elim (fun h => h ▸ hkeep b hb)
        (fun h => h ▸ hkeep a ha)) hba z).symm

/-- Every connected component of retained separation-depth squares has one
root satisfying the sharp proximity bound at every member. -/
theorem exists_nearRoot_of_connected {p : Hex.ZPoly}
    {component : List Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hconnected : Glue.Connected component)
    (hprec : ∀ u ∈ component, (Hex.separationDepth p : Int) ≤ u.prec)
    (hkeep : ∀ u ∈ component, Hex.rootFree p u ≠ true) :
    ∃ z ∈ (toPolyℂ p).roots, ∀ u ∈ component,
      ‖z - DyadicSquare.center u‖ ≤
        (65 / 32 : ℝ) * Dyadic.toReal u.radiusHi := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil component hconnected.1
  obtain ⟨z, hz, hzs⟩ := exists_root_le_radius_of_not_rootFree
    hp hsize hsep (hprec s hs) (hkeep s hs)
  refine ⟨z, hz, ?_⟩
  intro u hu
  exact (nearRoot_iff_of_connected hp hsize hsep hconnected
    hprec hkeep hs hu z).mp
    ⟨hz, hzs⟩ |>.2

/-- Every actual glued component of retained separation-depth squares belongs
to one root, uniformly satisfying the sharp proximity bound. -/
theorem exists_nearRoot_of_glueCovered {p : Hex.ZPoly}
    {squares component : Array Hex.DyadicSquare}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hprec : ∀ u ∈ squares.toList,
      (Hex.separationDepth p : Int) ≤ u.prec)
    (hkeep : ∀ u ∈ squares.toList, Hex.rootFree p u ≠ true)
    (hc : component ∈ (Hex.glueCovered squares).toList) :
    ∃ z ∈ (toPolyℂ p).roots, ∀ u ∈ component.toList,
      ‖z - DyadicSquare.center u‖ ≤
        (65 / 32 : ℝ) * Dyadic.toReal u.radiusHi := by
  apply exists_nearRoot_of_connected hp hsize hsep
    (glueCovered_connected squares component hc)
  · intro u hu
    exact hprec u (mem_of_mem_glueCovered hc hu)
  · intro u hu
    exact hkeep u (mem_of_mem_glueCovered hc hu)

end

end HexRootsMathlib
