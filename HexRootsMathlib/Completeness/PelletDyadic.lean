/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.PelletConverse
public import HexRootsMathlib.Pellet

public section

/-!
# Executable Pellet converse

This module absorbs the Gaussian-dyadic coefficient and dyadic-radius slack
needed to turn a wide one-root isolation into the three executable Pellet
checks.
-/

open Finset Polynomial

namespace HexRootsMathlib

noncomputable section

private theorem sum_erase_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n k : ℕ) :
    (∑ i ∈ (Finset.range n).erase k, f i) =
      ∑ i ∈ Finset.range n, if i = k then 0 else f i := by
  classical
  calc
    (∑ i ∈ (Finset.range n).erase k, f i) =
        ∑ i ∈ (Finset.range n).filter (fun i => i ≠ k), f i := by
      congr 1
      ext i
      simp [and_comm]
    _ = ∑ i ∈ Finset.range n, if i ≠ k then f i else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ Finset.range n, if i = k then 0 else f i := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hik : i = k <;> simp [hik]

/-- Converse to `pelletAt_bound`: a strict inequality between the exact real
casts of the dyadic bounds makes the executable Boolean check succeed. -/
theorem pelletAt_of_bound {cs : Array Hex.GaussDyadic} {k : ℕ}
    {rlo rhi : _root_.Dyadic} (hk : k < cs.size)
    (hbound :
      (∑ i ∈ (Finset.range cs.size).erase k,
          Dyadic.toReal (Hex.GaussDyadic.hi (cs.getD i (0, 0))) *
            Dyadic.toReal rhi ^ i) <
        Dyadic.toReal (Hex.GaussDyadic.lo (cs.getD k (0, 0))) *
          Dyadic.toReal rlo ^ k) :
    Hex.pelletAt cs k rlo rhi = true := by
  unfold Hex.pelletAt
  rw [if_pos hk]
  apply decide_eq_true
  apply Dyadic.toReal_lt_toReal_iff.mp
  let result := (List.range cs.size).foldl
      (fun acc i =>
        let acc' := if i = k then acc.1
          else acc.1 + Hex.GaussDyadic.hi (cs.getD i (0, 0)) * acc.2
        (acc', acc.2 * rhi))
      ((0 : _root_.Dyadic), (1 : _root_.Dyadic))
  change Dyadic.toReal result.1 <
    Dyadic.toReal (Hex.GaussDyadic.lo (cs.getD k (0, 0)) * rlo ^ k)
  rw [show Dyadic.toReal result.1 =
      (∑ i ∈ Finset.range cs.size,
        if i = k then 0 else
          Dyadic.toReal (Hex.GaussDyadic.hi (cs.getD i (0, 0))) *
            Dyadic.toReal rhi ^ i) from (pelletFold cs k rhi cs.size).1]
  simpa only [Dyadic.toReal_mul, Dyadic.toReal_pow,
    sum_erase_range] using hbound

/-- A factor-two exact-norm margin absorbs both Gaussian-dyadic coefficient
bounds. The two radii may differ, matching the executable lower radius on
the dominant term and upper radius on the omitted tail. -/
theorem pelletAt_one_of_slack {p : Hex.ZPoly} {c : Hex.GaussDyadic}
    {rlo rhi : _root_.Dyadic}
    (hsize : 1 < p.size) (hrlo : 0 ≤ Dyadic.toReal rlo)
    (hrhi : 0 ≤ Dyadic.toReal rhi)
    (hslack :
      2 * (∑ i ∈ (Finset.range p.size).erase 1,
          ‖((toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))).coeff i‖ *
            Dyadic.toReal rhi ^ i) <
        ‖((toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))).coeff 1‖ *
          Dyadic.toReal rlo) :
    Hex.pelletAt (Hex.taylor p c) 1 rlo rhi = true := by
  let q := (toPolyℂ p).comp (X + C (GaussDyadic.toComplex c))
  let S := ∑ i ∈ (Finset.range p.size).erase 1,
    ‖q.coeff i‖ * Dyadic.toReal rhi ^ i
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have htail :
      (∑ i ∈ (Finset.range p.size).erase 1,
          Dyadic.toReal
              (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) *
            Dyadic.toReal rhi ^ i) ≤ √2 * S := by
    calc
      (∑ i ∈ (Finset.range p.size).erase 1,
          Dyadic.toReal
              (Hex.GaussDyadic.hi ((Hex.taylor p c).getD i (0, 0))) *
            Dyadic.toReal rhi ^ i) ≤
        ∑ i ∈ (Finset.range p.size).erase 1,
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
      (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 1 (0, 0))) := by
    rw [GaussDyadic.toReal_lo]
    positivity
  have hmain : ‖q.coeff 1‖ ≤
      √2 * Dyadic.toReal
        (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 1 (0, 0))) := by
    dsimp [q]
    rw [show ((toPolyℂ p).comp
        (X + C (GaussDyadic.toComplex c))).coeff 1 =
          GaussDyadic.toComplex ((Hex.taylor p c).getD 1 (0, 0)) by
      exact (taylor_coeff p c 1).symm]
    exact GaussDyadic.norm_le_sqrt_two_mul_lo _
  have hsqrt : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hstrict : √2 * S <
      Dyadic.toReal (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 1 (0, 0))) *
        Dyadic.toReal rlo := by
    have hmain_mul : ‖q.coeff 1‖ * Dyadic.toReal rlo ≤
        (√2 * Dyadic.toReal
          (Hex.GaussDyadic.lo ((Hex.taylor p c).getD 1 (0, 0)))) *
            Dyadic.toReal rlo := mul_le_mul_of_nonneg_right hmain hrlo
    dsimp [q, S] at hslack ⊢
    nlinarith
  apply pelletAt_of_bound (by simpa only [Hex.taylor_size] using hsize)
  simpa only [Hex.taylor_size, pow_one] using htail.trans_lt hstrict

/-- Coefficient-mass form of the strengthened Pellet converse. It allows
different upper-tail and lower-dominant radii and an arbitrary nonnegative
slack multiplier. Item 27 uses `L = 2`. -/
private theorem pellet_one_normalized_slack {g : ℂ[X]} {a : ℂ} {n : ℕ}
    {R r E L : ℝ} (hn : 0 < n) (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hL : 0 ≤ L) (hdeg : g.natDegree < n) (hg0 : g.coeff 0 = 1)
    (hmass : coeffMass g n R ≤ 1 + E) (hone : ‖g.coeff 1‖ * R ≤ E)
    (hmargin :
      L * ‖a‖ + (L * R + (2 * L + 1) * ‖a‖) * E < r) :
    L * (∑ i ∈ (Finset.range (n + 1)).erase 1,
        ‖((X - C a) * g).coeff i‖ * R ^ i) <
      ‖((X - C a) * g).coeff 1‖ * r := by
  let h := (X - C a) * g
  have hE : 0 ≤ E :=
    (mul_nonneg (norm_nonneg (g.coeff 1)) hR).trans hone
  have hfactor : 0 ≤ R + ‖a‖ := add_nonneg hR (norm_nonneg a)
  have htotal : coeffMass h (n + 1) R ≤ (R + ‖a‖) * (1 + E) :=
    (coeffMass_X_sub_C_mul_le hR hdeg).trans
      (mul_le_mul_of_nonneg_left hmass hfactor)
  have hcoeff : h.coeff 1 = 1 - a * g.coeff 1 := by
    dsimp [h]
    rw [coeff_X_sub_C_mul, hg0]
  have hreverse :
      1 - ‖a‖ * ‖g.coeff 1‖ ≤ ‖h.coeff 1‖ := by
    rw [hcoeff]
    simpa only [norm_one, norm_mul] using
      (norm_sub_norm_le (1 : ℂ) (a * g.coeff 1))
  have hmain (t : ℝ) (ht : 0 ≤ t) (htR : t ≤ R) :
      t - ‖a‖ * E ≤ ‖h.coeff 1‖ * t := by
    have hone_t : ‖g.coeff 1‖ * t ≤ E :=
      (mul_le_mul_of_nonneg_left htR (norm_nonneg (g.coeff 1))).trans hone
    have hscaled : ‖a‖ * (‖g.coeff 1‖ * t) ≤ ‖a‖ * E :=
      mul_le_mul_of_nonneg_left hone_t (norm_nonneg a)
    calc
      t - ‖a‖ * E ≤ t - ‖a‖ * (‖g.coeff 1‖ * t) :=
        sub_le_sub_left hscaled t
      _ = (1 - ‖a‖ * ‖g.coeff 1‖) * t := by ring
      _ ≤ ‖h.coeff 1‖ * t := mul_le_mul_of_nonneg_right hreverse ht
  have hone_mem : 1 ∈ Finset.range (n + 1) := by simp [hn]
  have hdecomp :
      (∑ i ∈ (Finset.range (n + 1)).erase 1,
          ‖h.coeff i‖ * R ^ i) + ‖h.coeff 1‖ * R =
        coeffMass h (n + 1) R := by
    unfold coeffMass
    simpa only [pow_one] using
      (Finset.sum_erase_add (Finset.range (n + 1))
        (fun i => ‖h.coeff i‖ * R ^ i) hone_mem)
  have hmainR := hmain R hR le_rfl
  have hmainr := hmain r hr hrR
  change L * (∑ i ∈ (Finset.range (n + 1)).erase 1,
      ‖h.coeff i‖ * R ^ i) < ‖h.coeff 1‖ * r
  nlinarith [norm_nonneg a]

/-- Strengthened translation form of the exact Pellet converse. The
multiplier and the two radii make the coefficient slack required by an
executable enclosure explicit; `pelletAt_one_of_slack` consumes the case
`L = 2`. -/
theorem pellet_one_comp_slack {p : ℂ[X]} {c z : ℂ} {s : Multiset ℂ}
    {d R r L : ℝ} (hp : p ≠ 0) (hroots : p.roots = z ::ₘ s) (hd : 0 < d)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R) (hL : 0 ≤ L)
    (hremote : ∀ w ∈ s, d ≤ ‖w - c‖)
    (hmargin :
      L * ‖z - c‖ +
          (L * R + (2 * L + 1) * ‖z - c‖) *
            ((1 + R / d) ^ s.card - 1) < r) :
    L * (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
        ‖(p.comp (X + C c)).coeff i‖ * R ^ i) <
      ‖(p.comp (X + C c)).coeff 1‖ * r := by
  let q := p.comp (X + C c)
  let t := s.map fun w => w - c
  let a := z - c
  let g := remotePoly (t.map Inv.inv)
  let h := (X - C a) * g
  let K := q.leadingCoeff * (t.map Neg.neg).prod
  have hq : q ≠ 0 := (comp_X_add_C_ne_zero_iff (p := p) (t := c)).mpr hp
  have hqroots : q.roots = a ::ₘ t := by
    have htranslate : q.roots = p.roots.map fun w => w - c := by
      dsimp [q]
      convert roots_comp_C_mul_X_add_C p 1 c isUnit_one using 1 <;> simp
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
  have hgdeg : g.natDegree < t.card + 1 := by
    dsimp [g]
    have hdegree := natDegree_remotePoly_le (t.map Inv.inv)
    simpa using Nat.lt_succ_of_le hdegree
  have hgdom :
      L * (∑ i ∈ (Finset.range (t.card + 2)).erase 1,
          ‖h.coeff i‖ * R ^ i) < ‖h.coeff 1‖ * r := by
    apply pellet_one_normalized_slack (n := t.card + 1)
      (E := (1 + R / d) ^ t.card - 1) (by omega) hR hr hrR hL hgdeg
    · exact coeff_remotePoly_zero _
    · dsimp [g]
      calc
        coeffMass (remotePoly (t.map Inv.inv)) (t.card + 1) R ≤
            (1 + R / d) ^ t.card := coeffMass_remotePoly_le hd hR hremote'
        _ = 1 + ((1 + R / d) ^ t.card - 1) := by ring
    · dsimp [g]
      exact coeff_one_remotePoly_le hd hR hremote'
    · simpa [a, t] using hmargin
  change L * (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
      ‖q.coeff i‖ * R ^ i) < ‖q.coeff 1‖ * r
  rw [hfactor]
  simp only [coeff_C_mul, norm_mul]
  calc
    L * (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
        (‖K‖ * ‖h.coeff i‖) * R ^ i) =
      ‖K‖ * (L * ∑ i ∈ (Finset.range (t.card + 2)).erase 1,
        ‖h.coeff i‖ * R ^ i) := by
      dsimp [t]
      simp only [Multiset.card_map]
      calc
        L * (∑ i ∈ (Finset.range (s.card + 2)).erase 1,
            (‖K‖ * ‖h.coeff i‖) * R ^ i) =
          L * (‖K‖ * ∑ i ∈ (Finset.range (s.card + 2)).erase 1,
            ‖h.coeff i‖ * R ^ i) := by
          apply congrArg (fun x : ℝ => L * x)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ‖K‖ * (L * ∑ i ∈ (Finset.range (s.card + 2)).erase 1,
            ‖h.coeff i‖ * R ^ i) := by ring
    _ < ‖K‖ * (‖h.coeff 1‖ * r) :=
      mul_lt_mul_of_pos_left hgdom (norm_pos_iff.mpr hK)
    _ = (‖K‖ * ‖h.coeff 1‖) * r := by ring

/-- A wide one-root isolation satisfying the explicit enclosure margin at
the base, doubled, and quadrupled radii makes the actual executable Pellet
witness succeed. The remote multiset retains root multiplicity. -/
theorem witness_one_of_roots {p : Hex.ZPoly} {sq : Hex.DyadicSquare}
    {z : ℂ} {roots : Multiset ℂ} {d : ℝ}
    (hp : toPolyℂ p ≠ 0) (hsize : 1 < p.size)
    (hroots : (toPolyℂ p).roots = z ::ₘ roots) (hd : 0 < d)
    (hremote : ∀ w ∈ roots,
      d ≤ ‖w - GaussDyadic.toComplex sq.center‖)
    (hmargin : ∀ j : ℕ, j < 3 →
      let rlo := Dyadic.toReal (sq.radiusLo <<< (j : Int))
      let rhi := Dyadic.toReal (sq.radiusHi <<< (j : Int))
      2 * ‖z - GaussDyadic.toComplex sq.center‖ +
          (2 * rhi + 5 * ‖z - GaussDyadic.toComplex sq.center‖) *
            ((1 + rhi / d) ^ roots.card - 1) < rlo) :
    Hex.witness p sq 1 := by
  have hsize_eq : p.size = roots.card + 2 := by
    have hnat := natDegree_eq_of_roots hroots
    rw [natDegree_toPolyℂ] at hnat
    have hdegree : p.degree? = some (p.size - 1) := by
      have hpos : 0 < p.size := by omega
      simp [Hex.DensePoly.degree?, Nat.ne_of_gt hpos]
    rw [hdegree, Option.getD_some] at hnat
    omega
  have hrlo : 0 < Dyadic.toReal sq.radiusLo := by
    simp only [Hex.DyadicSquare.radiusLo, Dyadic.toReal_ofIntWithPrec]
    positivity
  have hrhi : 0 < Dyadic.toReal sq.radiusHi := by
    simp only [Hex.DyadicSquare.radiusHi, Dyadic.toReal_ofIntWithPrec]
    positivity
  have hlohi : Dyadic.toReal sq.radiusLo ≤ Dyadic.toReal sq.radiusHi :=
    (DyadicSquare.radiusLo_lt_radius sq).trans
      (DyadicSquare.radius_lt_radiusHi sq) |>.le
  have hcheck (j : ℕ) (hj : j < 3) :
      Hex.pelletAt (Hex.taylor p sq.center) 1
        (sq.radiusLo <<< (j : Int)) (sq.radiusHi <<< (j : Int)) = true := by
    have hpow : 0 < (2 : ℝ) ^ (j : Int) := zpow_pos (by norm_num) _
    have hrlo_j : 0 ≤ Dyadic.toReal (sq.radiusLo <<< (j : Int)) := by
      rw [Dyadic.toReal_shiftLeft]
      exact mul_nonneg hrlo.le hpow.le
    have hrhi_j : 0 ≤ Dyadic.toReal (sq.radiusHi <<< (j : Int)) := by
      rw [Dyadic.toReal_shiftLeft]
      exact mul_nonneg hrhi.le hpow.le
    have hle_j : Dyadic.toReal (sq.radiusLo <<< (j : Int)) ≤
        Dyadic.toReal (sq.radiusHi <<< (j : Int)) := by
      rw [Dyadic.toReal_shiftLeft, Dyadic.toReal_shiftLeft]
      exact mul_le_mul_of_nonneg_right hlohi hpow.le
    apply pelletAt_one_of_slack hsize hrlo_j hrhi_j
    have hslack := pellet_one_comp_slack hp hroots hd hrhi_j hrlo_j hle_j
      (by norm_num : (0 : ℝ) ≤ 2) hremote (by
        have hm := hmargin j hj
        norm_num at hm ⊢
        exact hm)
    simpa only [hsize_eq] using hslack
  have shift_zero (x : _root_.Dyadic) : x <<< (0 : Int) = x := by
    cases x with
    | zero => rfl
    | ofOdd n k hn =>
        show _root_.Dyadic.ofOdd n (k - 0) hn = _
        rw [sub_zero]
  have hcheck0 :
      Hex.pelletAt (Hex.taylor p sq.center) 1 sq.radiusLo sq.radiusHi = true := by
    simpa only [Int.ofNat_zero, shift_zero] using hcheck 0 (by omega)
  unfold Hex.witness Hex.witnessCheck
  simpa [Bool.and_eq_true] using
    ⟨⟨hcheck0, hcheck 1 (by omega)⟩, hcheck 2 (by omega)⟩

end

end HexRootsMathlib
