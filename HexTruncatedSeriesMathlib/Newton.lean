/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeriesMathlib.Ops
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Substitution

public section

/-!
Correspondence between the executable bounded algorithms and Mathlib power
series operations.
-/

noncomputable section

namespace HexTruncatedSeriesMathlib

open Hex Hex.TSeries
open scoped BigOperators

universe u

variable {R : Type u} {n : Nat}

private theorem one_add_X_mul_geom [CommRing R] [Algebra ℚ R] :
    (1 + PowerSeries.X) *
        PowerSeries.mk (fun k => algebraMap ℚ R ((-1 : ℚ) ^ k)) = 1 := by
  apply PowerSeries.ext
  intro k
  rw [add_mul, _root_.one_mul, map_add]
  cases k with
  | zero =>
      simp [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_one]
  | succ k =>
      rw [PowerSeries.coeff_mk,
        show PowerSeries.coeff (k + 1)
            (PowerSeries.X *
              PowerSeries.mk (fun j => algebraMap ℚ R ((-1 : ℚ) ^ j))) =
            algebraMap ℚ R ((-1 : ℚ) ^ k) by
          simp,
        PowerSeries.coeff_one, if_neg (by omega), ← map_add]
      rw [_root_.pow_succ]
      simp

/-- Truncation carries Mathlib's unit-certified inverse to executable Newton
inversion. -/
theorem ofPowerSeries_invOfUnit [CommRing R] (f : PowerSeries R) (u : Rˣ)
    (hu : PowerSeries.constantCoeff f = u) :
    ofPowerSeries (n := n) (f.invOfUnit u) =
      invOfUnit (ofPowerSeries f) (u⁻¹ : Rˣ) := by
  by_cases hn : n = 0
  · apply Hex.TSeries.ext
    intro _ hi
    omega
  · apply invOfUnit_unique (a := ofPowerSeries f)
      (u := ((u⁻¹ : Rˣ) : R))
    · rw [coeff_ofPowerSeries f 0 (by omega),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hu]
      simp
    · have hmul := congrArg (ofPowerSeriesHom (R := R) (n := n))
        (PowerSeries.mul_invOfUnit f u hu)
      simpa only [RingHom.map_mul, RingHom.map_one,
        ofPowerSeriesHom_apply] using hmul

/-- Truncation carries Mathlib substitution by a zero-constant series to
executable composition. -/
theorem ofPowerSeries_subst [CommRing R] (f g : PowerSeries R)
    (hg : PowerSeries.constantCoeff g = 0) :
    ofPowerSeries (n := n) (f.subst g) =
      comp (ofPowerSeries f) (ofPowerSeries g) := by
  apply Hex.TSeries.ext
  intro i hi
  have hg0 : (ofPowerSeries (n := n) g).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_ofPowerSeries g 0 hn,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hg]
    · unfold Hex.TSeries.coeff
      rw [dif_neg hn]
  rw [coeff_ofPowerSeries (f.subst g) i hi, comp_spec _ _ hg0,
    coeff_foldl_add (List.range n)
      (fun k => C ((ofPowerSeries (n := n) f).coeff k) *
        (ofPowerSeries (n := n) g).pow k) 0 i hi,
    Hex.TSeries.coeff_zero]
  have hsubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg
  rw [PowerSeries.coeff_subst' hsubst]
  have hsupp : Function.support
      (fun d : Nat => PowerSeries.coeff d f • PowerSeries.coeff i (g ^ d)) ⊆
      (Finset.range n : Set Nat) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hdn
    have hid : i < d := by omega
    have hid' : (i : ℕ∞) < (d : ℕ∞) := by exact_mod_cast hid
    have hord := PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg
    have hz := PowerSeries.coeff_of_lt_order i (lt_of_lt_of_le hid' hord)
    simp [hz] at hd
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  let term := fun k : Nat =>
    (C ((ofPowerSeries (n := n) f).coeff k) *
      (ofPowerSeries (n := n) g).pow k).coeff i
  symm
  calc
    (List.range n).foldl (fun acc k => acc + term k) 0 =
        ((List.range n).map term).sum := by
          rw [List.sum_eq_foldl, List.foldl_map]
    _ = ∑ k ∈ (List.range n).toFinset, term k :=
      (List.sum_toFinset _ List.nodup_range).symm
    _ = ∑ k ∈ Finset.range n, term k := by
      congr 1
      ext k
      simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
    _ = ∑ k ∈ Finset.range n,
        PowerSeries.coeff k f • PowerSeries.coeff i (g ^ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [term]
      have hk' : k < n := Finset.mem_range.mp hk
      rw [coeff_ofPowerSeries f k hk', Hex.TSeries.coeff_C_mul _ _ i hi]
      have hpowCore (q : Nat) :
          (ofPowerSeries (n := n) g).pow q =
            ofPowerSeries (n := n) (g ^ q) := by
        induction q with
        | zero =>
            calc
              (ofPowerSeries (n := n) g).pow 0 = 1 :=
                Hex.TSeries.pow_zero _
              _ = ofPowerSeries (n := n) 1 := by
                exact ((ofPowerSeriesHom (R := R) (n := n)).map_one).symm
              _ = ofPowerSeries (n := n) (g ^ 0) := by rw [_root_.pow_zero]
        | succ q ih =>
            calc
              (ofPowerSeries (n := n) g).pow (q + 1) =
                  (ofPowerSeries (n := n) g).pow q * ofPowerSeries g :=
                Hex.TSeries.pow_succ _ q
              _ = ofPowerSeries (n := n) (g ^ q) * ofPowerSeries g := by rw [ih]
              _ = ofPowerSeries (n := n) (g ^ q * g) := by
                exact ((ofPowerSeriesHom (R := R) (n := n)).map_mul (g ^ q) g).symm
              _ = ofPowerSeries (n := n) (g ^ (q + 1)) := by rw [_root_.pow_succ]
      rw [hpowCore k, coeff_ofPowerSeries (g ^ k) i hi]
      simp

/-- Truncation carries Mathlib's compositional inverse to executable Newton
reversion. -/
theorem ofPowerSeries_substInvOfIsUnit [CommRing R] (g : PowerSeries R)
    (h0 : PowerSeries.constantCoeff g = 0)
    (hu : IsUnit (PowerSeries.coeff 1 g)) :
    ofPowerSeries (n := n) (g.substInvOfIsUnit hu) =
      revOfUnit (ofPowerSeries g) ((hu.unit⁻¹ : Rˣ) : R) := by
  by_cases hn : 1 < n
  · let y := ofPowerSeries (n := n) (g.substInvOfIsUnit hu)
    let b := ofPowerSeries (n := n) g
    let v : R := ((hu.unit⁻¹ : Rˣ) : R)
    have hb0 : b.coeff 0 = 0 := by
      dsimp only [b]
      rw [coeff_ofPowerSeries g 0 (by omega),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    have hy0 : y.coeff 0 = 0 := by
      dsimp only [y]
      rw [coeff_ofPowerSeries _ 0 (by omega),
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_substInvOfIsUnit]
    have hb1 : b.coeff 1 * v = 1 := by
      dsimp only [b, v]
      rw [coeff_ofPowerSeries g 1 hn]
      have huval : ((hu.unit : Rˣ) : R) = PowerSeries.coeff 1 g := hu.unit_spec
      calc
        PowerSeries.coeff 1 g * ((hu.unit⁻¹ : Rˣ) : R) =
            ((hu.unit : Rˣ) : R) * ((hu.unit⁻¹ : Rˣ) : R) := by
              rw [huval]
        _ = 1 := by simp
    have hleft : comp b y = Hex.TSeries.X := by
      have hps := PowerSeries.subst_substInvOfIsUnit_right g h0 hu
      have ht := congrArg (ofPowerSeries (n := n)) hps
      rw [ofPowerSeries_subst g (g.substInvOfIsUnit hu)
        (PowerSeries.constantCoeff_substInvOfIsUnit g hu), ofPowerSeries_X] at ht
      exact ht
    have hright : comp y b = Hex.TSeries.X := by
      have hps := PowerSeries.subst_substInvOfIsUnit_left g h0 hu
      have ht := congrArg (ofPowerSeries (n := n)) hps
      rw [ofPowerSeries_subst (g.substInvOfIsUnit hu) g h0,
        ofPowerSeries_X] at ht
      exact ht
    have hrev0 : (revOfUnit b v).coeff 0 = 0 :=
      revOfUnit_coeff_zero b v hb0 hb1
    have hrev := (revOfUnit_comp b v hb0 hb1).1
    calc
      y = comp y Hex.TSeries.X := (comp_X_right y).symm
      _ = comp y (comp b (revOfUnit b v)) := by rw [hrev]
      _ = comp (comp y b) (revOfUnit b v) :=
        (comp_assoc y b (revOfUnit b v) hb0 hrev0).symm
      _ = comp Hex.TSeries.X (revOfUnit b v) := by rw [hright]
      _ = revOfUnit b v := comp_X_left _ hrev0
  · by_cases hn0 : n = 0
    · apply Hex.TSeries.ext
      intro i hi
      omega
    · have hn1 : n = 1 := by omega
      subst n
      apply Hex.TSeries.ext
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rw [coeff_ofPowerSeries _ 0 (by omega),
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_substInvOfIsUnit]
      rw [revOfUnit_le_one (ofPowerSeries g) _ (by omega),
        Hex.TSeries.coeff_zero]

/-- Truncation carries Mathlib's formal exponential to the executable
truncated exponential. -/
theorem ofPowerSeries_exp [CommRing R] [Algebra ℚ R]
    [NatInverses R (n - 1)] (f : PowerSeries R)
    (h : PowerSeries.constantCoeff f = 0) :
    ofPowerSeries (n := n) ((PowerSeries.exp R).subst f) =
      exp (ofPowerSeries f) := by
  by_cases hnpos : 0 < n
  swap
  · apply Hex.TSeries.ext
    intro i hi
    omega
  let a := ofPowerSeries (n := n) f
  let y := ofPowerSeries (n := n) ((PowerSeries.exp R).subst f)
  have ha0 : a.coeff 0 = 0 := by
    dsimp only [a]
    rw [coeff_ofPowerSeries f 0 hnpos,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  have hyEq : y =
      comp (ofPowerSeries (n := n) (PowerSeries.exp R)) a := by
    dsimp only [y, a]
    exact ofPowerSeries_subst (PowerSeries.exp R) f h
  have hy0 : y.coeff 0 = 1 := by
    rw [hyEq, coeff_comp_zero _ a ha0]
    rw [coeff_ofPowerSeries _ 0 hnpos,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_exp]
  have hchain : PowerSeries.derivative R ((PowerSeries.exp R).subst f) =
      (PowerSeries.exp R).subst f * PowerSeries.derivative R f := by
    calc
      PowerSeries.derivative R ((PowerSeries.exp R).subst f) =
          (PowerSeries.derivative R (PowerSeries.exp R)).subst f *
            PowerSeries.derivative R f :=
        PowerSeries.derivative_subst
          (PowerSeries.HasSubst.of_constantCoeff_zero' h)
      _ = (PowerSeries.exp R).subst f * PowerSeries.derivative R f := by
        rw [PowerSeries.derivative_exp]
  have ht := congrArg (ofPowerSeriesHom (R := R) (n := n - 1)) hchain
  simp only [RingHom.map_mul, ofPowerSeriesHom_apply] at ht
  have hode : y.deriv =
      y.truncate (n - 1) (Nat.sub_le n 1) * a.deriv := by
    dsimp only [y, a]
    rw [deriv_ofPowerSeries, truncate_ofPowerSeries, deriv_ofPowerSeries]
    exact ht
  have hyu : y.coeff 0 * (1 : R) = 1 := by rw [hy0]; ring
  have hinv :
      y.truncate (n - 1) (Nat.sub_le n 1) *
          (invOfUnit y 1).truncate (n - 1) (Nat.sub_le n 1) = 1 := by
    have ht' := congrArg
      (fun z : TSeries R n => z.truncate (n - 1) (Nat.sub_le n 1))
      (invOfUnit_mul y 1 hyu)
    rw [truncate_mul, truncate_one] at ht'
    exact ht'
  have hyArg : (y - 1).coeff 0 = 0 := by
    rw [Hex.TSeries.coeff_sub y 1 0 hnpos,
      Hex.TSeries.coeff_one 0 hnpos, hy0]
    simp
  have hlogDeriv : (log y).deriv = a.deriv := by
    rw [deriv_log y hyArg, hode]
    calc
      (y.truncate (n - 1) (Nat.sub_le n 1) * a.deriv) *
          (invOfUnit y 1).truncate (n - 1) (Nat.sub_le n 1) =
          a.deriv * (y.truncate (n - 1) (Nat.sub_le n 1) *
            (invOfUnit y 1).truncate (n - 1) (Nat.sub_le n 1)) := by ring
      _ = a.deriv := by rw [hinv]; ring
  have hlog : log y = a := by
    apply eq_of_deriv
    · rw [log_coeff_zero y hyArg hnpos, ha0]
    · exact hlogDeriv
  have hexplog := exp_log y hyArg
  rw [hlog] at hexplog
  exact hexplog.symm

/-- Truncation carries Mathlib's formal logarithm to the executable truncated
logarithm. -/
theorem ofPowerSeries_logOf [CommRing R] [Algebra ℚ R]
    [NatInverses R (n - 1)] (f : PowerSeries R)
    (h : PowerSeries.constantCoeff f = 1) :
    ofPowerSeries (n := n) (PowerSeries.logOf f) =
      log (ofPowerSeries f) := by
  by_cases hn : 1 < n
  swap
  · by_cases hn0 : n = 0
    · apply Hex.TSeries.ext
      intro i hi
      omega
    · have hn1 : n = 1 := by omega
      subst n
      apply Hex.TSeries.ext
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      have ha0 : (ofPowerSeries (n := 1) f).coeff 0 = 1 := by
        rw [coeff_ofPowerSeries f 0 (by omega),
          PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
      have harg : ((ofPowerSeries (n := 1) f) - 1).coeff 0 = 0 := by
        rw [Hex.TSeries.coeff_sub _ _ 0 (by omega),
          Hex.TSeries.coeff_one 0 (by omega), ha0]
        simp
      rw [coeff_ofPowerSeries _ 0 (by omega),
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_logOf h]
      exact (log_coeff_zero (ofPowerSeries f) harg (by omega)).symm
  let q := f - 1
  let geom : PowerSeries R :=
    PowerSeries.mk (fun k => algebraMap ℚ R ((-1 : ℚ) ^ k))
  let g := geom.subst q
  let a := ofPowerSeries (n := n) f
  let ell := ofPowerSeries (n := n) (PowerSeries.logOf f)
  have hq0 : PowerSeries.constantCoeff q = 0 := by
    dsimp only [q]
    rw [map_sub, map_one, h]
    ring
  have hqSub : PowerSeries.HasSubst q :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hq0
  have hone : (1 : PowerSeries R).subst q = 1 := by
    rw [← PowerSeries.coe_substAlgHom hqSub]
    exact map_one (PowerSeries.substAlgHom hqSub)
  have hlinear : ((1 : PowerSeries R) + PowerSeries.X).subst q = f := by
    rw [PowerSeries.subst_add hqSub, PowerSeries.subst_X hqSub, hone]
    dsimp only [q]
    ring
  have hprodPS : f * g = 1 := by
    calc
      f * g = (((1 : PowerSeries R) + PowerSeries.X).subst q) *
          (geom.subst q) := by rw [hlinear]
      _ = ((((1 : PowerSeries R) + PowerSeries.X) * geom).subst q) := by
        rw [PowerSeries.subst_mul hqSub]
      _ = (1 : PowerSeries R).subst q := by
        rw [show ((1 : PowerSeries R) + PowerSeries.X) * geom = 1 by
          dsimp only [geom]
          exact one_add_X_mul_geom]
      _ = 1 := by
        simpa only [PowerSeries.coe_substAlgHom] using
          (map_one (PowerSeries.substAlgHom hqSub))
  have hchain : PowerSeries.derivative R (PowerSeries.logOf f) =
      g * PowerSeries.derivative R f := by
    rw [PowerSeries.logOf_eq]
    calc
      PowerSeries.derivative R ((PowerSeries.log R).subst q) =
          (PowerSeries.derivative R (PowerSeries.log R)).subst q *
            PowerSeries.derivative R q :=
        PowerSeries.derivative_subst hqSub
      _ = g * PowerSeries.derivative R q := by
        rw [PowerSeries.deriv_log]
      _ = g * PowerSeries.derivative R f := by
        dsimp only [q]
        simp
  have ha0 : a.coeff 0 = 1 := by
    dsimp only [a]
    rw [coeff_ofPowerSeries f 0 (by omega),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  have harg : (a - 1).coeff 0 = 0 := by
    rw [Hex.TSeries.coeff_sub _ _ 0 (by omega),
      Hex.TSeries.coeff_one 0 (by omega), ha0]
    simp
  let a' := a.truncate (n - 1) (Nat.sub_le n 1)
  let g' := ofPowerSeries (n := n - 1) g
  let ainv' := (invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1)
  have ha'0 : a'.coeff 0 * (1 : R) = 1 := by
    dsimp only [a']
    rw [Hex.TSeries.coeff_truncate _ (Nat.sub_le n 1) 0 (by omega), ha0]
    ring
  have hprod : a' * g' = 1 := by
    have ht := congrArg (ofPowerSeriesHom (R := R) (n := n - 1)) hprodPS
    simp only [RingHom.map_mul, RingHom.map_one, ofPowerSeriesHom_apply] at ht
    dsimp only [a', g', a]
    rw [truncate_ofPowerSeries]
    exact ht
  have hinvProd : a' * ainv' = 1 := by
    have ht := congrArg
      (fun z : TSeries R n => z.truncate (n - 1) (Nat.sub_le n 1))
      (invOfUnit_mul a 1 (by rw [ha0]; ring))
    rw [truncate_mul, truncate_one] at ht
    exact ht
  have hginv : g' = ainv' := by
    calc
      g' = invOfUnit a' 1 := invOfUnit_unique a' g' 1 ha'0 hprod
      _ = ainv' := (invOfUnit_unique a' ainv' 1 ha'0 hinvProd).symm
  have ht := congrArg (ofPowerSeriesHom (R := R) (n := n - 1)) hchain
  simp only [RingHom.map_mul, ofPowerSeriesHom_apply] at ht
  have hellDeriv : ell.deriv = g' * a.deriv := by
    dsimp only [ell, g', a]
    rw [deriv_ofPowerSeries, deriv_ofPowerSeries]
    exact ht
  have hderiv : ell.deriv = (log a).deriv := by
    rw [hellDeriv, deriv_log a harg]
    rw [hginv]
    dsimp only [ainv']
    ring
  apply eq_of_deriv
  · rw [coeff_ofPowerSeries _ 0 (by omega),
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_logOf h,
      log_coeff_zero a harg (by omega)]
  · exact hderiv

/-- A unit derivative at a chosen constant root gives exactly one square-root
lift in the full power-series ring. -/
theorem exists_unique_sq [CommRing R] (f : PowerSeries R) (r : R)
    (hr : r * r = PowerSeries.constantCoeff f) (hu : IsUnit (2 * r)) :
    ∃! s : PowerSeries R,
      s * s = f ∧ PowerSeries.constantCoeff s = r := by
  let v : R := ((hu.unit⁻¹ : Rˣ) : R)
  have hv : ((1 + 1) * r) * v = 1 := by
    have huval : ((hu.unit : Rˣ) : R) = 2 * r := hu.unit_spec
    dsimp only [v]
    calc
      ((1 + 1) * r) * ((hu.unit⁻¹ : Rˣ) : R) =
          (2 * r) * ((hu.unit⁻¹ : Rˣ) : R) := by ring
      _ = ((hu.unit : Rˣ) : R) * ((hu.unit⁻¹ : Rˣ) : R) := by rw [huval]
      _ = 1 := by simp
  let root : (m : Nat) → TSeries R m := fun m =>
    sqrtOfRoot (ofPowerSeries (n := m) f) r v
  have hrootSq (m : Nat) (hm : 0 < m) :
      root m * root m = ofPowerSeries (n := m) f := by
    dsimp only [root]
    apply sqrtOfRoot_sq
    · rw [coeff_ofPowerSeries f 0 hm,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hr
    · exact hv
  have hrootConst (m : Nat) (hm : 0 < m) :
      (root m).coeff 0 = r := by
    dsimp only [root]
    apply sqrtOfRoot_coeff_zero
    · rw [coeff_ofPowerSeries f 0 hm,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hr
    · exact hv
    · exact hm
  have hrootTruncate (m k : Nat) (hm : 0 < m) (hk : 0 < k)
      (hkm : k ≤ m) :
      (root m).truncate k hkm = root k := by
    apply sqrt_unique _ _ r v hv
    · rw [← truncate_mul, hrootSq m hm,
        truncate_ofPowerSeries f hkm, hrootSq k hk]
    · rw [Hex.TSeries.coeff_truncate _ hkm 0 hk, hrootConst m hm]
    · exact hrootConst k hk
  let s : PowerSeries R := PowerSeries.mk fun k => (root (k + 1)).coeff k
  have hsApprox (m : Nat) (hm : 0 < m) :
      ofPowerSeries (n := m) s = root m := by
    apply Hex.TSeries.ext
    intro i hi
    dsimp only [s]
    rw [coeff_ofPowerSeries _ i hi, PowerSeries.coeff_mk]
    have hc := congrArg (fun z : TSeries R (i + 1) => z.coeff i)
      (hrootTruncate m (i + 1) hm (by omega) (by omega))
    rw [Hex.TSeries.coeff_truncate _ (by omega) i (by omega)] at hc
    exact hc.symm
  have hsSq : s * s = f := by
    apply PowerSeries.ext
    intro k
    have heq : ofPowerSeries (n := k + 1) (s * s) =
        ofPowerSeries (n := k + 1) f := by
      calc
        ofPowerSeries (n := k + 1) (s * s) =
            ofPowerSeries (n := k + 1) s * ofPowerSeries (n := k + 1) s :=
          (ofPowerSeriesHom (R := R) (n := k + 1)).map_mul s s
        _ = root (k + 1) * root (k + 1) := by
          rw [hsApprox (k + 1) (by omega)]
        _ = ofPowerSeries (n := k + 1) f := hrootSq (k + 1) (by omega)
    have hc := congrArg (fun z : TSeries R (k + 1) => z.coeff k) heq
    rw [coeff_ofPowerSeries (s * s) k (by omega),
      coeff_ofPowerSeries f k (by omega)] at hc
    exact hc
  have hsConst : PowerSeries.constantCoeff s = r := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    dsimp only [s]
    rw [PowerSeries.coeff_mk]
    exact hrootConst 1 (by omega)
  refine ⟨s, ⟨hsSq, hsConst⟩, ?_⟩
  intro t ht
  apply PowerSeries.ext
  intro k
  have htSq : ofPowerSeries (n := k + 1) t *
      ofPowerSeries (n := k + 1) t = ofPowerSeries (n := k + 1) f := by
    have hm := congrArg (ofPowerSeriesHom (R := R) (n := k + 1)) ht.1
    simpa only [RingHom.map_mul, ofPowerSeriesHom_apply] using hm
  have htConst : (ofPowerSeries (n := k + 1) t).coeff 0 = r := by
    rw [coeff_ofPowerSeries t 0 (by omega),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ht.2]
  have htr : ofPowerSeries (n := k + 1) t = root (k + 1) :=
    sqrt_unique _ _ r v hv
      (htSq.trans (hrootSq (k + 1) (by omega)).symm)
      htConst (hrootConst (k + 1) (by omega))
  have hts : ofPowerSeries (n := k + 1) t =
      ofPowerSeries (n := k + 1) s :=
    htr.trans (hsApprox (k + 1) (by omega)).symm
  have hc := congrArg (fun z : TSeries R (k + 1) => z.coeff k) hts
  rw [coeff_ofPowerSeries t k (by omega),
    coeff_ofPowerSeries s k (by omega)] at hc
  exact hc

end HexTruncatedSeriesMathlib
