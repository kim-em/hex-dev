/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Basic
public import HexResultant.ExactDiv

public section

/-!
Algebraic transport laws for fraction-free pseudo-division.

The executable coefficient recurrence in `HexResultant.Basic` already proves
reconstruction and the quotient/remainder size bounds.  This module adds the
uniqueness theorem that characterizes those outputs and uses it to derive the
two scalar homogeneity laws needed by the Brown--Traub development.
-/
namespace Hex.DensePoly

universe u

variable {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S]

variable [Div S] [ExactDivLaws S]

/-- Powers distribute over multiplication in the lightweight commutative ring. -/
private theorem mul_pow {T : Type u} [Lean.Grind.CommRing T]
    (a b : T) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by
      rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero,
        Lean.Grind.Semiring.pow_zero]
      exact (Lean.Grind.Semiring.mul_one 1).symm
  | n + 1 => by
      rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ,
        Lean.Grind.Semiring.pow_succ, mul_pow a b n]
      grind

/-- Below a positive-degree divisor, a strict dense-size bound gives the
corresponding default-degree bound. -/
private theorem degree_lt_of_size_lt {T : Type u} [Lean.Grind.CommRing T]
    [DecidableEq T] (p g : DensePoly T)
    (hg : 1 < g.size) (hp : p.size < g.size) :
    p.degree?.getD 0 < g.degree?.getD 0 := by
  rw [degree?_eq_some_of_pos_size g (by omega), Option.getD_some]
  by_cases hp0 : p.size = 0
  · rw [(degree?_eq_none_iff p).2 hp0, Option.getD_none]
    omega
  · rw [degree?_eq_some_of_pos_size p (Nat.pos_of_ne_zero hp0),
      Option.getD_some]
    omega

/-- Reconstruction and the strict remainder bound uniquely characterize
`pseudoDivMod` on an ordered nonzero input pair. -/
theorem pseudoDivMod_unique (f g q r : DensePoly S) (hg : g ≠ 0)
    (hgf : g.size ≤ f.size)
    (hrec : scale (g.leadingCoeff ^ (f.size - g.size + 1)) f = q * g + r)
    (hr : r.size < g.size) :
    pseudoDivMod f g = (q, r) := by
  rcases hqr : pseudoDivMod f g with ⟨q', r'⟩
  have hrec' :
      scale (g.leadingCoeff ^ (f.size - g.size + 1)) f = q' * g + r' := by
    simpa only [hqr] using pseudoDivMod_reconstruct f g hg hgf
  have hr' : r'.size < g.size := by
    simpa only [hqr] using pseudoDivMod_remainder_lt f g hg
  have hg_pos : 0 < g.size := by
    exact Nat.pos_of_ne_zero fun hzero =>
      hg ((size_eq_zero_iff g).mp hzero)
  by_cases hg_const : g.size = 1
  · have hr0 : r = 0 := (size_eq_zero_iff r).mp (by omega)
    have hr'0 : r' = 0 := (size_eq_zero_iff r').mp (by omega)
    have hmul : q' * g = q * g := by
      rw [hr0, DensePoly.add_zero_poly] at hrec
      rw [hr'0, DensePoly.add_zero_poly] at hrec'
      exact hrec'.symm.trans hrec
    have hq : q' = q :=
      ExactDivLaws.mul_right_cancel (R := DensePoly S) hg hmul
    exact Prod.ext hq (hr'0.trans hr0.symm)
  · have hg_big : 1 < g.size := by omega
    have hg_deg : 0 < g.degree?.getD 0 := by
      rw [degree?_eq_some_of_pos_size g hg_pos, Option.getD_some]
      omega
    have hr_deg := degree_lt_of_size_lt r g hg_big hr
    have hr'_deg := degree_lt_of_size_lt r' g hg_big hr'
    have hmul : (q - q') * g = r' - r := by
      rw [sub_mul_poly q q' g]
      apply ext_coeff
      intro n
      have heq : (q * g).coeff n + r.coeff n =
          (q' * g).coeff n + r'.coeff n := by
        have h := congrArg (fun p : DensePoly S => p.coeff n)
          (hrec.symm.trans hrec')
        simpa only [coeff_add_semiring] using h
      simp only [coeff_sub_ring]
      grind
    have hdeg : (r' - r).degree?.getD 0 < g.degree?.getD 0 :=
      degree_getD_sub_lt r' r g hg_deg hr'_deg hr_deg
    have hlc : g.leadingCoeff ≠ (0 : S) :=
      leadingCoeff_ne_zero_of_pos_size g hg_pos
    have hA : divMod (r' - r) g = (q - q', 0) :=
      divMod_eq_of_polynomial_mul (r' - r) g (q - q') hg
        (fun a => ExactDivLaws.mul_div_cancel_right a g.leadingCoeff hlc)
        (fun _ ha => ExactDivLaws.mul_ne_zero ha hlc) hmul
    have hB : divMod (r' - r) g = (0, r' - r) :=
      divMod_eq_zero_self_of_degree_lt (r' - r) g hdeg
    rw [hA] at hB
    have hqq : q - q' = 0 := (Prod.mk.injEq _ _ _ _ ▸ hB).1
    have hrr : (0 : DensePoly S) = r' - r :=
      (Prod.mk.injEq _ _ _ _ ▸ hB).2
    have hq : q' = q := by
      apply ext_coeff
      intro n
      have h := congrArg (fun p : DensePoly S => p.coeff n) hqq
      rw [coeff_sub_ring, coeff_zero] at h
      grind
    have hremainder : r' = r := by
      apply ext_coeff
      intro n
      have h := congrArg (fun p : DensePoly S => p.coeff n) hrr.symm
      rw [coeff_sub_ring, coeff_zero] at h
      grind
    exact Prod.ext hq hremainder

/-- Scaling the dividend scales both pseudo-division outputs. -/
theorem pseudoDivMod_scale_left (f g : DensePoly S) {a : S} (ha : a ≠ 0)
    (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    pseudoDivMod (scale a f) g =
      (scale a (pseudoDivMod f g).1, scale a (pseudoDivMod f g).2) := by
  let q := (pseudoDivMod f g).1
  let r := (pseudoDivMod f g).2
  have hfsize : (scale a f).size = f.size := size_scale ha f
  have hrec := pseudoDivMod_reconstruct f g hg hgf
  have hcandidate :
      scale (g.leadingCoeff ^ ((scale a f).size - g.size + 1)) (scale a f) =
        scale a q * g + scale a r := by
    rw [hfsize, scale_scale, show g.leadingCoeff ^ (f.size - g.size + 1) * a =
        a * g.leadingCoeff ^ (f.size - g.size + 1) by grind,
      ← scale_mul a q g,
      ← scale_add, ← hrec, scale_scale]
  apply pseudoDivMod_unique (scale a f) g (scale a q) (scale a r) hg
    (by omega) hcandidate
  have hr : r.size < g.size := by
    simpa only [r] using pseudoDivMod_remainder_lt f g hg
  have hle : (scale a r).size ≤ r.size := by
    rw [scale_eq_scaleImpl]
    exact size_scaleImpl_le a r
  omega

/-- Scaling the divisor by `a` scales the pseudo-quotient by `a^(d-1)` and
the pseudo-remainder by `a^d`, where `d` is the number of cancellation rounds. -/
theorem pseudoDivMod_scale_right (f g : DensePoly S) {a : S} (ha : a ≠ 0)
    (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let d := f.size - g.size + 1
    pseudoDivMod f (scale a g) =
      (scale (a ^ (d - 1)) (pseudoDivMod f g).1,
        scale (a ^ d) (pseudoDivMod f g).2) := by
  let d := f.size - g.size + 1
  let q := (pseudoDivMod f g).1
  let r := (pseudoDivMod f g).2
  have hgscale : scale a g ≠ 0 := by
    intro hzero
    have hsize := congrArg DensePoly.size hzero
    rw [size_scale ha g, size_zero] at hsize
    exact hg ((size_eq_zero_iff g).mp hsize)
  have hgsize : (scale a g).size = g.size := size_scale ha g
  have hlc : (scale a g).leadingCoeff = a * g.leadingCoeff :=
    leadingCoeff_scale ha g
  have hrec := pseudoDivMod_reconstruct f g hg hgf
  have hdpos : 0 < d := by
    dsimp only [d]
    omega
  have hpow : a ^ (d - 1) * a = a ^ d := by
    rw [← Lean.Grind.Semiring.pow_succ]
    exact congrArg (fun n : Nat => a ^ n) (by omega)
  have hcandidate :
      scale ((scale a g).leadingCoeff ^ (f.size - (scale a g).size + 1)) f =
        scale (a ^ (d - 1)) q * scale a g + scale (a ^ d) r := by
    rw [hgsize, hlc]
    change scale ((a * g.leadingCoeff) ^ d) f = _
    calc
      scale ((a * g.leadingCoeff) ^ d) f =
          scale (a ^ d * g.leadingCoeff ^ d) f := by rw [mul_pow]
      _ = scale (a ^ d) (scale (g.leadingCoeff ^ d) f) := by
        rw [scale_scale]
      _ = scale (a ^ d) (q * g + r) := by
        have hrec' : scale (g.leadingCoeff ^ d) f = q * g + r := by
          simpa only [d, q, r] using hrec
        rw [hrec']
      _ = scale (a ^ d) (q * g) + scale (a ^ d) r :=
        scale_add (a ^ d) (q * g) r
      _ = scale (a ^ (d - 1)) (scale a (q * g)) + scale (a ^ d) r := by
        rw [scale_scale, hpow]
      _ = scale (a ^ (d - 1)) (q * scale a g) + scale (a ^ d) r := by
        rw [mul_scale a q g]
      _ = scale (a ^ (d - 1)) q * scale a g + scale (a ^ d) r := by
        rw [scale_mul (a ^ (d - 1)) q (scale a g)]
  dsimp only
  apply pseudoDivMod_unique f (scale a g)
    (scale (a ^ (d - 1)) q) (scale (a ^ d) r) hgscale
    (by omega) hcandidate
  have hr : r.size < g.size := by
    simpa only [r] using pseudoDivMod_remainder_lt f g hg
  have hle : (scale (a ^ d) r).size ≤ r.size := by
    rw [scale_eq_scaleImpl]
    exact size_scaleImpl_le (a ^ d) r
  omega

end Hex.DensePoly
