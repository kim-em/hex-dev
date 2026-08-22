/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Comp

public section

/-!
Compositional reversion of fixed-precision truncated series.

The primary route is Newton iteration and needs only an inverse of the linear
coefficient.  It composes the zero-padded derivative, inverts that denominator
with the same witness, and applies a bounded correction.  A direct Lagrange
formula is also provided under `NatInverses`; it is an independent conformance
route rather than the primary algorithm because its explicit `1/k` divisions
exclude valid integral reversions.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

attribute [local instance] Lean.Grind.Semiring.natCast

/-- One bounded Newton reversion update. -/
def revStep [Lean.Grind.CommRing R] (b : TSeries R n) (v : R)
    (y : TSeries R n) (m : Nat) : TSeries R n :=
  let numerator := compUpTo m b y - X
  let denominator := compUpTo m b.derivPad y
  let correction := mulUpTo m numerator (invUpTo m denominator v)
  let next := y - correction
  ofFn fun i => if i < m then next.coeff i else 0

/-- Revert through coefficient `m - 1`, zeroing all later coefficients. -/
def revUpTo [Lean.Grind.CommRing R] (m : Nat)
    (b : TSeries R n) (v : R) : TSeries R n :=
  let init := mulUpTo m (C v) X
  let y := newton (revStep b v) init (steps (min m n))
  ofFn fun i => if i < m then y.coeff i else 0

/-- The compositional inverse of `b`, given an inverse of its linear
coefficient. -/
def revOfUnit [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) : TSeries R n :=
  revUpTo n b v

/-- Check the constant coefficient and look up the linear inverse when that
coefficient is represented. -/
def rev? [Lean.Grind.CommRing R] [DecidableEq R] [UnitOps R]
    (b : TSeries R n) : Option (TSeries R n) :=
  if b.coeff 0 ≠ 0 then
    none
  else if n ≤ 1 then
    some 0
  else
    match UnitOps.inv? (R := R) (b.coeff 1) with
    | some v => some (revOfUnit b v)
    | none => none

/-- Direct Lagrange inversion.  This deliberately performs the explicit
division by `k` and therefore carries `NatInverses R (n-1)`. -/
def revLagrange [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (b : TSeries R n) (v : R) : TSeries R n :=
  let quotient : TSeries R n := ofFn fun i => b.coeff (i + 1)
  let xOverB := invOfUnit quotient v
  ofFn fun k =>
    if k = 0 then
      0
    else
      NatInverses.invNat (R := R) (m := n - 1) k *
        (xOverB.pow k).coeff (k - 1)

private def tangent [Lean.Grind.CommRing R]
    (y d : TSeries R n) (k : Nat) : TSeries R n :=
  if k = 0 then 0 else C ((k : Nat) : R) * y ^ (k - 1) * d

private theorem tangent_vanish [Lean.Grind.CommRing R]
    (y d : TSeries R n) (p k : Nat) (hd : Agree p d 0) :
    Agree p (tangent y d k) 0 := by
  unfold tangent
  split
  · exact Agree.refl p 0
  · have hm := Agree.mul
        (Agree.mul (Agree.refl p (C ((k : Nat) : R)))
          (Agree.refl p (y ^ (k - 1)))) hd
    simpa only [mul_zero] using hm

private theorem pow_taylor [Lean.Grind.CommRing R]
    (y d : TSeries R n) (p k : Nat) (hd : Agree p d 0) :
    Agree (p + p) ((y + d) ^ k) (y ^ k + tangent y d k) := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      unfold tangent
      rw [if_pos rfl, add_zero]
      exact Agree.refl (p + p) (1 : TSeries R n)
  | succ k ih =>
      rw [pow_succ]
      have hmul := Agree.mul ih (Agree.refl (p + p) (y + d))
      have halg :
          (y ^ k + tangent y d k) * (y + d) =
            (y ^ (k + 1) + tangent y d (k + 1)) + tangent y d k * d := by
        cases k with
        | zero =>
            simp [tangent, pow_zero, pow_succ,
              Lean.Grind.Semiring.natCast_one]
            grind
        | succ k =>
            unfold tangent
            simp only [Nat.add_sub_cancel]
            have hcast1 : (((k + 1 : Nat) : R)) = ((k : Nat) : R) + 1 := by
              rw [Lean.Grind.Semiring.natCast_succ]
            have hcast2 : (((k + 2 : Nat) : R)) = ((k : Nat) : R) + 1 + 1 := by
              rw [show k + 2 = (k + 1) + 1 by omega,
                Lean.Grind.Semiring.natCast_succ, hcast1]
            have hpow2 : y ^ (k + 2) = y ^ k * y * y := by
              rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, pow_succ]
            rw [hcast1, hcast2, hpow2, pow_succ]
            simp only [C_add, C_one]
            grind
      apply Agree.trans hmul
      rw [halg]
      have hquad := Agree.zeroMul (tangent_vanish y d p k hd) hd
      simpa only [add_zero] using
        Agree.add (Agree.refl (p + p) (y ^ (k + 1) + tangent y d (k + 1))) hquad

private theorem tangent_sum [Lean.Grind.CommRing R]
    (b y d : TSeries R n) (hy : y.coeff 0 = 0) :
    (List.range n).foldl
        (fun acc k => acc + C (b.coeff k) * tangent y d k) 0 =
      comp b.derivPad y * d := by
  cases n with
  | zero =>
      apply ext
      intro i hi
      omega
  | succ q =>
      rw [comp_spec b.derivPad y hy]
      have hright :
          (List.range (q + 1)).foldl
              (fun acc j => acc + C (b.derivPad.coeff j) * y ^ j) 0 =
            (List.range q).foldl
              (fun acc j => acc +
                C ((((j + 1 : Nat) : R)) * b.coeff (j + 1)) * y ^ j) 0 := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hpref :
            (List.range q).foldl
                (fun acc j => acc + C (b.derivPad.coeff j) * y ^ j) 0 =
              (List.range q).foldl
                (fun acc j => acc +
                  C ((((j + 1 : Nat) : R)) * b.coeff (j + 1)) * y ^ j) 0 := by
          apply List.foldl_add_congr
          intro j hj
          have hjq : j < q := List.mem_range.mp hj
          rw [coeff_derivPad b j (by omega), if_pos (by omega)]
        rw [hpref, coeff_derivPad b q (Nat.lt_succ_self q),
          if_neg (Nat.lt_irrefl (q + 1)),
          C_zero, zero_mul, add_zero]
      change
        (List.range (q + 1)).foldl
            (fun acc k => acc + C (b.coeff k) * tangent y d k) 0 =
          (List.range (q + 1)).foldl
            (fun acc k => acc + C (b.derivPad.coeff k) * y ^ k) 0 * d
      rw [hright, ← List.foldl_add_mul_right_zero]
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hzero : C (b.coeff 0) * tangent y d 0 = 0 := by
        rw [show tangent y d 0 = 0 by simp [tangent], mul_zero]
      rw [hzero, add_zero]
      apply List.foldl_add_congr
      intro j hj
      unfold tangent
      rw [if_neg (by omega), Nat.succ_sub_one]
      have hc :
          C (b.coeff (j + 1)) *
              (C (((j + 1 : Nat) : R)) : TSeries R (q + 1)) =
            C ((((j + 1 : Nat) : R)) * b.coeff (j + 1)) := by
        rw [← C_mul]
        congr 1
        grind
      grind

private theorem comp_taylor [Lean.Grind.CommRing R]
    (b y d : TSeries R n) (p : Nat) (hy : y.coeff 0 = 0)
    (hd0 : d.coeff 0 = 0) (hd : Agree p d 0) :
    Agree (p + p) (comp b (y + d))
      (comp b y + comp b.derivPad y * d) := by
  have hyd : (y + d).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_add y d 0 hn, hy, hd0]
      grind
    · unfold coeff
      rw [dif_neg hn]
  rw [comp_spec b (y + d) hyd, comp_spec b y hy]
  have hfold :
      Agree (p + p)
        ((List.range n).foldl
          (fun acc k => acc + C (b.coeff k) * (y + d) ^ k) 0)
        ((List.range n).foldl
          (fun acc k => acc + C (b.coeff k) *
            (y ^ k + tangent y d k)) 0) := by
    have go (xs : List Nat) (z z' : TSeries R n)
        (hz : Agree (p + p) z z') :
        Agree (p + p)
          (xs.foldl (fun acc k => acc + C (b.coeff k) * (y + d) ^ k) z)
          (xs.foldl (fun acc k => acc + C (b.coeff k) *
            (y ^ k + tangent y d k)) z') := by
      induction xs generalizing z z' with
      | nil => exact hz
      | cons k ks ih =>
          simp only [List.foldl_cons]
          exact ih _ _ (Agree.add hz
            (Agree.mul (Agree.refl (p + p) (C (b.coeff k)))
              (pow_taylor y d p k hd)))
    exact go (List.range n) 0 0 (Agree.refl (p + p) 0)
  apply Agree.trans hfold
  have hsplit :
      (List.range n).foldl
          (fun acc k => acc + C (b.coeff k) *
            (y ^ k + tangent y d k)) 0 =
        (List.range n).foldl
            (fun acc k => acc + C (b.coeff k) * y ^ k) 0 +
          (List.range n).foldl
            (fun acc k => acc + C (b.coeff k) * tangent y d k) 0 := by
    calc
      _ = (List.range n).foldl
          (fun acc k => acc +
            (C (b.coeff k) * y ^ k + C (b.coeff k) * tangent y d k)) 0 := by
              apply List.foldl_add_congr
              intro k hk
              rw [left_distrib]
      _ = _ := List.foldl_add_add _ _ _
  rw [hsplit, tangent_sum b y d hy]
  exact Agree.refl (p + p) _

private theorem derivPad_coeff_zero_mul [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (hv : b.coeff 1 * v = 1) :
    b.derivPad.coeff 0 * v = 1 := by
  by_cases hn : 0 < n
  · rw [coeff_derivPad b 0 hn]
    simp only [Nat.zero_add]
    by_cases h1 : 1 < n
    · rw [if_pos h1, Lean.Grind.Semiring.natCast_one]
      calc
        1 * b.coeff 1 * v = b.coeff 1 * v := by grind
        _ = 1 := hv
    · rw [if_neg h1]
      have hb : b.coeff 1 = 0 := by
        unfold coeff
        rw [dif_neg h1]
      rw [hb] at hv
      simpa only [zero_mul] using hv
  · have hd : b.derivPad.coeff 0 = 0 := by
      unfold coeff
      rw [dif_neg hn]
    have hb : b.coeff 1 = 0 := by
      unfold coeff
      rw [dif_neg (by omega)]
    rw [hd]
    calc
      0 * v = b.coeff 1 * v := by rw [hb]
      _ = 1 := hv

private theorem revStep_correct [Lean.Grind.CommRing R]
    (b y : TSeries R n) (v : R) (p : Nat) (hp : 0 < p)
    (hy : y.coeff 0 = 0) (hv : b.coeff 1 * v = 1)
    (herr : Agree p (comp b y - X) 0) :
    (revStep b v y (p + p)).coeff 0 = 0 ∧
      Agree (p + p) (comp b (revStep b v y (p + p)) - X) 0 := by
  let m := p + p
  let numerator := compUpTo m b y - X
  let denominator := compUpTo m b.derivPad y
  let inverse := invUpTo m denominator v
  let correction := mulUpTo m numerator inverse
  let derivative := comp b.derivPad y
  have hnum : Agree m numerator (comp b y - X) := by
    dsimp only [numerator]
    exact Agree.sub (Agree.compUpTo m b y hy) (Agree.refl m X)
  have hden : Agree m denominator derivative := by
    dsimp only [denominator, derivative]
    exact Agree.compUpTo m b.derivPad y hy
  have hden0 : denominator.coeff 0 * v = 1 := by
    by_cases hn : 0 < n
    · calc
        denominator.coeff 0 * v = derivative.coeff 0 * v := by
          rw [hden 0 hn (by dsimp only [m]; omega)]
        _ = b.derivPad.coeff 0 * v := by
          rw [coeff_comp_zero b.derivPad y hy]
        _ = 1 := derivPad_coeff_zero_mul b v hv
    · have hd : denominator.coeff 0 = 0 := by
        unfold coeff
        rw [dif_neg hn]
      have hb : b.coeff 1 = 0 := by
        unfold coeff
        rw [dif_neg (by omega)]
      rw [hd]
      calc
        0 * v = b.coeff 1 * v := by rw [hb]
        _ = 1 := hv
  have hinv : Agree m inverse (invOfUnit denominator v) := by
    intro i hi him
    dsimp only [inverse]
    rw [coeff_invUpTo m denominator v hden0 i hi, if_pos him]
  have hdeninv : Agree m (denominator * inverse) 1 := by
    have hmul := Agree.mul (Agree.refl m denominator) hinv
    rw [invOfUnit_mul denominator v hden0] at hmul
    exact hmul
  have hcorrection : Agree m correction (numerator * inverse) := by
    dsimp only [correction]
    exact Agree.mulUpTo m numerator inverse
  have hcancel : Agree m (derivative * correction) (comp b y - X) := by
    have hleft := Agree.mul hden.symm hcorrection
    have halg : denominator * (numerator * inverse) =
        numerator * (denominator * inverse) := by
      grind
    rw [halg] at hleft
    have hright := Agree.mul (Agree.refl m numerator) hdeninv
    rw [mul_one] at hright
    exact hleft.trans (hright.trans hnum)
  have hnumSmall : Agree p numerator 0 :=
    (hnum.mono (by dsimp only [m]; omega)).trans herr
  have hcorrectionSmall : Agree p correction 0 := by
    have hprod := Agree.mul hnumSmall (Agree.refl p inverse)
    rw [zero_mul] at hprod
    exact (hcorrection.mono (by dsimp only [m]; omega)).trans hprod
  have hnegSmall : Agree p (-correction) 0 := by
    have hneg := Agree.neg hcorrectionSmall
    have hz : -(0 : TSeries R n) = 0 := by grind
    rw [hz] at hneg
    exact hneg
  have hneg0 : (-correction).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_neg correction 0 hn,
        hcorrectionSmall 0 hn hp, coeff_zero]
      grind
    · unfold coeff
      rw [dif_neg hn]
  have hyc0 : (y - correction).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · rw [coeff_sub y correction 0 hn, hy,
        hcorrectionSmall 0 hn hp, coeff_zero]
      grind
    · unfold coeff
      rw [dif_neg hn]
  have htaylor : Agree m (comp b (y - correction))
      (comp b y - derivative * correction) := by
    have ht := comp_taylor b y (-correction) p hy hneg0 hnegSmall
    have hleft : y + -correction = y - correction := by grind
    have hright : comp b y + derivative * -correction =
        comp b y - derivative * correction := by grind
    rw [hleft, hright] at ht
    dsimp only [m, derivative]
    exact ht
  have hlinear : Agree m ((comp b y - derivative * correction) - X) 0 := by
    have hs := Agree.sub
      (Agree.sub (Agree.refl m (comp b y)) hcancel) (Agree.refl m X)
    have halg : (comp b y - (comp b y - X)) - X = 0 := by
      grind
    rw [halg] at hs
    exact hs
  have hideal : Agree m (comp b (y - correction) - X) 0 :=
    (Agree.sub htaylor (Agree.refl m X)).trans hlinear
  have hstep : Agree m (revStep b v y m) (y - correction) := by
    intro i hi him
    unfold revStep
    rw [coeff_ofFn _ i hi, if_pos him]
  have hstep0 : (revStep b v y m).coeff 0 = 0 := by
    by_cases hn : 0 < n
    · exact (hstep 0 hn (by dsimp only [m]; omega)).trans hyc0
    · unfold coeff
      rw [dif_neg hn]
  have hcomp := Agree.comp_inner b (revStep b v y m) (y - correction)
    hstep hstep0 hyc0
  have hresult := (Agree.sub hcomp (Agree.refl m X)).trans hideal
  dsimp only [m] at hstep0 hresult
  exact ⟨hstep0, hresult⟩

private theorem coeff_mul_right_lead [Lean.Grind.CommRing R]
    (a d : TSeries R n) (p : Nat) (hp : p < n) (hd : Agree p d 0) :
    (a * d).coeff p = a.coeff 0 * d.coeff p := by
  rw [coeff_mul a d p hp]
  unfold convCoeff
  calc
    (List.range (p + 1)).foldl
        (fun acc j => acc + a.coeff j * d.coeff (p - j)) 0 =
      (List.range (p + 1)).foldl
        (fun acc j => acc + if j = 0 then a.coeff 0 * d.coeff p else 0) 0 := by
          apply List.foldl_add_congr
          intro j hj
          have hjp : j < p + 1 := List.mem_range.mp hj
          by_cases hj0 : j = 0
          · subst j
            rw [if_pos rfl, Nat.sub_zero]
          · rw [if_neg hj0, hd (p - j) (by omega) (by omega), coeff_zero]
            grind
    _ = 0 + a.coeff 0 * d.coeff p :=
      List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
    _ = a.coeff 0 * d.coeff p := by grind

private theorem comp_left_cancel [Lean.Grind.CommRing R]
    (b y z : TSeries R n) (hy : y.coeff 0 = 0) (hz : z.coeff 0 = 0)
    (v : R) (hv : b.coeff 1 * v = 1) (hcomp : comp b y = comp b z) :
    y = z := by
  have go (p : Nat) : Agree p y z := by
    induction p with
    | zero =>
        intro i hi hip
        omega
    | succ p ih =>
        intro i hi hip
        by_cases hil : i < p
        · exact ih i hi hil
        · have hip' : i = p := by omega
          subst i
          by_cases hp0 : p = 0
          · subst p
            exact hy.trans hz.symm
          · let d := y - z
            have hd : Agree p d 0 := by
              have hs := Agree.sub ih (Agree.refl p z)
              have hzz : z - z = 0 := by grind
              rw [hzz] at hs
              exact hs
            have hd0 : d.coeff 0 = 0 := by
              dsimp only [d]
              rw [coeff_sub y z 0 (by omega), hy, hz]
              grind
            have ht := comp_taylor b z d p hz hd0 hd
            have hyd : z + d = y := by
              dsimp only [d]
              grind
            have htp := ht p hi (by omega)
            rw [hyd, hcomp, coeff_add _ _ p hi] at htp
            have hmul : (comp b.derivPad z * d).coeff p = 0 := by
              grind
            rw [coeff_mul_right_lead (comp b.derivPad z) d p hi hd] at hmul
            have hunit : (comp b.derivPad z).coeff 0 * v = 1 := by
              rw [coeff_comp_zero b.derivPad z hz]
              exact derivPad_coeff_zero_mul b v hv
            have hdp : d.coeff p = 0 := by
              calc
                d.coeff p = 1 * d.coeff p := by grind
                _ = ((comp b.derivPad z).coeff 0 * v) * d.coeff p := by rw [hunit]
                _ = v * ((comp b.derivPad z).coeff 0 * d.coeff p) := by grind
                _ = 0 := by rw [hmul]; grind
            dsimp only [d] at hdp
            rw [coeff_sub y z p hi] at hdp
            grind
  exact Agree.full (go n) (Nat.le_refl n)

private theorem revInit_zero [Lean.Grind.CommRing R] (v : R) :
    (mulUpTo n (C v) X : TSeries R n).coeff 0 = 0 := by
  by_cases hn : 0 < n
  · rw [Agree.mulUpTo_full, coeff_mul_zero (C v) X hn,
      coeff_C v 0 hn, coeff_X 0 hn]
    grind
  · unfold coeff
    rw [dif_neg hn]

private theorem revNewton_correct [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (j : Nat) :
    (newton (revStep b v) (mulUpTo n (C v) X) j).coeff 0 = 0 ∧
      Agree (2 ^ j)
        (comp b (newton (revStep b v) (mulUpTo n (C v) X) j) - X) 0 := by
  induction j with
  | zero =>
      rw [newton]
      refine ⟨revInit_zero v, ?_⟩
      intro i hi hip
      have hi0 : i = 0 := by omega
      subst i
      rw [coeff_sub _ X 0 hi, coeff_comp_zero b _ (revInit_zero v),
        h0, coeff_X 0 hi, coeff_zero]
      grind
  | succ j ih =>
      rw [newton]
      have hs := revStep_correct b
        (newton (revStep b v) (mulUpTo n (C v) X) j) v (2 ^ j)
        (Nat.two_pow_pos j) ih.1 hv ih.2
      have hp : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
        rw [Nat.pow_succ]
        omega
      simpa only [hp] using hs

private theorem revOfUnit_eq [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) :
    revOfUnit b v =
      newton (revStep b v) (mulUpTo n (C v) X) (steps n) := by
  apply ext
  intro i hi
  unfold revOfUnit revUpTo
  rw [coeff_ofFn _ i hi, if_pos hi, Nat.min_self]

private theorem X_coeff_zero [Lean.Grind.CommRing R] :
    (X : TSeries R n).coeff 0 = 0 := by
  by_cases hn : 0 < n
  · rw [coeff_X 0 hn]
    grind
  · unfold coeff
    rw [dif_neg hn]

private theorem coeff_comp_one [Lean.Grind.CommRing R]
    (b y : TSeries R n) (hy : y.coeff 0 = 0) (h : 1 < n) :
    (comp b y).coeff 1 = b.coeff 1 * y.coeff 1 := by
  have hyAgree : Agree 1 y 0 := by
    intro i hi hi1
    have hi0 : i = 0 := by omega
    subst i
    rw [hy, coeff_zero]
  have ht := comp_taylor b 0 y 1 (coeff_zero 0) hy hyAgree
  have hzy : (0 : TSeries R n) + y = y := by grind
  rw [hzy] at ht
  have hc := ht 1 h (by omega)
  rw [coeff_add _ _ 1 h, comp_zero_right,
    coeff_C (b.coeff 0) 1 h, if_neg (by omega),
    coeff_mul_right_lead (comp b.derivPad 0) y 1 h hyAgree,
    coeff_comp_zero b.derivPad 0 (coeff_zero 0),
    coeff_derivPad b 0 (by omega), if_pos h,
    Lean.Grind.Semiring.natCast_one] at hc
  grind

/-- Newton reversion is both a left and right compositional inverse. -/
theorem revOfUnit_comp [Lean.Grind.CommRing R] (b : TSeries R n) (v : R)
    (h0 : b.coeff 0 = 0) (hv : b.coeff 1 * v = 1) :
    comp b (revOfUnit b v) = X ∧ comp (revOfUnit b v) b = X := by
  let y := newton (revStep b v) (mulUpTo n (C v) X) (steps n)
  have hy0 : y.coeff 0 = 0 := (revNewton_correct b v h0 hv (steps n)).1
  have hyerr : Agree (2 ^ steps n) (comp b y - X) 0 :=
    (revNewton_correct b v h0 hv (steps n)).2
  have hleftY : comp b y = X := by
    apply Agree.full (Agree.ofSub hyerr) (two_pow_steps_ge n)
  have hrev : revOfUnit b v = y := revOfUnit_eq b v
  have hleft : comp b (revOfUnit b v) = X := by
    rw [hrev]
    exact hleftY
  have hrev0 : (revOfUnit b v).coeff 0 = 0 := by
    rw [hrev]
    exact hy0
  have hright0 : (comp (revOfUnit b v) b).coeff 0 = 0 := by
    rw [coeff_comp_zero (revOfUnit b v) b h0, hrev0]
  have hcomp : comp b (comp (revOfUnit b v) b) = comp b X := by
    calc
      comp b (comp (revOfUnit b v) b) =
          comp (comp b (revOfUnit b v)) b :=
        (comp_assoc b (revOfUnit b v) b hrev0 h0).symm
      _ = comp X b := by rw [hleft]
      _ = b := comp_X_left b h0
      _ = comp b X := (comp_X_right b).symm
  exact ⟨hleft, comp_left_cancel b (comp (revOfUnit b v) b) X
    hright0 X_coeff_zero v hv hcomp⟩

/-- A Newton reversion has zero constant coefficient. -/
theorem revOfUnit_coeff_zero [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) : (revOfUnit b v).coeff 0 = 0 := by
  rw [revOfUnit_eq b v]
  exact (revNewton_correct b v h0 hv (steps n)).1

/-- The compositional inverse retains the supplied inverse linear
coefficient. -/
theorem revOfUnit_coeff_one [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (h : 1 < n) :
    (revOfUnit b v).coeff 1 = v := by
  have hleft := (revOfUnit_comp b v h0 hv).1
  have hrev0 : (revOfUnit b v).coeff 0 = 0 := by
    rw [revOfUnit_eq b v]
    exact (revNewton_correct b v h0 hv (steps n)).1
  have hc := coeff_comp_one b (revOfUnit b v) hrev0 h
  rw [hleft, coeff_X 1 h, if_pos rfl] at hc
  calc
    (revOfUnit b v).coeff 1 = 1 * (revOfUnit b v).coeff 1 := by grind
    _ = (b.coeff 1 * v) * (revOfUnit b v).coeff 1 := by rw [hv]
    _ = v * (b.coeff 1 * (revOfUnit b v).coeff 1) := by grind
    _ = v := by rw [← hc]; grind

/-- At precision at most one, every zero-constant series reverts to zero. -/
theorem rev_le_one [Lean.Grind.CommRing R] (b : TSeries R n)
    (hn : n ≤ 1) (h0 : b.coeff 0 = 0) :
    comp b 0 = X ∧ comp 0 b = X := by
  have hb : b = 0 := by
    apply ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    rw [h0, coeff_zero]
  have hX : (X : TSeries R n) = 0 := by
    apply ext
    intro i hi
    rw [coeff_X i hi, coeff_zero]
    have hi0 : i = 0 := by omega
    simp [hi0]
  subst b
  rw [hX]
  exact ⟨comp_zero 0 (coeff_zero 0), comp_zero 0 (coeff_zero 0)⟩

/-- The bounded Newton implementation itself returns zero when no linear
coefficient is represented. -/
theorem revOfUnit_le_one [Lean.Grind.CommRing R] (b : TSeries R n) (v : R)
    (hn : n ≤ 1) : revOfUnit b v = 0 := by
  apply ext
  intro i hi
  have hn1 : n = 1 := by omega
  subst n
  have hi0 : i = 0 := by omega
  subst i
  unfold revOfUnit revUpTo steps
  simp only [Nat.min_self, if_pos (by omega : 1 ≤ 1), newton]
  grind

/-- The Newton numerator vanishes throughout the precision already established
by an iterate. -/
theorem rev_numerator_valuation [Lean.Grind.CommRing R]
    (b : TSeries R n) (v : R) (h0 : b.coeff 0 = 0)
    (hv : b.coeff 1 * v = 1) (j i : Nat)
    (hi : i < min n (2 ^ j)) :
    (comp b (newton (revStep b v) (mulUpTo n (C v) X) j) - X).coeff i = 0 := by
  have h := (revNewton_correct b v h0 hv j).2 i (by omega) (by omega)
  rw [coeff_zero] at h
  exact h

/-- Optional reversion keeps the constant test at precision one while dropping
the nonexistent linear test. -/
theorem rev?_isSome_iff [Lean.Grind.CommRing R] [DecidableEq R]
    [UnitOps R] [LawfulUnitOps R] (b : TSeries R n) :
    (rev? b).isSome = true ↔
      b.coeff 0 = 0 ∧ (n ≤ 1 ∨ ∃ v, b.coeff 1 * v = 1) := by
  by_cases h0 : b.coeff 0 = 0
  · by_cases hn : n ≤ 1
    · simp [rev?, h0, hn]
    · rw [show rev? b =
        match UnitOps.inv? (R := R) (b.coeff 1) with
        | some v => some (revOfUnit b v)
        | none => none by simp [rev?, h0, hn]]
      cases hq : UnitOps.inv? (R := R) (b.coeff 1) with
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff, h0,
            true_and, hn, false_or]
          intro hunit
          have hsome := LawfulUnitOps.inv?_isSome (R := R) (b.coeff 1) hunit
          simp [hq] at hsome
      | some v =>
          simp only [Option.isSome_some, h0, true_and, hn, false_or, true_iff]
          exact ⟨v, LawfulUnitOps.inv?_eq (R := R) (b.coeff 1) v hq⟩
  · simp [rev?, h0]

end Hex.TSeries
