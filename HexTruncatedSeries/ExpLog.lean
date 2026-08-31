/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Sqrt

public section

/-!
Formal logarithm and exponential at a fixed precision.

The logarithm integrates `a' / a`; the explicit final truncation handles the
precision-zero identity `n - 1 + 1 = 1`.  Exponential uses the bounded Newton
update `y ↦ y * (1 + a - log y)`.  Neither operation searches for a unit:
the logarithm uses the literal inverse witness `1`, so only the
precision-indexed `NatInverses` capability is required.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Formal logarithm computed only below precision `m`. -/
@[expose]
def logUpTo [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (m : Nat) (a : TSeries R n) : TSeries R n :=
  let ainv := (invUpTo m a 1).truncate (n - 1) (Nat.sub_le n 1)
  let product := mulUpTo (m - 1) a.deriv ainv
  let integrated := (integrate product).truncate n (by omega)
  ofFn fun i => if i < m then integrated.coeff i else 0

/-- Formal logarithm with zero constant coefficient. -/
@[expose]
def log [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) : TSeries R n :=
  logUpTo n a

/-- One bounded exponential Newton update. -/
@[expose]
def expStep [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a y : TSeries R n) (m : Nat) : TSeries R n :=
  mulUpTo m y (C 1 + a - logUpTo m y)

/-- Formal exponential computed only below precision `m`. -/
@[expose]
def expUpTo [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (m : Nat) (a : TSeries R n) : TSeries R n :=
  let y := newton (expStep a) 1 (steps (min m n))
  ofFn fun i => if i < m then y.coeff i else 0

/-- Formal exponential with constant coefficient one. -/
@[expose]
def exp [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) : TSeries R n :=
  expUpTo n a

/-- The derivative characterizes the logarithm.  The constant-term hypothesis
is retained as the public domain contract shared by the other logarithm laws;
the derivative identity itself follows from the total implementation without
using it. -/
theorem deriv_log [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) (_h : (a - 1).coeff 0 = 0) :
    (log a).deriv =
      a.deriv * (invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1) := by
  apply ext
  intro i hi
  rw [coeff_deriv (log a) i hi]
  unfold log logUpTo
  rw [coeff_ofFn _ (i + 1) (by omega), if_pos (by omega),
    coeff_truncate _ _ (i + 1) (by omega),
    coeff_integrate _ (i + 1) (by omega)]
  simp only [show i + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
  rw [coeff_mulUpTo (n - 1) _ _ i (by omega), if_pos hi,
    coeff_mul _ _ i hi]
  simp only [invOfUnit]
  have hinv := NatInverses.invNat_eq (R := R) (m := n - 1) (i + 1)
    (by omega) (by omega)
  rw [Lean.Grind.Semiring.natCast_succ] at hinv ⊢
  rw [← Lean.Grind.Semiring.mul_assoc, hinv, Lean.Grind.Semiring.one_mul]
  rw [coeff_mul _ _ i hi]

private theorem logUpTo_coeff_zero [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (m : Nat) (a : TSeries R n)
    (hn : 0 < n) (hm : 0 < m) :
    (logUpTo m a).coeff 0 = 0 := by
  unfold logUpTo
  rw [coeff_ofFn _ 0 hn, if_pos hm,
    coeff_truncate _ _ 0 (by omega), coeff_integrate _ 0 (by omega)]
  simp

/-- The logarithm has zero constant coefficient at positive precision.  The
constant-term hypothesis is retained for a stable, uniform logarithm API even
though this particular coefficient identity does not use it. -/
theorem log_coeff_zero [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) (_h : (a - 1).coeff 0 = 0) (h0 : 0 < n) :
    (log a).coeff 0 = 0 := by
  exact logUpTo_coeff_zero n a h0 h0

private theorem expStep_coeff_zero [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a y : TSeries R n) (m : Nat)
    (ha : a.coeff 0 = 0) (hy : y.coeff 0 = 1)
    (hn : 0 < n) (hm : 0 < m) :
    (expStep a y m).coeff 0 = 1 := by
  unfold expStep
  rw [coeff_mulUpTo m y (C 1 + a - logUpTo m y) 0 hn, if_pos hm,
    coeff_mul_zero y (C 1 + a - logUpTo m y) hn,
    coeff_sub (C 1 + a) (logUpTo m y) 0 hn,
    coeff_add (C 1) a 0 hn, coeff_C 1 0 hn,
    logUpTo_coeff_zero m y hn hm, ha, hy]
  grind

private theorem expNewton_coeff_zero [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a : TSeries R n)
    (ha : a.coeff 0 = 0) (hn : 0 < n) (j : Nat) :
    (newton (expStep a) 1 j).coeff 0 = 1 := by
  induction j with
  | zero =>
      rw [newton, coeff_one 0 hn]
      simp
  | succ j ih =>
      change (expStep a (newton (expStep a) 1 j) (2 ^ (j + 1))).coeff 0 = 1
      exact expStep_coeff_zero a _ _ ha ih hn (Nat.two_pow_pos _)

/-- The exponential has constant coefficient one at positive precision. -/
theorem exp_coeff_zero [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) (h : a.coeff 0 = 0) (h0 : 0 < n) :
    (exp a).coeff 0 = 1 := by
  unfold exp expUpTo
  rw [coeff_ofFn _ 0 h0, if_pos h0]
  simpa only [Nat.min_self] using expNewton_coeff_zero a h h0 (steps n)

private theorem deriv_add [Lean.Grind.CommRing R] (a b : TSeries R n) :
    (a + b).deriv = a.deriv + b.deriv := by
  apply ext
  intro i hi
  rw [coeff_deriv (a + b) i hi, coeff_add a b (i + 1) (by omega),
    coeff_add a.deriv b.deriv i hi, coeff_deriv a i hi, coeff_deriv b i hi]
  grind

private theorem deriv_one [Lean.Grind.CommRing R] :
    (1 : TSeries R n).deriv = 0 := by
  apply ext
  intro i hi
  rw [coeff_deriv 1 i hi, coeff_one (i + 1) (by omega),
    if_neg (by omega), coeff_zero]
  grind

private theorem deriv_zero [Lean.Grind.CommRing R] :
    (0 : TSeries R n).deriv = 0 := by
  apply ext
  intro i hi
  rw [coeff_deriv 0 i hi, coeff_zero, coeff_zero]
  grind

private theorem agree_of_deriv [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] {a b : TSeries R n} {p : Nat}
    (h0 : a.coeff 0 = b.coeff 0) (h : Agree p a.deriv b.deriv) :
    Agree (p + 1) a b := by
  intro i hi hip
  cases i with
  | zero => exact h0
  | succ i =>
      have hin : i < n - 1 := by omega
      have hip' : i < p := by omega
      have hd := h i hin hip'
      rw [coeff_deriv a i hin, coeff_deriv b i hin] at hd
      have hu := NatInverses.invNat_eq (R := R) (m := n - 1) (i + 1)
        (by omega) (by omega)
      calc
        a.coeff (i + 1) = 1 * a.coeff (i + 1) := by grind
        _ = (((i + 1 : Nat) : R) *
              NatInverses.invNat (R := R) (m := n - 1) (i + 1)) *
              a.coeff (i + 1) := by rw [hu]
        _ = NatInverses.invNat (R := R) (m := n - 1) (i + 1) *
              (((i + 1 : Nat) : R) * a.coeff (i + 1)) := by grind
        _ = NatInverses.invNat (R := R) (m := n - 1) (i + 1) *
              (((i + 1 : Nat) : R) * b.coeff (i + 1)) := by rw [hd]
        _ = (((i + 1 : Nat) : R) *
              NatInverses.invNat (R := R) (m := n - 1) (i + 1)) *
              b.coeff (i + 1) := by grind
        _ = b.coeff (i + 1) := by rw [hu]; grind

private theorem unitCoeff_mul [Lean.Grind.CommRing R]
    (a b : TSeries R n) (ha : a.coeff 0 = 1) (hb : b.coeff 0 = 1) :
    (a * b).coeff 0 = 1 := by
  by_cases hn : 0 < n
  · rw [coeff_mul_zero a b hn, ha, hb]
    grind
  · unfold coeff at ha ⊢
    rw [dif_neg hn] at ha ⊢
    exact ha

private theorem logArg [Lean.Grind.CommRing R]
    (a : TSeries R n) (ha : a.coeff 0 = 1) :
    (a - 1).coeff 0 = 0 := by
  by_cases hn : 0 < n
  · rw [coeff_sub a 1 0 hn, coeff_one 0 hn, ha]
    grind
  · unfold coeff
    rw [dif_neg hn]

private theorem log_mul [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a b : TSeries R n)
    (ha : a.coeff 0 = 1) (hb : b.coeff 0 = 1) :
    log (a * b) = log a + log b := by
  by_cases hn : 0 < n
  · let ai := invOfUnit a 1
    let bi := invOfUnit b 1
    have hau : a.coeff 0 * 1 = 1 := by rw [ha]; grind
    have hbu : b.coeff 0 * 1 = 1 := by rw [hb]; grind
    have hab : (a * b).coeff 0 = 1 := unitCoeff_mul a b ha hb
    have habu : (a * b).coeff 0 * 1 = 1 := by rw [hab]; grind
    have hai : a * ai = 1 := by
      dsimp only [ai]
      exact invOfUnit_mul a 1 hau
    have hbi : b * bi = 1 := by
      dsimp only [bi]
      exact invOfUnit_mul b 1 hbu
    have hinv : invOfUnit (a * b) 1 = ai * bi := by
      have hm : (a * b) * (ai * bi) = 1 := by
        calc
          (a * b) * (ai * bi) = (a * ai) * (b * bi) := by grind
          _ = 1 * 1 := by rw [hai, hbi]
          _ = 1 := by grind
      exact (invOfUnit_unique (a * b) (ai * bi) 1 habu hm).symm
    have haiT :
        a.truncate (n - 1) (Nat.sub_le n 1) *
            ai.truncate (n - 1) (Nat.sub_le n 1) = 1 := by
      have ht := congrArg
        (fun z : TSeries R n => z.truncate (n - 1) (Nat.sub_le n 1)) hai
      rw [truncate_mul, truncate_one] at ht
      exact ht
    have hbiT :
        b.truncate (n - 1) (Nat.sub_le n 1) *
            bi.truncate (n - 1) (Nat.sub_le n 1) = 1 := by
      have ht := congrArg
        (fun z : TSeries R n => z.truncate (n - 1) (Nat.sub_le n 1)) hbi
      rw [truncate_mul, truncate_one] at ht
      exact ht
    have hderiv : (log (a * b)).deriv = (log a + log b).deriv := by
      rw [deriv_log (a * b) (logArg (a * b) hab), deriv_add,
        deriv_log a (logArg a ha), deriv_log b (logArg b hb),
        deriv_mul, hinv, truncate_mul]
      dsimp only [ai, bi] at haiT hbiT ⊢
      calc
        (a.deriv * b.truncate (n - 1) (Nat.sub_le n 1) +
              a.truncate (n - 1) (Nat.sub_le n 1) * b.deriv) *
            ((invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1) *
              (invOfUnit b 1).truncate (n - 1) (Nat.sub_le n 1)) =
          (a.deriv * (invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1)) *
              (b.truncate (n - 1) (Nat.sub_le n 1) *
                (invOfUnit b 1).truncate (n - 1) (Nat.sub_le n 1)) +
            (b.deriv * (invOfUnit b 1).truncate (n - 1) (Nat.sub_le n 1)) *
              (a.truncate (n - 1) (Nat.sub_le n 1) *
                (invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1)) := by grind
        _ = a.deriv * (invOfUnit a 1).truncate (n - 1) (Nat.sub_le n 1) +
              b.deriv * (invOfUnit b 1).truncate (n - 1) (Nat.sub_le n 1) := by
          rw [haiT, hbiT]
          grind
    have hconst : (log (a * b)).coeff 0 = (log a + log b).coeff 0 := by
      rw [log_coeff_zero (a * b) (logArg (a * b) hab) hn,
        coeff_add _ _ 0 hn, log_coeff_zero a (logArg a ha) hn,
        log_coeff_zero b (logArg b hb) hn]
      grind
    have hagree := agree_of_deriv (p := n - 1) hconst
      (by rw [hderiv]; exact Agree.refl (n - 1) _)
    have hp : n - 1 + 1 = n := by omega
    rw [hp] at hagree
    exact Agree.full hagree (Nat.le_refl n)
  · apply ext
    intro i hi
    omega

private theorem log_one_add [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (e : TSeries R n) (p : Nat) (hp : 0 < p)
    (he0 : e.coeff 0 = 0) (he : Agree p e 0) :
    Agree (p + p) (log (1 + e)) e := by
  by_cases hn : 0 < n
  · let q : TSeries R n := 1 + e
    let qi := invOfUnit q 1
    have hq0 : q.coeff 0 = 1 := by
      dsimp only [q]
      rw [coeff_add 1 e 0 hn, coeff_one 0 hn, he0]
      grind
    have hqu : q.coeff 0 * 1 = 1 := by rw [hq0]; grind
    have hqi : q * qi = 1 := by
      dsimp only [qi]
      exact invOfUnit_mul q 1 hqu
    have hInvDiff : Agree p (qi - 1) 0 := by
      have halg : qi - 1 = -(e * qi) := by
        dsimp only [q] at hqi
        grind
      rw [halg]
      have hm := Agree.mul he (Agree.refl p qi)
      rw [zero_mul] at hm
      have hneg := Agree.neg hm
      have hz : -(0 : TSeries R n) = 0 := by grind
      rw [hz] at hneg
      exact hneg
    have hInvDiffT : Agree p
        (qi.truncate (n - 1) (Nat.sub_le n 1) - 1) 0 := by
      intro i hi hip
      have h := hInvDiff i (by omega) hip
      rw [coeff_sub qi 1 i (by omega), coeff_one i (by omega), coeff_zero] at h
      rw [coeff_sub _ 1 i hi, coeff_truncate qi (Nat.sub_le n 1) i hi,
        coeff_one i hi, coeff_zero]
      exact h
    have heDeriv : Agree (p - 1) e.deriv 0 := by
      intro i hi hip
      rw [coeff_deriv e i hi, he (i + 1) (by omega) (by omega), coeff_zero]
      grind
    have hqderiv : q.deriv = e.deriv := by
      dsimp only [q]
      rw [deriv_add, deriv_one]
      grind
    have hlogderiv : (log q).deriv =
        e.deriv * qi.truncate (n - 1) (Nat.sub_le n 1) := by
      rw [deriv_log q (logArg q hq0), hqderiv]
    have hderr : Agree ((p - 1) + p) ((log q).deriv - e.deriv) 0 := by
      have heq : (log q).deriv - e.deriv =
          e.deriv * (qi.truncate (n - 1) (Nat.sub_le n 1) - 1) := by
        rw [hlogderiv]
        grind
      rw [heq]
      exact Agree.zeroMul heDeriv hInvDiffT
    have hconst : (log q).coeff 0 = e.coeff 0 := by
      rw [log_coeff_zero q (logArg q hq0) hn, he0]
    have hseries := agree_of_deriv hconst (Agree.ofSub hderr)
    have hprec : (p - 1) + p + 1 = p + p := by omega
    rw [hprec] at hseries
    exact hseries
  · intro i hi hip
    omega

/-- Bounded logarithm agrees with the full logarithm throughout the requested
prefix. -/
theorem logUpTo_agree [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (m : Nat) (a : TSeries R n)
    (ha : (a - 1).coeff 0 = 0) : Agree m (logUpTo m a) (log a) := by
  by_cases hn : 0 < n
  · have ha0 : a.coeff 0 = 1 := by
      rw [coeff_sub a 1 0 hn, coeff_one 0 hn] at ha
      grind
    intro i hi him
    have hau : a.coeff 0 * 1 = 1 := by rw [ha0]; grind
    unfold log logUpTo
    rw [coeff_ofFn _ i hi, if_pos him, coeff_ofFn _ i hi, if_pos hi,
      coeff_truncate _ _ i hi, coeff_truncate _ _ i hi]
    cases i with
    | zero =>
        rw [coeff_integrate _ 0 (by omega), coeff_integrate _ 0 (by omega)]
        simp
    | succ i =>
        rw [coeff_integrate _ (i + 1) (by omega),
          coeff_integrate _ (i + 1) (by omega)]
        simp only [show i + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
        rw [coeff_mulUpTo (m - 1) _ _ i (by omega), if_pos (by omega),
          coeff_mulUpTo (n - 1) _ _ i (by omega), if_pos (by omega),
          coeff_mul _ _ i (by omega), coeff_mul _ _ i (by omega)]
        congr 1
        unfold convCoeff
        apply List.foldl_add_congr
        intro j hj
        have hj' : j < i + 1 := List.mem_range.mp hj
        rw [coeff_truncate _ _ (i - j) (by omega),
          coeff_truncate _ _ (i - j) (by omega),
          coeff_invUpTo m a 1 hau (i - j) (by omega), if_pos (by omega),
          coeff_invUpTo n a 1 hau (i - j) (by omega), if_pos (by omega)]
  · intro i hi _
    omega

private theorem log_agree [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (p : Nat) (hp : 0 < p) (a b : TSeries R n)
    (ha : a.coeff 0 = 1) (hb : b.coeff 0 = 1) (hab : Agree p a b) :
    Agree p (log a) (log b) := by
  by_cases hn : 0 < n
  · let ai := invOfUnit a 1
    let bi := invOfUnit b 1
    have hau : a.coeff 0 * 1 = 1 := by rw [ha]; grind
    have hbu : b.coeff 0 * 1 = 1 := by rw [hb]; grind
    have hai : a * ai = 1 := by
      dsimp only [ai]
      exact invOfUnit_mul a 1 hau
    have hbi : b * bi = 1 := by
      dsimp only [bi]
      exact invOfUnit_mul b 1 hbu
    have hdiff : Agree p (b - a) 0 := by
      have hs := Agree.sub hab.symm (Agree.refl p a)
      have haa : a - a = 0 := by grind
      rw [haa] at hs
      exact hs
    have hinv : Agree p ai bi := by
      have halg : ai - bi = ai * (b - a) * bi := by
        grind
      have hleft := Agree.mul (Agree.refl p ai) hdiff
      rw [mul_zero] at hleft
      have hright := Agree.mul hleft (Agree.refl p bi)
      rw [zero_mul] at hright
      have hsub : Agree p (ai - bi) 0 := by
        rw [halg]
        exact hright
      exact Agree.ofSub hsub
    have hderiv : Agree (p - 1) a.deriv b.deriv := by
      intro i hi hip
      rw [coeff_deriv a i hi, coeff_deriv b i hi,
        hab (i + 1) (by omega) (by omega)]
    have hinvT : Agree p
        (ai.truncate (n - 1) (Nat.sub_le n 1))
        (bi.truncate (n - 1) (Nat.sub_le n 1)) := by
      intro i hi hip
      rw [coeff_truncate ai (Nat.sub_le n 1) i hi,
        coeff_truncate bi (Nat.sub_le n 1) i hi,
        hinv i (by omega) hip]
    have hlogDeriv : Agree (p - 1) (log a).deriv (log b).deriv := by
      rw [deriv_log a (logArg a ha), deriv_log b (logArg b hb)]
      exact Agree.mul hderiv (hinvT.mono (by omega))
    have hconst : (log a).coeff 0 = (log b).coeff 0 := by
      rw [log_coeff_zero a (logArg a ha) hn,
        log_coeff_zero b (logArg b hb) hn]
    have hs := agree_of_deriv hconst hlogDeriv
    have hprec : p - 1 + 1 = p := by omega
    rw [hprec] at hs
    exact hs
  · intro i hi hip
    omega

private theorem expStep_correct [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a y : TSeries R n) (p : Nat)
    (hp : 0 < p) (hn : 0 < n) (ha : a.coeff 0 = 0)
    (hy : y.coeff 0 = 1) (herr : Agree p (a - log y) 0) :
    (expStep a y (p + p)).coeff 0 = 1 ∧
      Agree (p + p) (a - log (expStep a y (p + p))) 0 := by
  let m := p + p
  let e := a - log y
  let factor := C 1 + a - logUpTo m y
  let ideal := y * (1 + e)
  have he0 : e.coeff 0 = 0 := by
    dsimp only [e]
    rw [coeff_sub a (log y) 0 hn, ha,
      log_coeff_zero y (logArg y hy) hn]
    grind
  have hfac0 : (1 + e : TSeries R n).coeff 0 = 1 := by
    rw [coeff_add 1 e 0 hn, coeff_one 0 hn, he0]
    grind
  have hfactor : Agree m factor (1 + e) := by
    have h := Agree.sub
      (Agree.add (Agree.refl m (C 1)) (Agree.refl m a))
      (logUpTo_agree m y (logArg y hy))
    have halg : C 1 + a - log y = 1 + e := by
      dsimp only [e]
      rw [C_one]
      grind
    rw [halg] at h
    exact h
  have hnext : Agree m (expStep a y m) ideal := by
    have hbounded : Agree m (expStep a y m) (y * factor) := by
      dsimp only [factor]
      exact Agree.mulUpTo m y (C 1 + a - logUpTo m y)
    exact hbounded.trans (Agree.mul (Agree.refl m y) hfactor)
  have hideal0 : ideal.coeff 0 = 1 := by
    dsimp only [ideal]
    exact unitCoeff_mul y (1 + e) hy hfac0
  have hnext0 : (expStep a y m).coeff 0 = 1 := by
    exact (hnext 0 hn (by dsimp only [m]; omega)).trans hideal0
  have hlogNext : Agree m (log (expStep a y m)) (log ideal) :=
    log_agree m (by dsimp only [m]; omega) (expStep a y m) ideal
      hnext0 hideal0 hnext
  have hlocal : Agree m (log (1 + e)) e := by
    dsimp only [m]
    exact log_one_add e p hp he0 herr
  have hlogIdeal : log ideal = log y + log (1 + e) := by
    dsimp only [ideal]
    exact log_mul y (1 + e) hy hfac0
  have hideal : Agree m (log ideal) (log y + e) := by
    have h := Agree.add (Agree.refl m (log y)) hlocal
    rw [← hlogIdeal] at h
    exact h
  have hlog := hlogNext.trans hideal
  have herror := Agree.sub (Agree.refl m a) hlog
  have halg : a - (log y + e) = 0 := by
    dsimp only [e]
    grind
  rw [halg] at herror
  dsimp only [m] at hnext0 herror
  exact ⟨hnext0, herror⟩

private theorem expStep_stable [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a y : TSeries R n) (p m : Nat)
    (hpm : p ≤ m) (hy : y.coeff 0 = 1)
    (herr : Agree p (a - log y) 0) : Agree p (expStep a y m) y := by
  let e := a - log y
  let factor := C 1 + a - logUpTo m y
  have hfactor : Agree m factor (1 + e) := by
    have h := Agree.sub
      (Agree.add (Agree.refl m (C 1)) (Agree.refl m a))
      (logUpTo_agree m y (logArg y hy))
    have halg : C 1 + a - log y = 1 + e := by
      dsimp only [e]
      rw [C_one]
      grind
    rw [halg] at h
    exact h
  have hfactorP : Agree p factor 1 := by
    have hone := Agree.add (Agree.refl p (1 : TSeries R n)) herr
    have hsum : (1 : TSeries R n) + 0 = 1 := by grind
    rw [hsum] at hone
    exact (hfactor.mono hpm).trans hone
  have hbounded : Agree m (expStep a y m) (y * factor) := by
    dsimp only [factor]
    exact Agree.mulUpTo m y (C 1 + a - logUpTo m y)
  have hmul := Agree.mul (Agree.refl p y) hfactorP
  rw [mul_one] at hmul
  exact (hbounded.mono hpm).trans hmul

private theorem expNewton_correct [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a : TSeries R n) (ha : a.coeff 0 = 0)
    (hn : 0 < n) (j : Nat) :
    (newton (expStep a) 1 j).coeff 0 = 1 ∧
      Agree (2 ^ j) (a - log (newton (expStep a) 1 j)) 0 := by
  induction j with
  | zero =>
      rw [newton]
      refine ⟨by rw [coeff_one 0 hn]; simp, ?_⟩
      intro i hi hip
      have hi0 : i = 0 := by omega
      subst i
      rw [coeff_sub a (log 1) 0 hn, ha,
        log_coeff_zero 1 (logArg 1 (by rw [coeff_one 0 hn]; simp)) hn,
        coeff_zero]
      grind
  | succ j ih =>
      rw [newton]
      have hs := expStep_correct a (newton (expStep a) 1 j) (2 ^ j)
        (Nat.two_pow_pos j) hn ha ih.1 ih.2
      have hp : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
        rw [Nat.pow_succ]
        omega
      simpa only [hp] using hs

private theorem expNewton_stable [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a : TSeries R n) (ha : a.coeff 0 = 0)
    (hn : 0 < n) (j : Nat) :
    Agree (2 ^ j) (newton (expStep a) 1 (j + 1))
      (newton (expStep a) 1 j) := by
  change Agree (2 ^ j)
    (expStep a (newton (expStep a) 1 j) (2 ^ (j + 1)))
    (newton (expStep a) 1 j)
  exact expStep_stable a _ (2 ^ j) (2 ^ (j + 1))
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ j))
    (expNewton_correct a ha hn j).1 (expNewton_correct a ha hn j).2

private theorem exp_eq [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a : TSeries R n) :
    exp a = newton (expStep a) 1 (steps n) := by
  apply ext
  intro i hi
  unfold exp expUpTo
  rw [coeff_ofFn _ i hi, if_pos hi, Nat.min_self]

/-- Bounded exponential agrees with the full exponential throughout the
requested prefix. -/
theorem expUpTo_agree [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (m : Nat) (a : TSeries R n)
    (ha : a.coeff 0 = 0) : Agree m (expUpTo m a) (exp a) := by
  by_cases hn : 0 < n
  · have hiter : Agree (min m n)
        (newton (expStep a) 1 (steps (min m n)))
        (newton (expStep a) 1 (steps n)) := by
      have h := newton_agree (expStep a) (1 : TSeries R n)
        (expNewton_stable a ha hn)
        (steps_mono (Nat.min_le_right m n))
      exact (h.mono (two_pow_steps_ge (min m n))).symm
    intro i hi him
    unfold expUpTo
    rw [coeff_ofFn _ i hi, if_pos him, exp_eq a]
    exact hiter i hi (by omega)
  · intro i hi _
    omega

private theorem log_one_eq [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] : log (1 : TSeries R n) = 0 := by
  by_cases hn : 0 < n
  · have h := log_one_add (0 : TSeries R n) n hn (coeff_zero 0)
      (Agree.refl n 0)
    have hone : (1 : TSeries R n) + 0 = 1 := by grind
    rw [hone] at h
    exact Agree.full h (by omega)
  · apply ext
    intro i hi
    omega

private theorem log_eq_zero [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a : TSeries R n) (ha : a.coeff 0 = 1)
    (hlog : log a = 0) : a = 1 := by
  by_cases hn : 0 < n
  · let ai := invOfUnit a 1
    have hau : a.coeff 0 * 1 = 1 := by rw [ha]; grind
    have hai : a * ai = 1 := by
      dsimp only [ai]
      exact invOfUnit_mul a 1 hau
    have haiT :
        a.truncate (n - 1) (Nat.sub_le n 1) *
            ai.truncate (n - 1) (Nat.sub_le n 1) = 1 := by
      have ht := congrArg
        (fun z : TSeries R n => z.truncate (n - 1) (Nat.sub_le n 1)) hai
      rw [truncate_mul, truncate_one] at ht
      exact ht
    have haiT' :
        ai.truncate (n - 1) (Nat.sub_le n 1) *
            a.truncate (n - 1) (Nat.sub_le n 1) = 1 := by
      rw [mul_comm]
      exact haiT
    have hdlog := deriv_log a (logArg a ha)
    rw [hlog, deriv_zero] at hdlog
    have haderiv : a.deriv = 0 := by
      calc
        a.deriv = a.deriv * 1 := by grind
        _ = a.deriv *
            (ai.truncate (n - 1) (Nat.sub_le n 1) *
              a.truncate (n - 1) (Nat.sub_le n 1)) := by
                rw [haiT']
        _ = (a.deriv * ai.truncate (n - 1) (Nat.sub_le n 1)) *
              a.truncate (n - 1) (Nat.sub_le n 1) := by grind
        _ = 0 := by rw [← hdlog]; grind
    have hconst : a.coeff 0 = (1 : TSeries R n).coeff 0 := by
      rw [coeff_one 0 hn, ha]
      simp
    have hder : Agree (n - 1) a.deriv (1 : TSeries R n).deriv := by
      rw [haderiv, deriv_one]
      exact Agree.refl (n - 1) 0
    have hs := agree_of_deriv hconst hder
    have hp : n - 1 + 1 = n := by omega
    rw [hp] at hs
    exact Agree.full hs (Nat.le_refl n)
  · apply ext
    intro i hi
    omega

private theorem log_injective [Lean.Grind.CommRing R]
    [NatInverses R (n - 1)] (a b : TSeries R n)
    (ha : a.coeff 0 = 1) (hb : b.coeff 0 = 1)
    (hlog : log a = log b) : a = b := by
  by_cases hn : 0 < n
  · let bi := invOfUnit b 1
    have hbu : b.coeff 0 * 1 = 1 := by rw [hb]; grind
    have hbi : b * bi = 1 := by
      dsimp only [bi]
      exact invOfUnit_mul b 1 hbu
    have hbi0 : bi.coeff 0 = 1 := by
      have hc := congrArg (fun z : TSeries R n => z.coeff 0) hbi
      rw [coeff_mul_zero b bi hn, hb, coeff_one 0 hn] at hc
      grind
    have hlogBi : log bi = -log b := by
      have hm := log_mul b bi hb hbi0
      rw [hbi, log_one_eq] at hm
      grind
    have hab0 : (a * bi).coeff 0 = 1 := unitCoeff_mul a bi ha hbi0
    have hratio : log (a * bi) = 0 := by
      rw [log_mul a bi ha hbi0, hlogBi, hlog]
      grind
    have hratioOne : a * bi = 1 := log_eq_zero (a * bi) hab0 hratio
    calc
      a = a * 1 := by grind
      _ = a * (bi * b) := by rw [mul_comm bi b, hbi]
      _ = (a * bi) * b := by grind
      _ = b := by rw [hratioOne]; grind
  · apply ext
    intro i hi
    omega

/-- Logarithm is a left inverse to exponential on zero-constant series. -/
theorem log_exp [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) (h : a.coeff 0 = 0) : log (exp a) = a := by
  by_cases hn : 0 < n
  · let y := newton (expStep a) 1 (steps n)
    have herr : Agree (2 ^ steps n) (a - log y) 0 :=
      (expNewton_correct a h hn (steps n)).2
    have haLog : a = log y :=
      Agree.full (Agree.ofSub herr) (two_pow_steps_ge n)
    rw [exp_eq a]
    exact haLog.symm
  · apply ext
    intro i hi
    omega

/-- Exponential is a left inverse to logarithm on one-constant series. -/
theorem exp_log [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a : TSeries R n) (h : (a - 1).coeff 0 = 0) : exp (log a) = a := by
  by_cases hn : 0 < n
  · have ha0 : a.coeff 0 = 1 := by
      rw [coeff_sub a 1 0 hn, coeff_one 0 hn] at h
      grind
    have hlog0 : (log a).coeff 0 = 0 := log_coeff_zero a h hn
    have hexp0 : (exp (log a)).coeff 0 = 1 :=
      exp_coeff_zero (log a) hlog0 hn
    exact log_injective (exp (log a)) a hexp0 ha0
      (log_exp (log a) hlog0)
  · apply ext
    intro i hi
    omega

/-- Exponential carries addition to multiplication. -/
theorem exp_add [Lean.Grind.CommRing R] [NatInverses R (n - 1)]
    (a b : TSeries R n) (ha : a.coeff 0 = 0) (hb : b.coeff 0 = 0) :
    exp (a + b) = exp a * exp b := by
  by_cases hn : 0 < n
  · have hab0 : (a + b).coeff 0 = 0 := by
      rw [coeff_add a b 0 hn, ha, hb]
      grind
    have hea0 : (exp a).coeff 0 = 1 := exp_coeff_zero a ha hn
    have heb0 : (exp b).coeff 0 = 1 := exp_coeff_zero b hb hn
    have hleft0 : (exp (a + b)).coeff 0 = 1 :=
      exp_coeff_zero (a + b) hab0 hn
    have hright0 : (exp a * exp b).coeff 0 = 1 :=
      unitCoeff_mul (exp a) (exp b) hea0 heb0
    have hleft : log (exp (a + b)) = a + b := log_exp (a + b) hab0
    have hright : log (exp a * exp b) = a + b := by
      rw [log_mul (exp a) (exp b) hea0 heb0, log_exp a ha, log_exp b hb]
    exact log_injective (exp (a + b)) (exp a * exp b)
      hleft0 hright0 (hleft.trans hright.symm)
  · apply ext
    intro i hi
    omega

end Hex.TSeries
