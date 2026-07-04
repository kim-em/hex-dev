/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp
public import HexPolyZ

public section

/-!
Core conversion operations for executable Hensel lifting.

This module connects the integer polynomial surface from `HexPolyZ` with the
prime-field polynomial surface from `HexPolyFp`, exposing the coefficientwise
reductions and lifts that later Hensel steps reuse.
-/
namespace Hex

/-- Indexed lookup into `(List.range size).map f`: returns `f n` for `n < size` and the
zero default otherwise. Shared coefficient-lookup plumbing used by the `modP`, `reduceModPow`,
and `liftToZ` conversions in this file. -/
private theorem list_getD_map_range {α : Type} [Zero α] (size n : Nat) (f : Nat → α) :
    ((List.range size).map f).getD n (Zero.zero : α) =
      if n < size then f n else (Zero.zero : α) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

namespace ZPoly

/--
Canonical nonnegative representative of `z` modulo `m`.

Computes `Int.toNat (z % m)`; for `0 < m` this is the unique value in `[0, m)`
congruent to `z`. Used coefficientwise by `modP` and `reduceModPow` to land
integer coefficients in the standard representative window before transport
to `FpPoly` or back into `ZPoly`.
-/
@[expose]
def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

/-- `intModNat` is the canonical nonnegative representative: re-coercing to `Int`
recovers the ordinary integer remainder. Used to connect the `Nat`-valued executable
reduction with `Int`-level congruence reasoning. -/
private theorem intModNat_eq_emod (z : Int) {m : Nat} (hm : 0 < m) :
    Int.ofNat (intModNat z m) = z % (m : Int) := by
  unfold intModNat
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hm)))

/-- The canonical representative of `z` and `z` itself differ by a multiple of `m`.
Used to discharge the per-coefficient congruence obligation in `congr_reduceModPow`. -/
private theorem intModNat_sub_self_emod (z : Int) {m : Nat} (hm : 0 < m) :
    (Int.ofNat (intModNat z m) - z) % (m : Int) = 0 := by
  rw [intModNat_eq_emod z hm]
  exact Int.emod_eq_zero_of_dvd (Int.dvd_sub_self_of_emod_eq rfl)

/-- Congruent integers have the same canonical representative. Used coefficientwise to
prove that `reduceModPow` and `modP` are well-defined on congruence classes. -/
private theorem intModNat_eq_of_congr {a b : Int} {m : Nat} (h : (a - b) % (m : Int) = 0) :
    Int.ofNat (intModNat a m) = Int.ofNat (intModNat b m) := by
  have hmod : a % (m : Int) = b % (m : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr h
  simp [intModNat, hmod]

/-- Reduce the coefficients of an integer polynomial modulo `p`. -/
@[expose]
def modP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  FpPoly.ofCoeffs <|
    (List.range f.size).map (fun i => ZMod64.ofNat p (intModNat (f.coeff i) p)) |>.toArray

/-- Reduce each coefficient to its canonical representative modulo `p^k`. -/
@[expose]
def reduceModPow (f : ZPoly) (p k : Nat) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => Int.ofNat (intModNat (f.coeff i) (p ^ k))) |>.toArray

/-- Coefficientwise characterisation of `modP`: the `i`-th coefficient of the reduction
is the `ZMod64` image of the canonical representative of the original coefficient. -/
@[simp, grind =] theorem coeff_modP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) (i : Nat) :
    (modP p f).coeff i = ZMod64.ofNat p (intModNat (f.coeff i) p) := by
  unfold modP FpPoly.ofCoeffs
  rw [DensePoly.coeff_ofCoeffs_list, list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff, intModNat]
    change (ZMod64.zero : ZMod64 p) = ZMod64.ofNat p 0
    rfl

/-- Reducing the zero polynomial modulo `p` preserves zero. -/
@[simp, grind =] theorem modP_zero (p : Nat) [ZMod64.Bounds p] :
    modP p 0 = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_modP]
  have hcoeff : (0 : ZPoly).coeff i = 0 :=
    DensePoly.coeff_eq_zero_of_size_le (0 : ZPoly) (by simp)
  simp [hcoeff, intModNat]
  change (ZMod64.zero : ZMod64 p) = ZMod64.ofNat p 0
  rfl

/-- Coefficientwise characterisation of `reduceModPow`: each coefficient is replaced
by its canonical nonnegative representative in `[0, p^k)`. -/
@[simp, grind =] theorem coeff_reduceModPow (f : ZPoly) (p k i : Nat) :
    (reduceModPow f p k).coeff i = Int.ofNat (intModNat (f.coeff i) (p ^ k)) := by
  unfold reduceModPow
  rw [DensePoly.coeff_ofCoeffs_list, list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff, intModNat]
    rfl

/-- Reducing the zero polynomial modulo `p^k` preserves zero. -/
@[simp, grind =] theorem reduceModPow_zero (p k : Nat) :
    reduceModPow 0 p k = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_reduceModPow]
  have hcoeff : (0 : ZPoly).coeff i = 0 :=
    DensePoly.coeff_eq_zero_of_size_le (0 : ZPoly) (by simp)
  simp [hcoeff, intModNat]

/-- Reducing the integer one polynomial modulo a nontrivial power preserves one. -/
@[simp, grind =] theorem reduceModPow_one_of_nontrivial
    (p k : Nat) (hpk : 1 < p ^ k) :
    reduceModPow (1 : ZPoly) p k = 1 := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_reduceModPow]
  change
    Int.ofNat (intModNat (DensePoly.coeff (DensePoly.C (1 : Int)) i) (p ^ k)) =
      DensePoly.coeff (DensePoly.C (1 : Int)) i
  rw [DensePoly.coeff_C]
  cases i with
  | zero =>
      simp only [↓reduceIte]
      unfold intModNat
      rw [Int.emod_eq_of_lt]
      · rfl
      · decide
      · exact Int.ofNat_lt.mpr hpk
  | succ i =>
      change Int.ofNat (intModNat 0 (p ^ k)) = 0
      unfold intModNat
      rw [show (0 : Int) % Int.ofNat (p ^ k) = 0 by simp]
      rfl

/-- If a coefficient is already divisible by `p^k`, its `reduceModPow` image vanishes. -/
theorem coeff_reduceModPow_eq_zero_of_emod
    (f : ZPoly) (p k i : Nat)
    (hzero : f.coeff i % Int.ofNat (p ^ k) = 0) :
    (reduceModPow f p k).coeff i = 0 := by
  rw [coeff_reduceModPow]
  unfold intModNat
  rw [hzero]
  rfl

/-- For positive modulus `p^k`, the reduced coefficient equals the integer remainder
`f.coeff i % p^k`. Identifies the `Nat`-valued executable representative with `Int.emod`. -/
theorem coeff_reduceModPow_eq_emod_of_pos
    (f : ZPoly) (p k i : Nat) (hpk : 0 < p ^ k) :
    (reduceModPow f p k).coeff i = f.coeff i % Int.ofNat (p ^ k) := by
  rw [coeff_reduceModPow]
  exact intModNat_eq_emod (f.coeff i) hpk

/-- Coefficientwise reduction modulo `p^k` is congruent to the original polynomial. -/
theorem congr_reduceModPow (f : ZPoly) (p k : Nat) (hpk : 0 < p ^ k) :
    congr (reduceModPow f p k) f (p ^ k) := by
  intro i
  rw [coeff_reduceModPow]
  exact intModNat_sub_self_emod (f.coeff i) hpk

/-- Congruence is preserved by coefficientwise canonical reduction modulo `p^k`. -/
theorem congr_reduceModPow_of_congr (f g : ZPoly) (p k : Nat)
    (hfg : congr f g (p ^ k)) :
    reduceModPow f p k = reduceModPow g p k := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_reduceModPow, coeff_reduceModPow]
  exact intModNat_eq_of_congr (hfg i)

/-- Congruence modulo a larger modulus descends along divisibility of moduli. -/
theorem congr_of_dvd_modulus (f g : ZPoly) {m n : Nat}
    (hmn : m ∣ n)
    (hfg : congr f g n) :
    congr f g m := by
  intro i
  have hmnInt : (m : Int) ∣ (n : Int) := by
    exact_mod_cast hmn
  exact Int.emod_eq_zero_of_dvd
    (Int.dvd_trans hmnInt (Int.dvd_of_emod_eq_zero (hfg i)))

/-- Congruence modulo `p^b` descends to congruence modulo `p^a` for `a ≤ b`. -/
theorem congr_pow_of_le (p a b : Nat) (f g : ZPoly)
    (hab : a ≤ b)
    (hfg : congr f g (p ^ b)) :
    congr f g (p ^ a) :=
  congr_of_dvd_modulus f g (Nat.pow_dvd_pow p hab) hfg

/-- Alias oriented toward canonical reduction: congruent inputs have the same reduction. -/
theorem reduceModPow_eq_of_congr (f g : ZPoly) (p k : Nat)
    (hfg : congr f g (p ^ k)) :
    reduceModPow f p k = reduceModPow g p k :=
  congr_reduceModPow_of_congr f g p k hfg

/-- Reducing twice to the same positive modulus is idempotent. -/
theorem reduceModPow_idempotent (f : ZPoly) (p k : Nat) (hpk : 0 < p ^ k) :
    reduceModPow (reduceModPow f p k) p k = reduceModPow f p k :=
  reduceModPow_eq_of_congr (reduceModPow f p k) f p k
    (congr_reduceModPow f p k hpk)

/-- Canonical reduction modulo a positive power is idempotent. -/
@[simp, grind =] theorem reduceModPow_reduceModPow
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    reduceModPow (reduceModPow f p k) p k = reduceModPow f p k :=
  reduceModPow_idempotent f p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))

/-- Congruent integer polynomials have the same reduction modulo `p`. -/
theorem modP_eq_of_congr (p : Nat) [ZMod64.Bounds p] (f g : ZPoly)
    (hfg : congr f g p) :
    modP p f = modP p g := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_modP, coeff_modP]
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change
    (ZMod64.ofNat p (intModNat (f.coeff i) p)).toNat =
      (ZMod64.ofNat p (intModNat (g.coeff i) p)).toNat
  rw [ZMod64.toNat_ofNat, ZMod64.toNat_ofNat]
  have hnat :
      intModNat (f.coeff i) p = intModNat (g.coeff i) p := by
    exact Int.ofNat.inj (intModNat_eq_of_congr (hfg i))
  rw [hnat]

/-- Reducing modulo `p^(k+1)` does not change the reduction modulo `p`. -/
@[simp, grind =] theorem modP_reduceModPow
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    modP p (reduceModPow f p (k + 1)) = modP p f := by
  apply modP_eq_of_congr
  have hred :
      congr (reduceModPow f p (k + 1)) f (p ^ (k + 1)) :=
    congr_reduceModPow f p (k + 1) (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  have hred₁ :
      congr (reduceModPow f p (k + 1)) f (p ^ 1) :=
    congr_pow_of_le p 1 (k + 1) (reduceModPow f p (k + 1)) f (by omega) hred
  simpa using hred₁

/-- Reducing modulo any positive power of `p` does not change the reduction modulo `p`. -/
@[simp, grind =] theorem modP_reduceModPow_of_pos
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) (hk : 0 < k) :
    modP p (reduceModPow f p k) = modP p f := by
  cases k with
  | zero => cases hk
  | succ k =>
      simp

end ZPoly

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Lift `F_p` coefficients to their standard nonnegative integer representatives. -/
@[expose]
def liftToZ (f : FpPoly p) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => Int.ofNat (f.coeff i).toNat) |>.toArray

/-- Coefficientwise characterisation of `liftToZ`: each coefficient is the standard
nonnegative `Nat` representative of the corresponding `ZMod64` element. -/
@[simp, grind =] theorem coeff_liftToZ (f : FpPoly p) (i : Nat) :
    (liftToZ f).coeff i = Int.ofNat (f.coeff i).toNat := by
  unfold liftToZ
  rw [DensePoly.coeff_ofCoeffs_list, list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff]
    change (0 : Int) = Int.ofNat (ZMod64.zero : ZMod64 p).toNat
    rw [ZMod64.toNat_zero]
    rfl

/-- The canonical integer lift of the zero polynomial is zero. -/
@[simp, grind =] theorem liftToZ_zero :
    liftToZ (0 : FpPoly p) = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_liftToZ]
  have hcoeff : (0 : FpPoly p).coeff i = 0 :=
    DensePoly.coeff_eq_zero_of_size_le (0 : FpPoly p) (by simp)
  rw [hcoeff]
  change (Int.ofNat (ZMod64.zero : ZMod64 p).toNat) = 0
  rw [ZMod64.toNat_zero]
  rfl

/-- Reducing the canonical lift back modulo `p` recovers the original coefficient data. -/
theorem modP_liftToZ_coeff (f : FpPoly p) (i : Nat) :
    (ZPoly.modP p (liftToZ f)).coeff i = f.coeff i := by
  rw [ZPoly.coeff_modP, coeff_liftToZ]
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change (ZMod64.ofNat p (ZPoly.intModNat (Int.ofNat (f.coeff i).toNat) p)).toNat =
    (f.coeff i).toNat
  have hmod :
      ZPoly.intModNat (Int.ofNat (f.coeff i).toNat) p = (f.coeff i).toNat := by
    unfold ZPoly.intModNat
    rw [Int.emod_eq_of_lt]
    · rfl
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr (f.coeff i).toNat_lt
  rw [ZMod64.toNat_ofNat, hmod, Nat.mod_eq_of_lt (f.coeff i).toNat_lt]

/-- Reducing a canonical lift back modulo `p` recovers the original polynomial. -/
@[simp, grind =] theorem modP_liftToZ (f : FpPoly p) :
    ZPoly.modP p (liftToZ f) = f := by
  apply DensePoly.ext_coeff
  intro i
  exact modP_liftToZ_coeff f i

/-- Specialised `toNat` reduction for `(1 : ZMod64 p)` when `1 < p`, avoiding the
`1 % p` form that blocks rewriting in monicity proofs of `liftToZ`. -/
private theorem zmod64_toNat_one_of_one_lt (hp : 1 < p) :
    ZMod64.toNat (1 : ZMod64 p) = 1 := by
  rw [show (1 : ZMod64 p) = ZMod64.one from rfl, ZMod64.toNat_one, Nat.mod_eq_of_lt hp]

/-- Specialised `toNat` reduction for `(0 : ZMod64 p)`, dual to
`zmod64_toNat_one_of_one_lt`; lets monicity proofs derive `1 ≠ 0` from the lifted
representatives. -/
private theorem zmod64_toNat_zero :
    ZMod64.toNat (0 : ZMod64 p) = 0 := by
  rw [show (0 : ZMod64 p) = ZMod64.zero from rfl, ZMod64.toNat_zero]

/-- Size-positivity step for the monicity-preservation proof: a monic `FpPoly p`
with `1 < p` lifts to a `ZPoly` of positive size. Factored out to keep the
`leadingCoeff` rewrite in `monic_liftToZ_of_monic` linear. -/
private theorem liftToZ_size_pos_of_monic
    (f : FpPoly p)
    (hp : 1 < p)
    (hf : DensePoly.Monic f) :
    0 < (liftToZ f).size := by
  by_cases hpos : 0 < (liftToZ f).size
  · exact hpos
  have hsize : (liftToZ f).size = 0 := Nat.eq_zero_of_not_pos hpos
  have hcoeff_zero : (liftToZ f).coeff (f.size - 1) = 0 := by
    exact DensePoly.coeff_eq_zero_of_size_le (liftToZ f)
      (by rw [hsize]; exact Nat.zero_le _)
  have hf_pos : 0 < f.size := by
    by_cases hf_pos : 0 < f.size
    · exact hf_pos
    have hf_size : f.size = 0 := Nat.eq_zero_of_not_pos hf_pos
    have hlead_zero : f.leadingCoeff = 0 := by
      cases f with
      | mk coeffs normalized =>
          simp [DensePoly.size] at hf_size
          simp [DensePoly.leadingCoeff, hf_size]
          rfl
    have hlead_one : f.leadingCoeff = 1 := hf
    have hone_zero : (1 : ZMod64 p) = 0 := by
      rw [← hlead_one, hlead_zero]
    have hnat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat := congrArg ZMod64.toNat hone_zero
    rw [zmod64_toNat_one_of_one_lt hp, zmod64_toNat_zero] at hnat
    cases hnat
  have hlast : f.coeff (f.size - 1) = 1 := by
    rw [← DensePoly.leadingCoeff_eq_coeff_last f hf_pos]
    exact hf
  have hcoeff_one : (liftToZ f).coeff (f.size - 1) = 1 := by
    rw [coeff_liftToZ, hlast]
    change (Int.ofNat (ZMod64.toNat (1 : ZMod64 p)) : Int) = 1
    rw [zmod64_toNat_one_of_one_lt hp]
    rfl
  rw [hcoeff_one] at hcoeff_zero
  exact (Int.zero_ne_one hcoeff_zero.symm).elim

/--
The canonical integer lift of a monic polynomial over `F_p` is monic, provided
the modulus is nontrivial. The `1 < p` hypothesis is necessary because
`1 : ZMod64 1` has representative zero.
-/
theorem monic_liftToZ_of_monic
    (f : FpPoly p)
    (hp : 1 < p)
    (hf : DensePoly.Monic f) :
    DensePoly.Monic (liftToZ f) := by
  have hpos : 0 < (liftToZ f).size :=
    liftToZ_size_pos_of_monic f hp hf
  rw [DensePoly.Monic, DensePoly.leadingCoeff_eq_coeff_last (liftToZ f) hpos, coeff_liftToZ]
  have hf_pos : 0 < f.size := by
    by_cases hf_pos : 0 < f.size
    · exact hf_pos
    have hf_size : f.size = 0 := Nat.eq_zero_of_not_pos hf_pos
    have hlead_zero : f.leadingCoeff = 0 := by
      cases f with
      | mk coeffs normalized =>
          simp [DensePoly.size] at hf_size
          simp [DensePoly.leadingCoeff, hf_size]
          rfl
    have hlead_one : f.leadingCoeff = 1 := hf
    have hone_zero : (1 : ZMod64 p) = 0 := by
      rw [← hlead_one, hlead_zero]
    have hnat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat := congrArg ZMod64.toNat hone_zero
    rw [zmod64_toNat_one_of_one_lt hp, zmod64_toNat_zero] at hnat
    cases hnat
  have hlast : f.coeff (f.size - 1) = 1 := by
    rw [← DensePoly.leadingCoeff_eq_coeff_last f hf_pos]
    exact hf
  have hcoeff_one_at_f : (liftToZ f).coeff (f.size - 1) = 1 := by
    rw [coeff_liftToZ, hlast]
    change (Int.ofNat (ZMod64.toNat (1 : ZMod64 p)) : Int) = 1
    rw [zmod64_toNat_one_of_one_lt hp]
    rfl
  have hle : (liftToZ f).size ≤ f.size := by
    unfold liftToZ
    simpa using
      (DensePoly.size_ofCoeffs_le
        (((List.range f.size).map
          (fun i => Int.ofNat (f.coeff i).toNat)).toArray))
  have hge : f.size ≤ (liftToZ f).size := by
    by_cases hle_size : f.size ≤ (liftToZ f).size
    · exact hle_size
    have hlt_size : (liftToZ f).size < f.size := Nat.lt_of_not_ge hle_size
    have hle_idx : (liftToZ f).size ≤ f.size - 1 :=
      Nat.le_pred_of_lt hlt_size
    have hzero :
        (liftToZ f).coeff (f.size - 1) = 0 :=
      DensePoly.coeff_eq_zero_of_size_le (liftToZ f) hle_idx
    rw [hcoeff_one_at_f] at hzero
    exact (Int.zero_ne_one hzero.symm).elim
  have hsize_eq : (liftToZ f).size = f.size := Nat.le_antisymm hle hge
  have hidx : (liftToZ f).size - 1 = f.size - 1 := by
    rw [hsize_eq]
  rw [hidx, hlast]
  change (Int.ofNat (ZMod64.toNat (1 : ZMod64 p)) : Int) = 1
  rw [zmod64_toNat_one_of_one_lt hp]
  rfl

/-- A polynomial is congruent modulo `p` to the canonical integer lift of its reduction. -/
theorem congr_liftToZ_modP (f : ZPoly) :
    ZPoly.congr (liftToZ (ZPoly.modP p f)) f p := by
  intro i
  rw [coeff_liftToZ, ZPoly.coeff_modP, ZMod64.toNat_ofNat]
  have hp : 0 < p := ZMod64.Bounds.pPos (p := p)
  have hmod : ZPoly.intModNat (f.coeff i) p % p = ZPoly.intModNat (f.coeff i) p := by
    rw [Nat.mod_eq_of_lt]
    unfold ZPoly.intModNat
    have hlt :
        Int.toNat (f.coeff i % (p : Int)) < Int.toNat (p : Int) :=
      (Int.toNat_lt_toNat (by exact_mod_cast hp)).2
        (Int.emod_lt_of_pos _ (by exact_mod_cast hp))
    simpa using hlt
  rw [hmod]
  exact ZPoly.intModNat_sub_self_emod (f.coeff i) hp

end FpPoly

namespace ZPoly

/-- Reducing the integer `1` polynomial modulo `p` yields the `FpPoly p`
identity. Bottom-of-recursion case for the `modP p` rewrites used
by Hensel lifting modules. -/
@[simp, grind =] theorem modP_one (p : Nat) [ZMod64.Bounds p] :
    ZPoly.modP p (1 : ZPoly) = (1 : FpPoly p) := by
  have hcong : ZPoly.congr (FpPoly.liftToZ (1 : FpPoly p)) (1 : ZPoly) p := by
    intro i
    rw [FpPoly.coeff_liftToZ]
    change
      (Int.ofNat (DensePoly.coeff (DensePoly.C (1 : ZMod64 p)) i).toNat -
          DensePoly.coeff (DensePoly.C (1 : Int)) i) % (p : Int) = 0
    rw [DensePoly.coeff_C, DensePoly.coeff_C]
    cases i with
    | zero =>
        cases p with
        | zero =>
            cases Nat.not_lt_zero _ (ZMod64.Bounds.pPos (p := 0))
        | succ p' =>
            cases p' with
            | zero =>
                change (Int.ofNat (1 % 1) - 1) % (1 : Int) = 0
                simp
            | succ p'' =>
                have hlt : 1 < Nat.succ (Nat.succ p'') := by omega
                change
                  (Int.ofNat (1 % Nat.succ (Nat.succ p'')) - 1) %
                    (Nat.succ (Nat.succ p'') : Int) = 0
                simp [Nat.mod_eq_of_lt hlt]
    | succ i =>
        change (Int.ofNat 0 - (0 : Int)) % (p : Int) = 0
        simp
  exact Eq.trans (ZPoly.modP_eq_of_congr p _ _ (ZPoly.congr_symm _ _ _ hcong))
    (FpPoly.modP_liftToZ (p := p) (1 : FpPoly p))

end ZPoly

end Hex
