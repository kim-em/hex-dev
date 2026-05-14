import HexPolyFp
import HexPolyZ

/-!
Core bridge operations for executable Hensel lifting.

This module connects the integer polynomial surface from `HexPolyZ` with the
prime-field polynomial surface from `HexPolyFp`, exposing the coefficientwise
reductions and lifts that later Hensel steps reuse.
-/
namespace Hex

private theorem list_getD_map_range {α : Type} [Zero α] (size n : Nat) (f : Nat → α) :
    ((List.range size).map f).getD n (Zero.zero : α) =
      if n < size then f n else (Zero.zero : α) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

namespace ZPoly

def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

private theorem intModNat_eq_emod (z : Int) {m : Nat} (hm : 0 < m) :
    Int.ofNat (intModNat z m) = z % (m : Int) := by
  unfold intModNat
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hm)))

private theorem intModNat_sub_self_emod (z : Int) {m : Nat} (hm : 0 < m) :
    (Int.ofNat (intModNat z m) - z) % (m : Int) = 0 := by
  rw [intModNat_eq_emod z hm]
  exact Int.emod_eq_zero_of_dvd (Int.dvd_sub_self_of_emod_eq rfl)

private theorem intModNat_eq_of_congr {a b : Int} {m : Nat} (h : (a - b) % (m : Int) = 0) :
    Int.ofNat (intModNat a m) = Int.ofNat (intModNat b m) := by
  have hmod : a % (m : Int) = b % (m : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr h
  simp [intModNat, hmod]

/-- Reduce the coefficients of an integer polynomial modulo `p`. -/
def modP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  FpPoly.ofCoeffs <|
    (List.range f.size).map (fun i => ZMod64.ofNat p (intModNat (f.coeff i) p)) |>.toArray

/-- Reduce each coefficient to its canonical representative modulo `p^k`. -/
def reduceModPow (f : ZPoly) (p k : Nat) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => Int.ofNat (intModNat (f.coeff i) (p ^ k))) |>.toArray

@[simp] theorem coeff_modP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) (i : Nat) :
    (modP p f).coeff i = ZMod64.ofNat p (intModNat (f.coeff i) p) := by
  unfold modP FpPoly.ofCoeffs
  rw [DensePoly.coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff, intModNat]
    change (ZMod64.zero : ZMod64 p) = ZMod64.ofNat p 0
    rfl

@[simp] theorem coeff_reduceModPow (f : ZPoly) (p k i : Nat) :
    (reduceModPow f p k).coeff i = Int.ofNat (intModNat (f.coeff i) (p ^ k)) := by
  unfold reduceModPow
  rw [DensePoly.coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff, intModNat]
    rfl

theorem coeff_reduceModPow_eq_zero_of_emod
    (f : ZPoly) (p k i : Nat)
    (hzero : f.coeff i % Int.ofNat (p ^ k) = 0) :
    (reduceModPow f p k).coeff i = 0 := by
  rw [coeff_reduceModPow]
  unfold intModNat
  rw [hzero]
  rfl

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
theorem modP_reduceModPow
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

end ZPoly

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Lift `F_p` coefficients to their standard nonnegative integer representatives. -/
def liftToZ (f : FpPoly p) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => Int.ofNat (f.coeff i).toNat) |>.toArray

@[simp] theorem coeff_liftToZ (f : FpPoly p) (i : Nat) :
    (liftToZ f).coeff i = Int.ofNat (f.coeff i).toNat := by
  unfold liftToZ
  rw [DensePoly.coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff]
    change (0 : Int) = Int.ofNat (ZMod64.zero : ZMod64 p).toNat
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
theorem modP_liftToZ (f : FpPoly p) :
    ZPoly.modP p (liftToZ f) = f := by
  apply DensePoly.ext_coeff
  intro i
  exact modP_liftToZ_coeff f i

/-- A polynomial is congruent modulo `p` to the canonical integer lift of its reduction. -/
theorem congr_liftToZ_modP (f : ZPoly) :
    ZPoly.congr (liftToZ (ZPoly.modP p f)) f p := by
  intro i
  rw [coeff_liftToZ, ZPoly.coeff_modP]
  rw [ZMod64.toNat_ofNat]
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

/-- The canonical integer lift is congruent to itself after reduction modulo `p^k`. -/
theorem congr_reduceModPow_liftToZ (f : FpPoly p) (k : Nat) :
    ZPoly.congr (ZPoly.reduceModPow (liftToZ f) p k) (liftToZ f) (p ^ k) := by
  simpa using
    ZPoly.congr_reduceModPow (liftToZ f) p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))

end FpPoly

end Hex
