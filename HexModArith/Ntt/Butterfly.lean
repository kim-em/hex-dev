/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.Plan

public section

/-!
Bounded redundant residues and Harvey--Shoup butterfly arithmetic.

The raw types deliberately have no arithmetic instances: they are internal
transform-loop states whose only meaning is their canonical residue modulo
`p` together with an advertised redundant interval.
-/
namespace Hex

namespace ZMod64

/-- A raw transform word in the redundant interval `[0, 2p)`. -/
structure NttRaw2 (p : Nat) [Bounds p] where
  val : UInt64
  isLt : val.toNat < 2 * p

/-- A raw transform word in the redundant interval `[0, 4p)`. -/
structure NttRaw4 (p : Nat) [Bounds p] where
  val : UInt64
  isLt : val.toNat < 4 * p

namespace NttRaw2

/-- Raw forward words are equal when their backing words agree. -/
@[ext] theorem ext {p : Nat} [Bounds p] {left right : NttRaw2 p}
    (h : left.val = right.val) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- Enter the forward transform's redundant domain. -/
def ofZMod {p : Nat} [Bounds p] (value : ZMod64 p) : NttRaw2 p :=
  ⟨value.val, by
    have hv := value.isLt
    have hp := Bounds.pPos (p := p)
    omega⟩

/-- Canonical residue represented by a raw forward word. -/
def normalize {p : Nat} [Bounds p] (value : NttRaw2 p) : ZMod64 p :=
  ZMod64.ofNat p value.val.toNat

/-- Entering the forward raw domain and normalizing is the identity. -/
@[simp] theorem normalize_ofZMod {p : Nat} [Bounds p] (value : ZMod64 p) :
    (ofZMod value).normalize = value := by
  exact ZMod64.ofNat_toNat value

end NttRaw2

namespace NttRaw4

/-- Raw inverse words are equal when their backing words agree. -/
@[ext] theorem ext {p : Nat} [Bounds p] {left right : NttRaw4 p}
    (h : left.val = right.val) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- Enter the inverse transform's redundant domain. -/
def ofZMod {p : Nat} [Bounds p] (value : ZMod64 p) : NttRaw4 p :=
  ⟨value.val, by
    have hv := value.isLt
    have hp := Bounds.pPos (p := p)
    omega⟩

/-- Canonical residue represented by a raw inverse word. -/
def normalize {p : Nat} [Bounds p] (value : NttRaw4 p) : ZMod64 p :=
  ZMod64.ofNat p value.val.toNat

/-- Entering the inverse raw domain and normalizing is the identity. -/
@[simp] theorem normalize_ofZMod {p : Nat} [Bounds p] (value : ZMod64 p) :
    (ofZMod value).normalize = value := by
  exact ZMod64.ofNat_toNat value

end NttRaw4

namespace Ntt

/-- Nat-level quotient in Shoup multiplication. -/
def shoupQuot (w t p : Nat) : Nat :=
  (w * UInt64.word / p) * t / UInt64.word

/-- Redundant Shoup product `w*t - floor(floor(w*β/p)*t/β)*p`. -/
def shoupValue (w t p : Nat) : Nat :=
  w * t - shoupQuot w t p * p

private theorem shoupQuot_mul_le (w t p : Nat) :
    shoupQuot w t p * p ≤ w * t := by
  let precon := w * UInt64.word / p
  let quotient := precon * t / UInt64.word
  have hquotient : quotient * UInt64.word ≤ precon * t :=
    Nat.div_mul_le_self _ _
  have hprecon : precon * p ≤ w * UInt64.word :=
    Nat.div_mul_le_self _ _
  have hscaled : quotient * p * UInt64.word ≤ w * t * UInt64.word := by
    calc
      quotient * p * UInt64.word = quotient * UInt64.word * p := by ac_rfl
      _ ≤ (precon * t) * p := Nat.mul_le_mul_right p hquotient
      _ = (precon * p) * t := by ac_rfl
      _ ≤ (w * UInt64.word) * t := Nat.mul_le_mul_right t hprecon
      _ = w * t * UInt64.word := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hscaled (by decide : 0 < UInt64.word)

/-- Shoup multiplication without its final adjustment returns a representative
below `2p` when the multiplicand is below `4p`. -/
theorem shoupValue_lt {w t p : Nat}
    (hp : 0 < p) (hpWord : 4 * p < UInt64.word)
    (_hw : w < p) (ht : t < 4 * p) :
    shoupValue w t p < 2 * p := by
  let precon := w * UInt64.word / p
  let quotient := precon * t / UInt64.word
  let r := w * UInt64.word % p
  let s := precon * t % UInt64.word
  have hle : quotient * p ≤ w * t := by
    simpa [quotient, precon, shoupQuot] using shoupQuot_mul_le w t p
  have hr : r + p * precon = w * UInt64.word := by
    simpa [r, precon] using Nat.mod_add_div (w * UInt64.word) p
  have hs : s + UInt64.word * quotient = precon * t := by
    simpa [s, quotient] using Nat.mod_add_div (precon * t) UInt64.word
  have hdecomp :
      w * t * UInt64.word =
        (t * r + p * s) + quotient * p * UInt64.word := by
    calc
      w * t * UInt64.word = t * (w * UInt64.word) := by ac_rfl
      _ = t * (r + p * precon) := by rw [hr]
      _ = t * r + t * (p * precon) := by rw [Nat.mul_add]
      _ = t * r + p * (precon * t) := by ac_rfl
      _ = t * r + p * (s + UInt64.word * quotient) := by rw [hs]
      _ = (t * r + p * s) + quotient * p * UInt64.word := by
        rw [Nat.mul_add]
        ac_rfl
  have heq :
      (w * t - quotient * p) * UInt64.word = t * r + p * s := by
    rw [Nat.mul_sub_right_distrib]
    exact Nat.sub_eq_of_eq_add hdecomp
  have hrlt : r < p := Nat.mod_lt _ hp
  have hslt : s < UInt64.word := Nat.mod_lt _ (by decide)
  have htr : t * r < UInt64.word * p := by
    have h₁ : t * r < (4 * p) * p := Nat.mul_lt_mul'' ht hrlt
    have h₂ : (4 * p) * p < UInt64.word * p :=
      (Nat.mul_lt_mul_right hp).mpr hpWord
    exact Nat.lt_trans h₁ h₂
  have hps : p * s < p * UInt64.word :=
    (Nat.mul_lt_mul_left hp).mpr hslt
  have hsum : t * r + p * s < (2 * p) * UInt64.word := by
    calc
      t * r + p * s < UInt64.word * p + p * UInt64.word :=
        Nat.add_lt_add htr hps
      _ = p * UInt64.word + p * UInt64.word := by
        rw [Nat.mul_comm UInt64.word p]
      _ = (2 * p) * UInt64.word := by
        rw [Nat.two_mul, Nat.add_mul]
  apply (Nat.mul_lt_mul_right (by decide : 0 < UInt64.word)).mp
  rw [show shoupValue w t p = w * t - quotient * p by
    simp [shoupValue, shoupQuot, quotient, precon]]
  rw [heq]
  exact hsum

/-- The redundant Shoup product represents the ordinary product modulo `p`. -/
theorem shoupValue_mod {w t p : Nat} :
    shoupValue w t p % p = (w * t) % p := by
  have hle := shoupQuot_mul_le w t p
  have hadd : shoupValue w t p + shoupQuot w t p * p = w * t := by
    simp only [shoupValue]
    exact Nat.sub_add_cancel hle
  have hmod := congrArg (fun value : Nat => value % p) hadd
  simpa only [Nat.add_mul_mod_self_right] using hmod

/-- The small-modulus class leaves enough word room for a fourfold redundant
representative. -/
theorem four_mul_lt_word (p : Nat) [Bounds p] :
    4 * p < UInt64.word := by
  have hp := Bounds.pLtR (p := p)
  simpa [UInt64.word] using (show 4 * p < 2 ^ 64 by omega)

/-- Twice the modulus as a faithful machine word. -/
def twiceModulusWord (p : Nat) [Bounds p] : UInt64 :=
  UInt64.ofNatLT (2 * p) (by
    have hfour := four_mul_lt_word p
    have hp := Bounds.pPos (p := p)
    simpa [UInt64.word, UInt64.size] using (show 2 * p < UInt64.word by omega))

/-- Observation of the doubled modulus word. -/
@[simp] theorem twiceModulusWord_toNat (p : Nat) [Bounds p] :
    (twiceModulusWord p).toNat = 2 * p := by
  simp [twiceModulusWord]

private theorem toNat_add_of_lt_word (left right : UInt64)
    (h : left.toNat + right.toNat < UInt64.word) :
    (left + right).toNat = left.toNat + right.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by
    simpa [UInt64.word] using h)]

/-- Reduce a faithful representative below `4p` into `[0, 2p)` by at most
one word subtraction. -/
def reduceTwice (p : Nat) [Bounds p] (value : UInt64) : UInt64 :=
  if twiceModulusWord p ≤ value then value - twiceModulusWord p else value

/-- One-subtraction reduction agrees with reduction modulo `2p`. -/
theorem reduceTwice_toNat {p : Nat} [Bounds p] (value : UInt64)
    (hvalue : value.toNat < 4 * p) :
    (reduceTwice p value).toNat = value.toNat % (2 * p) := by
  unfold reduceTwice
  split
  · rename_i h
    have hle : 2 * p ≤ value.toNat := by
      simpa only [UInt64.le_iff_toNat_le, twiceModulusWord_toNat] using h
    rw [UInt64.toNat_sub_of_le _ _ h, twiceModulusWord_toNat,
      Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
  · rename_i h
    have hlt : value.toNat < 2 * p := by
      rw [← twiceModulusWord_toNat]
      exact Nat.lt_of_not_le (fun hle => h (UInt64.le_iff_toNat_le.mpr hle))
    exact (Nat.mod_eq_of_lt hlt).symm

/-- Reduce a faithful representative below `4p` into a bounded raw word. -/
def reduceTwiceRaw2 {p : Nat} [Bounds p] (value : UInt64)
    (hvalue : value.toNat < 4 * p) : NttRaw2 p :=
  ⟨reduceTwice p value, by
    rw [reduceTwice_toNat value hvalue]
    exact Nat.mod_lt _ (Nat.mul_pos (by decide) (Bounds.pPos (p := p)))⟩

/-- Raw observation of one-subtraction reduction. -/
@[simp] theorem reduceTwiceRaw2_toNat {p : Nat} [Bounds p]
    (value : UInt64) (hvalue : value.toNat < 4 * p) :
    (reduceTwiceRaw2 value hvalue).val.toNat = value.toNat % (2 * p) := by
  exact reduceTwice_toNat value hvalue

/-- Add `2p` and subtract a smaller raw representative without word wrap or
borrow. -/
def addTwiceSubWord (p : Nat) [Bounds p] (left right : UInt64) : UInt64 :=
  left + twiceModulusWord p - right

/-- Observation of the faithful `left + 2p - right` word expression. -/
theorem addTwiceSubWord_toNat {p : Nat} [Bounds p] (left right : UInt64)
    (hleft : left.toNat < 2 * p) (hright : right.toNat < 2 * p) :
    (addTwiceSubWord p left right).toNat =
      left.toNat + 2 * p - right.toNat := by
  have haddLt : left.toNat + (twiceModulusWord p).toNat < UInt64.word := by
    rw [twiceModulusWord_toNat]
    have hfour := four_mul_lt_word p
    omega
  have hadd := toNat_add_of_lt_word left (twiceModulusWord p) haddLt
  have hrightLe : right ≤ left + twiceModulusWord p := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hadd, twiceModulusWord_toNat]
    omega
  unfold addTwiceSubWord
  rw [UInt64.toNat_sub_of_le _ _ hrightLe, hadd, twiceModulusWord_toNat]

private theorem product_lt_word {p w t : Nat} [Bounds p]
    (hw : w < p) (ht : t < 4 * p) :
    w * t < UInt64.word := by
  have hp : p < 2 ^ 31 := Bounds.pLtR (p := p)
  have hp4 : 4 * p < 4 * 2 ^ 31 :=
    (Nat.mul_lt_mul_left (by decide : 0 < 4)).mpr hp
  have hprod : w * t < (2 ^ 31) * (4 * 2 ^ 31) :=
    Nat.lt_trans (Nat.mul_lt_mul'' hw ht) (Nat.mul_lt_mul'' hp hp4)
  exact Nat.lt_of_lt_of_le hprod (by decide)

/-- Logical Shoup multiplication, returning the unadjusted representative in
`[0, 2p)`. -/
@[expose]
def shoupMul {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) : NttRaw2 p := by
  let result := shoupValue twiddle.value.toNat value.val.toNat p
  have hresult : result < 2 * p :=
    shoupValue_lt (Bounds.pPos (p := p)) (four_mul_lt_word p)
      twiddle.value.toNat_lt value.isLt
  have hword : result < UInt64.size := by
    have htwo : 2 * p < UInt64.word := by
      have := four_mul_lt_word p
      have hp := Bounds.pPos (p := p)
      omega
    simpa [UInt64.word, UInt64.size] using Nat.lt_trans hresult htwo
  exact ⟨UInt64.ofNatLT result hword, by simpa using hresult⟩

/-- Nat observation of logical Shoup multiplication. -/
@[simp] theorem toNat_shoupMul {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) :
    (shoupMul twiddle value).val.toNat =
      shoupValue twiddle.value.toNat value.val.toNat p := by
  simp [shoupMul]

/-- Word implementation of Shoup multiplication, using the existing verified
high-word primitive. -/
def shoupWord {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) : UInt64 :=
  let quotient := UInt64.mulHi twiddle.precon value.val
  twiddle.value.val * value.val -
    quotient * modulusWord p (Bounds.pLtWord p)

/-- The word implementation agrees with the Nat-level Shoup formula. -/
theorem toNat_shoupWord {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) :
    (shoupWord twiddle value).toNat =
      shoupValue twiddle.value.toNat value.val.toNat p := by
  let quotient := UInt64.mulHi twiddle.precon value.val
  have hquotient : quotient.toNat =
      shoupQuot twiddle.value.toNat value.val.toNat p := by
    rw [show quotient.toNat =
        twiddle.precon.toNat * value.val.toNat / UInt64.word by
      exact UInt64.toNat_mulHi _ _]
    rw [twiddle.precon_eq]
    rfl
  have hproductLt : twiddle.value.toNat * value.val.toNat < UInt64.word :=
    product_lt_word twiddle.value.toNat_lt value.isLt
  have hproduct : (twiddle.value.val * value.val).toNat =
      twiddle.value.toNat * value.val.toNat := by
    rw [UInt64.toNat_mul]
    change (twiddle.value.toNat * value.val.toNat) % UInt64.word = _
    rw [Nat.mod_eq_of_lt hproductLt]
  have hle : shoupQuot twiddle.value.toNat value.val.toNat p * p ≤
      twiddle.value.toNat * value.val.toNat :=
    shoupQuot_mul_le _ _ _
  have hcorrectionLt :
      shoupQuot twiddle.value.toNat value.val.toNat p * p < UInt64.word :=
    Nat.lt_of_le_of_lt hle hproductLt
  have hmodulus : (modulusWord p (Bounds.pLtWord p)).toNat = p := by
    simp [modulusWord]
  have hcorrection :
      (quotient * modulusWord p (Bounds.pLtWord p)).toNat =
        shoupQuot twiddle.value.toNat value.val.toNat p * p := by
    rw [UInt64.toNat_mul, hquotient, hmodulus]
    change (shoupQuot twiddle.value.toNat value.val.toNat p * p) %
      UInt64.word = _
    rw [Nat.mod_eq_of_lt hcorrectionLt]
  have hwordLe : quotient * modulusWord p (Bounds.pLtWord p) ≤
      twiddle.value.val * value.val := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hcorrection, hproduct]
    exact hle
  unfold shoupWord
  dsimp only
  rw [UInt64.toNat_sub_of_le _ _ hwordLe, hproduct, hcorrection]
  rfl

/-- Compiled Shoup multiplication. -/
def shoupMulImpl {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) : NttRaw2 p :=
  ⟨shoupWord twiddle value, by
    rw [toNat_shoupWord]
    exact shoupValue_lt (Bounds.pPos (p := p)) (four_mul_lt_word p)
      twiddle.value.toNat_lt value.isLt⟩

/-- Nat observation of compiled Shoup multiplication. -/
@[simp] theorem toNat_shoupMulImpl {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) :
    (shoupMulImpl twiddle value).val.toNat =
      shoupValue twiddle.value.toNat value.val.toNat p := by
  exact toNat_shoupWord twiddle value

/-- Kernel-reducible and word-level Shoup multiplication agree. -/
@[csimp] theorem shoupMul_eq_impl : @shoupMul = @shoupMulImpl := by
  funext p _ twiddle value
  apply NttRaw2.ext
  apply UInt64.toNat_inj.mp
  rw [toNat_shoupMul]
  exact toNat_shoupWord twiddle value |>.symm

/-- Shoup multiplication has the canonical product residue. -/
theorem normalize_shoupMul {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) :
    (shoupMul twiddle value).normalize =
      twiddle.value * ZMod64.ofNat p value.val.toNat := by
  apply ZMod64.ext_toNat
  rw [NttRaw2.normalize, ZMod64.toNat_ofNat, toNat_shoupMul,
    shoupValue_mod]
  change (twiddle.value.toNat * value.val.toNat) % p =
    (ZMod64.mul twiddle.value (ZMod64.ofNat p value.val.toNat)).toNat
  rw [ZMod64.toNat_mul, ZMod64.toNat_ofNat, Nat.mul_mod,
    Nat.mod_eq_of_lt twiddle.value.toNat_lt]

def raw2OfNat {p : Nat} [Bounds p] (value : Nat) (h : value < 2 * p) :
    NttRaw2 p := by
  have hword : value < UInt64.size := by
    have htwo : 2 * p < UInt64.word := by
      have hfour := four_mul_lt_word p
      have hp := Bounds.pPos (p := p)
      omega
    simpa [UInt64.word, UInt64.size] using Nat.lt_trans h htwo
  exact ⟨UInt64.ofNatLT value hword, by simpa using h⟩

@[simp] theorem raw2OfNat_toNat {p : Nat} [Bounds p]
    (value : Nat) (h : value < 2 * p) :
    (raw2OfNat value h).val.toNat = value := by
  simp [raw2OfNat]

def raw4OfNat {p : Nat} [Bounds p] (value : Nat) (h : value < 4 * p) :
    NttRaw4 p := by
  have hword : value < UInt64.size := by
    simpa [UInt64.word, UInt64.size] using Nat.lt_trans h (four_mul_lt_word p)
  exact ⟨UInt64.ofNatLT value hword, by simpa using h⟩

@[simp] theorem raw4OfNat_toNat {p : Nat} [Bounds p]
    (value : Nat) (h : value < 4 * p) :
    (raw4OfNat value h).val.toNat = value := by
  simp [raw4OfNat]

private theorem ofNat_mod_two_mul {p value : Nat} [Bounds p] :
    ZMod64.ofNat p (value % (2 * p)) = ZMod64.ofNat p value := by
  apply ZMod64.ext_toNat
  rw [ZMod64.toNat_ofNat, ZMod64.toNat_ofNat]
  exact Nat.mod_mod_of_dvd value (Nat.dvd_mul_left p 2)

private theorem ofNat_add_double_sub {p x y : Nat} [Bounds p]
    (hy : y ≤ x + 2 * p) :
    ZMod64.ofNat p (x + 2 * p - y) =
      ZMod64.ofNat p x - ZMod64.ofNat p y := by
  have hsumNat : x + 2 * p - y + y = x + 2 * p :=
    Nat.sub_add_cancel hy
  have hsum :
      ZMod64.ofNat p (x + 2 * p - y) + ZMod64.ofNat p y =
        ZMod64.ofNat p x := by
    apply ZMod64.ext_toNat
    change (ZMod64.add (ZMod64.ofNat p (x + 2 * p - y))
      (ZMod64.ofNat p y)).toNat = (ZMod64.ofNat p x).toNat
    rw [ZMod64.toNat_add, ZMod64.toNat_ofNat, ZMod64.toNat_ofNat,
      ZMod64.toNat_ofNat]
    calc
      ((x + 2 * p - y) % p + y % p) % p =
          (x + 2 * p - y + y) % p := by
        exact (Nat.add_mod _ _ _).symm
      _ = (x + 2 * p) % p := by rw [hsumNat]
      _ = x % p := by
        rw [Nat.mul_comm 2 p]
        exact Nat.add_mul_mod_self_left x p 2
  symm
  exact Lean.Grind.AddCommGroup.sub_eq_iff.mpr hsum.symm

private theorem ofNat_shoupMul {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (value : NttRaw4 p) :
    ZMod64.ofNat p (shoupMul twiddle value).val.toNat =
      twiddle.value * ZMod64.ofNat p value.val.toNat := by
  simpa only [NttRaw2.normalize, NttRaw4.normalize] using
    normalize_shoupMul twiddle value

/-- Harvey's forward butterfly.  Inputs and outputs remain in `[0, 2p)`;
the second output uses an unadjusted Shoup product. -/
@[expose]
def forwardButterfly {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) : NttRaw2 p × NttRaw2 p := by
  let sum := (x.val.toNat + y.val.toNat) % (2 * p)
  have htwo : 0 < 2 * p := Nat.mul_pos (by decide) (Bounds.pPos (p := p))
  have hsum : sum < 2 * p := Nat.mod_lt _ htwo
  let difference := x.val.toNat + 2 * p - y.val.toNat
  have hydiff : y.val.toNat ≤ x.val.toNat + 2 * p := by
    have hy := y.isLt
    omega
  have hdifference : difference < 4 * p := by
    have hx := x.isLt
    have hp := Bounds.pPos (p := p)
    omega
  let product := shoupMul twiddle (raw4OfNat difference hdifference)
  exact (raw2OfNat sum hsum, product)

/-- Division-free word implementation of the forward butterfly. -/
def forwardButterflyImpl {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) : NttRaw2 p × NttRaw2 p := by
  let sumWord := x.val + y.val
  have hsumFaithful : sumWord.toNat = x.val.toNat + y.val.toNat := by
    apply toNat_add_of_lt_word
    have hfour := four_mul_lt_word p
    have hx := x.isLt
    have hy := y.isLt
    omega
  have hsum : sumWord.toNat < 4 * p := by
    rw [hsumFaithful]
    have hx := x.isLt
    have hy := y.isLt
    omega
  let differenceWord := addTwiceSubWord p x.val y.val
  have hdifferenceFaithful :
      differenceWord.toNat = x.val.toNat + 2 * p - y.val.toNat := by
    exact addTwiceSubWord_toNat x.val y.val x.isLt y.isLt
  have hdifference : differenceWord.toNat < 4 * p := by
    rw [hdifferenceFaithful]
    have hx := x.isLt
    have hy := y.isLt
    have hp := Bounds.pPos (p := p)
    omega
  exact
    (reduceTwiceRaw2 sumWord hsum,
      shoupMulImpl twiddle ⟨differenceWord, hdifference⟩)

/-- Raw observation of the logical forward sum. -/
@[simp] theorem toNat_forwardButterfly_fst {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) :
    (forwardButterfly twiddle x y).1.val.toNat =
      (x.val.toNat + y.val.toNat) % (2 * p) := by
  simp [forwardButterfly]

/-- Raw observation of the logical forward twiddled difference. -/
@[simp] theorem toNat_forwardButterfly_snd {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) :
    (forwardButterfly twiddle x y).2.val.toNat =
      shoupValue twiddle.value.toNat
        (x.val.toNat + 2 * p - y.val.toNat) p := by
  simp [forwardButterfly]

/-- Raw observation of the compiled forward sum. -/
@[simp] theorem toNat_forwardButterflyImpl_fst {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) :
    (forwardButterflyImpl twiddle x y).1.val.toNat =
      (x.val.toNat + y.val.toNat) % (2 * p) := by
  unfold forwardButterflyImpl
  dsimp only
  simp only [reduceTwiceRaw2]
  rw [reduceTwice_toNat _ (by
    rw [toNat_add_of_lt_word]
    · have hx := x.isLt
      have hy := y.isLt
      omega
    · have hfour := four_mul_lt_word p
      have hx := x.isLt
      have hy := y.isLt
      omega)]
  congr 1
  apply toNat_add_of_lt_word
  have hfour := four_mul_lt_word p
  have hx := x.isLt
  have hy := y.isLt
  omega

/-- Raw observation of the compiled forward twiddled difference. -/
@[simp] theorem toNat_forwardButterflyImpl_snd {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) :
    (forwardButterflyImpl twiddle x y).2.val.toNat =
      shoupValue twiddle.value.toNat
        (x.val.toNat + 2 * p - y.val.toNat) p := by
  unfold forwardButterflyImpl
  dsimp only
  rw [toNat_shoupMulImpl, addTwiceSubWord_toNat x.val y.val x.isLt y.isLt]

/-- The forward butterfly's kernel-reducible and division-free word
implementations agree. -/
@[csimp] theorem forwardButterfly_eq_impl :
    @forwardButterfly = @forwardButterflyImpl := by
  funext p _ twiddle x y
  apply Prod.ext
  · apply NttRaw2.ext
    apply UInt64.toNat_inj.mp
    rw [toNat_forwardButterfly_fst, toNat_forwardButterflyImpl_fst]
  · apply NttRaw2.ext
    apply UInt64.toNat_inj.mp
    rw [toNat_forwardButterfly_snd, toNat_forwardButterflyImpl_snd]

/-- The first forward output is the sum residue. -/
theorem normalize_forward_fst {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) :
    (forwardButterfly twiddle x y).1.normalize = x.normalize + y.normalize := by
  apply ZMod64.ext_toNat
  change (ZMod64.ofNat p _).toNat =
    (ZMod64.add (ZMod64.ofNat p x.val.toNat)
      (ZMod64.ofNat p y.val.toNat)).toNat
  rw [ZMod64.toNat_ofNat, ZMod64.toNat_add, ZMod64.toNat_ofNat,
    ZMod64.toNat_ofNat]
  simp only [forwardButterfly, raw2OfNat_toNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left p 2), Nat.add_mod]

/-- The second forward output is the twiddled difference residue. -/
theorem normalize_forward_snd {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw2 p) :
    (forwardButterfly twiddle x y).2.normalize =
      twiddle.value * (x.normalize - y.normalize) := by
  unfold forwardButterfly
  dsimp only
  rw [normalize_shoupMul, raw4OfNat_toNat,
    ofNat_add_double_sub (by have hy := y.isLt; omega)]
  rfl

/-- Harvey's inverse butterfly.  Inputs and outputs remain in `[0, 4p)`;
only the left input is reduced to `[0, 2p)` before the add/subtract pair. -/
@[expose]
def inverseButterfly {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) : NttRaw4 p × NttRaw4 p := by
  let reducedX := x.val.toNat % (2 * p)
  have htwo : 0 < 2 * p := Nat.mul_pos (by decide) (Bounds.pPos (p := p))
  have hreducedX : reducedX < 2 * p := Nat.mod_lt _ htwo
  let product := shoupMul twiddle y
  let sum := reducedX + product.val.toNat
  have hsum : sum < 4 * p := by
    have hproduct := product.isLt
    omega
  let difference := reducedX + 2 * p - product.val.toNat
  have hproductLe : product.val.toNat ≤ reducedX + 2 * p := by
    have hproduct := product.isLt
    omega
  have hdifference : difference < 4 * p := by
    have hreducedX' := hreducedX
    have hp := Bounds.pPos (p := p)
    omega
  exact (raw4OfNat sum hsum, raw4OfNat difference hdifference)

/-- Division-free word implementation of the inverse butterfly. -/
def inverseButterflyImpl {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) : NttRaw4 p × NttRaw4 p := by
  let reducedX := reduceTwiceRaw2 x.val x.isLt
  let product := shoupMulImpl twiddle y
  let sumWord := reducedX.val + product.val
  have hsumFaithful :
      sumWord.toNat = reducedX.val.toNat + product.val.toNat := by
    apply toNat_add_of_lt_word
    have hfour := four_mul_lt_word p
    have hx := reducedX.isLt
    have hp := product.isLt
    omega
  have hsum : sumWord.toNat < 4 * p := by
    rw [hsumFaithful]
    have hx := reducedX.isLt
    have hp := product.isLt
    omega
  let differenceWord := addTwiceSubWord p reducedX.val product.val
  have hdifferenceFaithful : differenceWord.toNat =
      reducedX.val.toNat + 2 * p - product.val.toNat := by
    exact addTwiceSubWord_toNat reducedX.val product.val
      reducedX.isLt product.isLt
  have hdifference : differenceWord.toNat < 4 * p := by
    rw [hdifferenceFaithful]
    have hx := reducedX.isLt
    have hp := product.isLt
    have hmod := Bounds.pPos (p := p)
    omega
  exact (⟨sumWord, hsum⟩, ⟨differenceWord, hdifference⟩)

/-- Raw observation of the logical inverse sum. -/
@[simp] theorem toNat_inverseButterfly_fst {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) :
    (inverseButterfly twiddle x y).1.val.toNat =
      x.val.toNat % (2 * p) +
        shoupValue twiddle.value.toNat y.val.toNat p := by
  simp [inverseButterfly]

/-- Raw observation of the logical inverse difference. -/
@[simp] theorem toNat_inverseButterfly_snd {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) :
    (inverseButterfly twiddle x y).2.val.toNat =
      x.val.toNat % (2 * p) + 2 * p -
        shoupValue twiddle.value.toNat y.val.toNat p := by
  simp [inverseButterfly]

/-- Raw observation of the compiled inverse sum. -/
@[simp] theorem toNat_inverseButterflyImpl_fst {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) :
    (inverseButterflyImpl twiddle x y).1.val.toNat =
      x.val.toNat % (2 * p) +
        shoupValue twiddle.value.toNat y.val.toNat p := by
  unfold inverseButterflyImpl
  dsimp only
  rw [toNat_add_of_lt_word, reduceTwiceRaw2_toNat, toNat_shoupMulImpl]
  have hfour := four_mul_lt_word p
  have hx := (reduceTwiceRaw2 x.val x.isLt).isLt
  have hp := (shoupMulImpl twiddle y).isLt
  omega

/-- Raw observation of the compiled inverse difference. -/
@[simp] theorem toNat_inverseButterflyImpl_snd {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) :
    (inverseButterflyImpl twiddle x y).2.val.toNat =
      x.val.toNat % (2 * p) + 2 * p -
        shoupValue twiddle.value.toNat y.val.toNat p := by
  unfold inverseButterflyImpl
  dsimp only
  rw [addTwiceSubWord_toNat _ _
      (reduceTwiceRaw2 x.val x.isLt).isLt (shoupMulImpl twiddle y).isLt,
    reduceTwiceRaw2_toNat, toNat_shoupMulImpl]

/-- The inverse butterfly's kernel-reducible and division-free word
implementations agree. -/
@[csimp] theorem inverseButterfly_eq_impl :
    @inverseButterfly = @inverseButterflyImpl := by
  funext p _ twiddle x y
  apply Prod.ext
  · apply NttRaw4.ext
    apply UInt64.toNat_inj.mp
    rw [toNat_inverseButterfly_fst, toNat_inverseButterflyImpl_fst]
  · apply NttRaw4.ext
    apply UInt64.toNat_inj.mp
    rw [toNat_inverseButterfly_snd, toNat_inverseButterflyImpl_snd]

/-- The first inverse output is the sum with the twiddled right input. -/
theorem normalize_inverse_fst {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) :
    (inverseButterfly twiddle x y).1.normalize =
      x.normalize + twiddle.value * y.normalize := by
  unfold inverseButterfly
  dsimp only
  apply ZMod64.ext_toNat
  change (ZMod64.ofNat p _).toNat =
    (ZMod64.add (ZMod64.ofNat p x.val.toNat)
      (ZMod64.mul twiddle.value (ZMod64.ofNat p y.val.toNat))).toNat
  rw [raw4OfNat_toNat, ZMod64.toNat_ofNat, ZMod64.toNat_add,
    ZMod64.toNat_ofNat, ZMod64.toNat_mul, ZMod64.toNat_ofNat,
    toNat_shoupMul, Nat.add_mod,
    Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left p 2), shoupValue_mod,
    Nat.mul_mod, Nat.mod_eq_of_lt twiddle.value.toNat_lt]

/-- The second inverse output is the corresponding difference. -/
theorem normalize_inverse_snd {p : Nat} [Bounds p]
    (twiddle : NttTwiddle p) (x y : NttRaw4 p) :
    (inverseButterfly twiddle x y).2.normalize =
      x.normalize - twiddle.value * y.normalize := by
  unfold inverseButterfly
  dsimp only
  unfold NttRaw4.normalize
  rw [raw4OfNat_toNat,
    ofNat_add_double_sub (by
      have hproduct := (shoupMul twiddle y).isLt
      omega),
    ofNat_mod_two_mul, ofNat_shoupMul]

end Ntt

end ZMod64

end Hex
