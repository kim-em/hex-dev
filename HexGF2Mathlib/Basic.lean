import HexGF2
import HexPolyFp
import Mathlib.Data.Nat.Bitwise

/-!
Correspondence definitions between packed `Hex.GF2Poly` values and the generic
`Hex.FpPoly 2` representation.

This module exposes the concrete unpack/repack conversions between the
bit-packed `GF(2)` polynomial execution path and the generic dense polynomial
over `Hex.ZMod64 2`, together with the ring equivalence and immediate simp
lemmas needed by later `GF(2^n)` correspondence modules.
-/

namespace HexGF2Mathlib

open Hex

universe u v w

/-! A minimal project-local equivalence structure used by the correspondence
modules without depending on Mathlib's heavier equivalence hierarchy. -/
structure TypeEquiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

namespace TypeEquiv

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Compose project-local type equivalences. -/
def trans (e₁ : TypeEquiv α β) (e₂ : TypeEquiv β γ) : TypeEquiv α γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  left_inv := by
    intro x
    exact (congrArg e₁.invFun (e₂.left_inv (e₁.toFun x))).trans (e₁.left_inv x)
  right_inv := by
    intro x
    exact (congrArg e₂.toFun (e₁.right_inv (e₂.invFun x))).trans (e₂.right_inv x)

end TypeEquiv

/-! A minimal project-local ring equivalence structure for executable algebra
types that have not imported Mathlib's heavier equivalence hierarchy. -/
structure RingEquiv (R : Type u) (S : Type v) [Mul R] [Mul S] [Add R] [Add S] where
  toFun : R → S
  invFun : S → R
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  map_mul' : ∀ a b : R, toFun (a * b) = toFun a * toFun b
  map_add' : ∀ a b : R, toFun (a + b) = toFun a + toFun b

infixl:25 " ≃+* " => RingEquiv

namespace RingEquiv

variable {R : Type u} {S : Type v} [Mul R] [Mul S] [Add R] [Add S]

instance : CoeFun (R ≃+* S) (fun _ => R → S) where
  coe e := e.toFun

/-- The inverse of a project-local ring equivalence. -/
def symm (e : R ≃+* S) : S ≃+* R where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_mul' := by
    intro a b
    have h := e.map_mul' (e.invFun a) (e.invFun b)
    rw [e.right_inv a, e.right_inv b] at h
    rw [← h, e.left_inv]
  map_add' := by
    intro a b
    have h := e.map_add' (e.invFun a) (e.invFun b)
    rw [e.right_inv a, e.right_inv b] at h
    rw [← h, e.left_inv]

end RingEquiv

namespace GF2Poly

instance : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩

/-- Interpret a packed `GF2Poly` coefficient as the corresponding `ZMod64 2`
residue. -/
private def coeffToFp (b : Bool) : Hex.ZMod64 2 :=
  if b then Hex.ZMod64.one else Hex.ZMod64.zero

/-- Pack a `ZMod64 2` coefficient into a single bit. -/
private def coeffOfFp (a : Hex.ZMod64 2) : UInt64 :=
  if a = Hex.ZMod64.zero then 0 else 1

/-- Unpack a packed `GF2Poly` into the generic dense polynomial over
`Hex.ZMod64 2`. -/
def toFpPoly (p : Hex.GF2Poly) : Hex.FpPoly 2 :=
  let coeffs :=
    if p.isZero then
      #[]
    else
      ((List.range (p.degree + 1)).map fun i => coeffToFp (p.coeff i)).toArray
  Hex.FpPoly.ofCoeffs coeffs

/-- Pack the coefficients of a single 64-term `FpPoly 2` segment into one
machine word. -/
private def packWord (p : Hex.FpPoly 2) (wordIdx : Nat) : UInt64 :=
  (List.range 64).foldl
    (fun acc bitIdx =>
      let coeff := p.coeff (64 * wordIdx + bitIdx)
      let bit := coeffOfFp coeff <<< bitIdx.toUInt64
      acc ||| bit)
    0

/-- Repack a generic dense polynomial over `Hex.ZMod64 2` into the packed
`GF2Poly` representation. -/
def ofFpPoly (p : Hex.FpPoly 2) : Hex.GF2Poly :=
  let wordCount := (p.size + 63) / 64
  let words := Array.ofFn fun i : Fin wordCount => packWord p i.1
  Hex.GF2Poly.ofWords words

/-- The `i`-th coefficient of `toFpPoly p` is the `ZMod64 2` lift of the packed
bit `p.coeff i`. -/
theorem coeff_toFpPoly (p : Hex.GF2Poly) (i : Nat) :
    (toFpPoly p).coeff i = if p.coeff i then (1 : Hex.ZMod64 2) else 0 := by
  have hcoeffToFp : ∀ b : Bool, coeffToFp b = if b then (1 : Hex.ZMod64 2) else 0 := by
    intro b; cases b <;> rfl
  by_cases hz : p.isZero = true
  · have hbody : toFpPoly p = Hex.FpPoly.ofCoeffs (#[] : Array (Hex.ZMod64 2)) := by
      unfold toFpPoly; rw [if_pos hz]
    rw [hbody, Hex.FpPoly.ofCoeffs, Hex.DensePoly.coeff_ofCoeffs,
      Hex.GF2Poly.eq_zero_of_isZero hz, Hex.GF2Poly.coeff_zero]
    rfl
  · have hbody : toFpPoly p =
        Hex.FpPoly.ofCoeffs
          ((List.range (p.degree + 1)).map (fun j => coeffToFp (p.coeff j))).toArray := by
      unfold toFpPoly; rw [if_neg hz]
    rw [hbody, Hex.FpPoly.ofCoeffs, Hex.DensePoly.coeff_ofCoeffs_list]
    have hrange :
        ((List.range (p.degree + 1)).map (fun j => coeffToFp (p.coeff j))).getD i
          (Zero.zero : Hex.ZMod64 2) =
          if i < p.degree + 1 then coeffToFp (p.coeff i)
          else (Zero.zero : Hex.ZMod64 2) := by
      by_cases hi : i < p.degree + 1 <;> simp [hi, List.getD]
    rw [hrange]
    by_cases hi : i < p.degree + 1
    · rw [if_pos hi, hcoeffToFp]
    · rw [if_neg hi]
      have hzf : p.isZero = false := by
        cases hb : p.isZero with
        | false => rfl
        | true => exact absurd hb hz
      obtain ⟨d, hd⟩ := Hex.GF2Poly.degree?_isSome_of_isZero_false hzf
      have hdd : p.degree = d := Hex.GF2Poly.degree_eq_of_degree?_eq_some hd
      have hcoeff : p.coeff i = false :=
        Hex.GF2Poly.coeff_eq_false_of_degree?_lt hd (by omega)
      rw [hcoeff]
      rfl

@[simp]
theorem toFpPoly_zero :
    toFpPoly (0 : Hex.GF2Poly) = 0 := by
  rfl

@[simp]
theorem ofFpPoly_zero :
    ofFpPoly (0 : Hex.FpPoly 2) = 0 := by
  rfl

@[simp]
theorem toFpPoly_one :
    toFpPoly (1 : Hex.GF2Poly) = 1 := by
  sorry

@[simp]
theorem ofFpPoly_toFpPoly (p : Hex.GF2Poly) :
    ofFpPoly (toFpPoly p) = p := by
  sorry

@[simp]
theorem toFpPoly_ofFpPoly (p : Hex.FpPoly 2) :
    toFpPoly (ofFpPoly p) = p := by
  sorry

@[simp]
theorem toFpPoly_add (p q : Hex.GF2Poly) :
    toFpPoly (p + q) = toFpPoly p + toFpPoly q := by
  sorry

@[simp]
theorem toFpPoly_mul (p q : Hex.GF2Poly) :
    toFpPoly (p * q) = toFpPoly p * toFpPoly q := by
  sorry

/-- The packed `GF2Poly` representation is ring-equivalent to the generic
degree-normalized `FpPoly 2` representation. -/
def equiv : Hex.GF2Poly ≃+* Hex.FpPoly 2 where
  toFun := toFpPoly
  invFun := ofFpPoly
  left_inv := ofFpPoly_toFpPoly
  right_inv := toFpPoly_ofFpPoly
  map_mul' := toFpPoly_mul
  map_add' := toFpPoly_add

@[simp]
theorem equiv_apply (p : Hex.GF2Poly) :
    equiv p = toFpPoly p := by
  rfl

@[simp]
theorem equiv_symm_apply (p : Hex.FpPoly 2) :
    RingEquiv.symm equiv p = ofFpPoly p := by
  rfl

/-- Interpret a packed polynomial as the natural number with the same binary
coefficient bits. This gives correspondence modules a finite index for
bounded-degree representatives without changing the executable `HexGF2`
representation. -/
private def wordsToNatAux : List UInt64 → Nat → Nat
  | [], _ => 0
  | w :: ws, i => w.toNat * 2 ^ (64 * i) + wordsToNatAux ws (i + 1)

def toNat (p : Hex.GF2Poly) : Nat :=
  wordsToNatAux p.toWords.toList 0

private theorem bit_eq_one_eq_testBit (x i : Nat) :
    (x >>> i % 2 == 1) = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

private theorem testBit_add_of_dvd_high {x y j : Nat}
    (hy : 2 ^ (j + 1) ∣ y) :
    (x + y).testBit j = x.testBit j := by
  have hmod : (x + y) % 2 ^ (j + 1) = x % 2 ^ (j + 1) := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hy, Nat.add_zero, Nat.mod_mod]
  calc
    (x + y).testBit j = ((x + y) % 2 ^ (j + 1)).testBit j := by
      rw [Nat.testBit_mod_two_pow]
      simp
    _ = (x % 2 ^ (j + 1)).testBit j := by rw [hmod]
    _ = x.testBit j := by
      rw [Nat.testBit_mod_two_pow]
      simp

private theorem add_shift_testBit (x k s t : Nat) (hx : x < 2 ^ s) :
    (x + k * 2 ^ s).testBit (s + t) = k.testBit t := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm k (2 ^ s)]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt hx, Nat.zero_add]

private theorem shift_testBit (k s t : Nat) :
    (k * 2 ^ s).testBit (s + t) = k.testBit t := by
  simpa using add_shift_testBit 0 k s t (Nat.two_pow_pos s)

private theorem testBit_add_of_lt_low {x y s t : Nat}
    (hx : x < 2 ^ s) (hy : 2 ^ s ∣ y) :
    (x + y).testBit (s + t) = y.testBit (s + t) := by
  rcases hy with ⟨k, hk⟩
  rw [hk, Nat.mul_comm]
  rw [add_shift_testBit x k s t hx, shift_testBit k s t]

private theorem wordsToNatAux_dvd_shift :
    ∀ (ws : List UInt64) (i : Nat), 2 ^ (64 * i) ∣ wordsToNatAux ws i
  | [], i => by simp [wordsToNatAux]
  | w :: ws, i => by
      unfold wordsToNatAux
      have htail' : 2 ^ (64 * i) ∣ wordsToNatAux ws (i + 1) :=
        dvd_trans (Nat.pow_dvd_pow 2 (by omega : 64 * i ≤ 64 * (i + 1)))
          (wordsToNatAux_dvd_shift ws (i + 1))
      rcases htail' with ⟨tail, htail⟩
      exact ⟨w.toNat + tail, by
        rw [htail, Nat.mul_add, Nat.mul_comm (2 ^ (64 * i)) w.toNat]⟩

private theorem word_shift_testBit (w : UInt64) (i bitIdx : Nat) :
    (w.toNat * 2 ^ (64 * i)).testBit (64 * i + bitIdx) =
      w.toNat.testBit bitIdx := by
  simpa using shift_testBit w.toNat (64 * i) bitIdx

private theorem word_shift_lt_next (w : UInt64) (i : Nat) :
    w.toNat * 2 ^ (64 * i) < 2 ^ (64 * (i + 1)) := by
  have hw : w.toNat < 2 ^ 64 := by
    simpa [UInt64.size] using UInt64.toNat_lt_size w
  have h := Nat.shiftLeft_lt (x := w.toNat) (n := 64) (m := 64 * i) hw
  simpa [Nat.shiftLeft_eq, show 64 + 64 * i = 64 * (i + 1) by omega] using h

private theorem word_shift_testBit_eq_false_of_next_le
    (w : UInt64) {i j : Nat} (hj : 64 * (i + 1) ≤ j) :
    (w.toNat * 2 ^ (64 * i)).testBit j = false := by
  exact Nat.testBit_eq_false_of_lt
    (Nat.lt_of_lt_of_le (word_shift_lt_next w i)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hj))

private theorem wordsToNatAux_testBit_getD :
    ∀ (ws : List UInt64) (i wordIdx bitIdx : Nat), bitIdx < 64 →
      (wordsToNatAux ws i).testBit (64 * (i + wordIdx) + bitIdx) =
        (ws.getD wordIdx 0).toNat.testBit bitIdx
  | [], i, wordIdx, bitIdx, hbit => by
      simp [wordsToNatAux]
  | w :: ws, i, 0, bitIdx, hbit => by
      simp only [wordsToNatAux]
      have htarget :
          64 * (i + 0) + bitIdx + 1 ≤ 64 * (i + 1) := by omega
      have htail :
          2 ^ (64 * (i + 0) + bitIdx + 1) ∣ wordsToNatAux ws (i + 1) :=
        dvd_trans (Nat.pow_dvd_pow 2 htarget) (wordsToNatAux_dvd_shift ws (i + 1))
      rw [testBit_add_of_dvd_high htail]
      simpa using word_shift_testBit w i bitIdx
  | w :: ws, i, wordIdx + 1, bitIdx, hbit => by
      simp only [wordsToNatAux]
      have htarget :
          64 * (i + (wordIdx + 1)) + bitIdx =
            64 * ((i + 1) + wordIdx) + bitIdx := by omega
      have hlowBound :
          w.toNat * 2 ^ (64 * i) <
            2 ^ (64 * (i + (wordIdx + 1)) + bitIdx) := by
        exact Nat.lt_of_lt_of_le (word_shift_lt_next w i)
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
      have htargetLow :
          64 * (i + (wordIdx + 1)) + bitIdx =
            64 * (i + 1) + (64 * wordIdx + bitIdx) := by omega
      rw [htargetLow]
      rw [testBit_add_of_lt_low (s := 64 * (i + 1)) (t := 64 * wordIdx + bitIdx)]
      · rw [← htargetLow, htarget]
        exact wordsToNatAux_testBit_getD ws (i + 1) wordIdx bitIdx hbit
      · exact Nat.lt_of_lt_of_le (word_shift_lt_next w i) (le_rfl)
      · exact wordsToNatAux_dvd_shift ws (i + 1)

theorem toNat_testBit_eq_coeff (p : Hex.GF2Poly) (j : Nat) :
    (toNat p).testBit j = p.coeff j := by
  unfold toNat
  rw [Hex.GF2Poly.coeff]
  have hbit : j % 64 < 64 := Nat.mod_lt j (by decide : 0 < 64)
  have hdecomp : 64 * (0 + j / 64) + j % 64 = j := by
    simpa using Nat.div_add_mod j 64
  rw [← hdecomp]
  rw [wordsToNatAux_testBit_getD p.toWords.toList 0 (j / 64) (j % 64) hbit]
  have hdiv : (64 * (j / 64) + j % 64) / 64 = j / 64 := by
    rw [Nat.mul_add_div (by decide : 64 > 0), Nat.div_eq_of_lt hbit, Nat.add_zero]
  simp [Hex.GF2Poly.coeffWords, Hex.GF2Poly.UInt64.bne_zero_eq_toNat_bne_zero,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hbit,
    bit_eq_one_eq_testBit, Hex.GF2Poly.toWords, hdiv]

/-- Rebuild the low `degree` bits of a natural number as a packed polynomial.
The input is expected to be bounded by `2 ^ degree` by callers that need a
canonical finite representative. -/
def ofNatBelowDegree (degree : Nat) (n : Nat) : Hex.GF2Poly :=
  let wordCount := (degree + 63) / 64
  Hex.GF2Poly.ofWords <|
    Array.ofFn fun i : Fin wordCount =>
      UInt64.ofNat (n / 2 ^ (64 * i.1))

private theorem div_word_mod_testBit (n wordIdx bitIdx : Nat) (hbit : bitIdx < 64) :
    ((n / 2 ^ (64 * wordIdx)) % 2 ^ 64).testBit bitIdx =
      n.testBit (64 * wordIdx + bitIdx) := by
  rw [Nat.testBit_mod_two_pow]
  simp [hbit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    Nat.pow_add]

private theorem div_word_testBit (n wordIdx bitIdx : Nat) (hbit : bitIdx < 64) :
    (UInt64.ofNat (n / 2 ^ (64 * wordIdx))).toNat.testBit bitIdx =
      n.testBit (64 * wordIdx + bitIdx) := by
  rw [UInt64.toNat_ofNat']
  exact div_word_mod_testBit n wordIdx bitIdx hbit

private theorem div_lt_wordCount_of_lt_degree {degree j : Nat} (hj : j < degree) :
    j / 64 < (degree + 63) / 64 := by
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 64)]
  have hceil : degree ≤ ((degree + 63) / 64) * 64 := by
    have hmod := Nat.mod_lt degree (by decide : 0 < 64)
    rw [← Nat.div_add_mod degree 64]
    omega
  omega

theorem coeff_ofNatBelowDegree_of_lt (degree n j : Nat) (hj : j < degree) :
    (ofNatBelowDegree degree n).coeff j = n.testBit j := by
  unfold ofNatBelowDegree
  rw [Hex.GF2Poly.coeff_ofWords]
  have hword : j / 64 < (degree + 63) / 64 := div_lt_wordCount_of_lt_degree hj
  have hget :
      (Array.ofFn
          (fun i : Fin ((degree + 63) / 64) =>
            UInt64.ofNat (n / 2 ^ (64 * i.1))))[j / 64]? =
        some (UInt64.ofNat (n / 2 ^ (64 * (j / 64)))) := by
    simp [hword]
  have hbit : j % 64 < 64 := Nat.mod_lt j (by decide : 0 < 64)
  have hdecomp : 64 * (j / 64) + j % 64 = j := by
    exact Nat.div_add_mod j 64
  simp [Hex.GF2Poly.coeffWords, hget, Hex.GF2Poly.UInt64.bne_zero_eq_toNat_bne_zero,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hbit,
    bit_eq_one_eq_testBit]
  change ((n / 2 ^ (64 * (j / 64))) % 2 ^ 64).testBit (j % 64) = n.testBit j
  rw [div_word_mod_testBit n (j / 64) (j % 64) hbit, hdecomp]

theorem coeff_ofNatBelowDegree_eq_false_of_bound
    {degree n j : Nat} (hn : n < 2 ^ degree) (hj : degree ≤ j) :
    (ofNatBelowDegree degree n).coeff j = false := by
  by_cases hword : j / 64 < (degree + 63) / 64
  · unfold ofNatBelowDegree
    rw [Hex.GF2Poly.coeff_ofWords]
    have hget :
        (Array.ofFn
            (fun i : Fin ((degree + 63) / 64) =>
              UInt64.ofNat (n / 2 ^ (64 * i.1))))[j / 64]? =
          some (UInt64.ofNat (n / 2 ^ (64 * (j / 64)))) := by
      simp [hword]
    have hbit : j % 64 < 64 := Nat.mod_lt j (by decide : 0 < 64)
    have hdecomp : 64 * (j / 64) + j % 64 = j := by
      exact Nat.div_add_mod j 64
    simp [Hex.GF2Poly.coeffWords, hget, Hex.GF2Poly.UInt64.bne_zero_eq_toNat_bne_zero,
      UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hbit,
      bit_eq_one_eq_testBit]
    change ((n / 2 ^ (64 * (j / 64))) % 2 ^ 64).testBit (j % 64) = false
    rw [div_word_mod_testBit n (j / 64) (j % 64) hbit, hdecomp]
    exact Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hn
      (Nat.pow_le_pow_right (by decide : 0 < 2) hj))
  · unfold ofNatBelowDegree
    rw [Hex.GF2Poly.coeff_ofWords]
    have hget :
        (Array.ofFn
            (fun i : Fin ((degree + 63) / 64) =>
              UInt64.ofNat (n / 2 ^ (64 * i.1))))[j / 64]? = none := by
      rw [Array.getElem?_eq_none_iff]
      simpa [Array.size_ofFn] using Nat.le_of_not_gt hword
    simp [Hex.GF2Poly.coeffWords, hget]

/-- A reduced polynomial (zero, or of degree `< degree`) has every coefficient
at index `≥ degree` clear. -/
private theorem coeff_eq_false_of_degree_le {p : Hex.GF2Poly} {degree j : Nat}
    (h : p.IsZero ∨ p.degree < degree) (hj : degree ≤ j) :
    p.coeff j = false := by
  rcases h with hzero | hlt
  · rw [Hex.GF2Poly.eq_zero_of_isZero hzero]
    exact Hex.GF2Poly.coeff_zero j
  · by_cases hpz : p.isZero = true
    · rw [Hex.GF2Poly.eq_zero_of_isZero hpz]
      exact Hex.GF2Poly.coeff_zero j
    · have hpz' : p.isZero = false := by
        cases hb : p.isZero with
        | true => exact absurd hb hpz
        | false => rfl
      obtain ⟨d, hd⟩ := Hex.GF2Poly.degree?_isSome_of_isZero_false hpz'
      have hdeg : p.degree = d := Hex.GF2Poly.degree_eq_of_degree?_eq_some hd
      exact Hex.GF2Poly.coeff_eq_false_of_degree?_lt hd (by omega)

/-- A polynomial known to have degree `< degree` has an index below
`2 ^ degree` under the packed binary interpretation. -/
theorem toNat_lt_of_degree_lt {p : Hex.GF2Poly} {degree : Nat}
    (h : p.IsZero ∨ p.degree < degree) :
    toNat p < 2 ^ degree := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [toNat_testBit_eq_coeff]
  exact coeff_eq_false_of_degree_le h hj

/-- Decoding a bounded index as low binary bits produces a reduced packed
representative for that degree bound. -/
theorem ofNatBelowDegree_reduced (degree : Nat) (i : Fin (2 ^ degree)) :
    (ofNatBelowDegree degree i.1).IsZero ∨
      (ofNatBelowDegree degree i.1).degree < degree := by
  by_cases hz : (ofNatBelowDegree degree i.1).isZero = true
  · exact Or.inl hz
  · right
    have hz' : (ofNatBelowDegree degree i.1).isZero = false := by
      cases hb : (ofNatBelowDegree degree i.1).isZero with
      | true => exact absurd hb hz
      | false => rfl
    obtain ⟨d, hd⟩ := Hex.GF2Poly.degree?_isSome_of_isZero_false hz'
    have hdeg : (ofNatBelowDegree degree i.1).degree = d :=
      Hex.GF2Poly.degree_eq_of_degree?_eq_some hd
    rw [hdeg]
    by_contra hge
    have hfalse : (ofNatBelowDegree degree i.1).coeff d = false :=
      coeff_ofNatBelowDegree_eq_false_of_bound i.2 (Nat.le_of_not_gt hge)
    have htrue : (ofNatBelowDegree degree i.1).coeff d = true :=
      Hex.GF2Poly.coeff_eq_true_of_degree?_eq_some hd
    rw [htrue] at hfalse
    contradiction

/-- Encoding after decoding a bounded packed index preserves the index. -/
theorem toNat_ofNatBelowDegree (degree : Nat) (i : Fin (2 ^ degree)) :
    toNat (ofNatBelowDegree degree i.1) = i.1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [toNat_testBit_eq_coeff]
  by_cases hj : j < degree
  · exact coeff_ofNatBelowDegree_of_lt degree i.1 j hj
  · have hge : degree ≤ j := Nat.le_of_not_gt hj
    rw [coeff_ofNatBelowDegree_eq_false_of_bound i.2 hge]
    symm
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le i.2 (Nat.pow_le_pow_right (by decide : 0 < 2) hge)

/-- Decoding after encoding a reduced packed representative preserves the
polynomial. -/
theorem ofNatBelowDegree_toNat {p : Hex.GF2Poly} {degree : Nat}
    (h : p.IsZero ∨ p.degree < degree) :
    ofNatBelowDegree degree (toNat p) = p := by
  have hbound : toNat p < 2 ^ degree := toNat_lt_of_degree_lt h
  apply Hex.GF2Poly.ext_coeff
  intro j
  by_cases hj : j < degree
  · rw [coeff_ofNatBelowDegree_of_lt degree (toNat p) j hj, toNat_testBit_eq_coeff]
  · have hge : degree ≤ j := Nat.le_of_not_gt hj
    rw [coeff_ofNatBelowDegree_eq_false_of_bound hbound hge,
      coeff_eq_false_of_degree_le h hge]

end GF2Poly

end HexGF2Mathlib
