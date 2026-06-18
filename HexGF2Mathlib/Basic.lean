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

/-- Rebuild the low `degree` bits of a natural number as a packed polynomial.
The input is expected to be bounded by `2 ^ degree` by callers that need a
canonical finite representative. -/
def ofNatBelowDegree (degree : Nat) (n : Nat) : Hex.GF2Poly :=
  let wordCount := (degree + 63) / 64
  Hex.GF2Poly.ofWords <|
    Array.ofFn fun i : Fin wordCount =>
      UInt64.ofNat (n / 2 ^ (64 * i.1))

private theorem bit_eq_one_eq_testBit (x i : Nat) :
    (x >>> i % 2 == 1) = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

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

/-- A polynomial known to have degree `< degree` has an index below
`2 ^ degree` under the packed binary interpretation. -/
theorem toNat_lt_of_degree_lt {p : Hex.GF2Poly} {degree : Nat}
    (h : p.IsZero ∨ p.degree < degree) :
    toNat p < 2 ^ degree := by
  sorry

/-- Decoding a bounded index as low binary bits produces a reduced packed
representative for that degree bound. -/
theorem ofNatBelowDegree_reduced (degree : Nat) (i : Fin (2 ^ degree)) :
    (ofNatBelowDegree degree i.1).IsZero ∨
      (ofNatBelowDegree degree i.1).degree < degree := by
  sorry

/-- Encoding after decoding a bounded packed index preserves the index. -/
theorem toNat_ofNatBelowDegree (degree : Nat) (i : Fin (2 ^ degree)) :
    toNat (ofNatBelowDegree degree i.1) = i.1 := by
  sorry

/-- Decoding after encoding a reduced packed representative preserves the
polynomial. -/
theorem ofNatBelowDegree_toNat {p : Hex.GF2Poly} {degree : Nat}
    (h : p.IsZero ∨ p.degree < degree) :
    ofNatBelowDegree degree (toNat p) = p := by
  sorry

end GF2Poly

end HexGF2Mathlib
