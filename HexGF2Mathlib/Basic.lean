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

private theorem bit_eq_one_eq_testBit (x i : Nat) :
    (x >>> i % 2 == 1) = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

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

@[simp, grind =]
theorem toFpPoly_zero :
    toFpPoly (0 : Hex.GF2Poly) = 0 := by
  rfl

@[simp, grind =]
theorem ofFpPoly_zero :
    ofFpPoly (0 : Hex.FpPoly 2) = 0 := by
  rfl

/-- The coefficients of the packed unit polynomial are `1` at degree `0` and
`0` elsewhere. -/
private theorem coeff_one_eq (i : Nat) :
    (1 : Hex.GF2Poly).coeff i = decide (i = 0) := by
  rw [← Hex.GF2Poly.ofUInt64_one]
  by_cases hi : i < 64
  · rw [Hex.GF2Poly.coeff_ofUInt64_eq_testBit 1 hi]
    have h1 : (1 : UInt64).toNat = 1 := by decide
    rw [h1]
    cases i with
    | zero => rfl
    | succ j => simp [Nat.testBit_succ]
  · rw [Hex.GF2Poly.coeff_ofUInt64_eq_false_of_ge_64 1 (Nat.le_of_not_gt hi)]
    have : i ≠ 0 := by omega
    simp [this]

@[simp, grind =]
theorem toFpPoly_one :
    toFpPoly (1 : Hex.GF2Poly) = 1 := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [coeff_toFpPoly, coeff_one_eq]
  show _ = (Hex.DensePoly.C (1 : Hex.ZMod64 2)).coeff i
  rw [Hex.DensePoly.coeff_C]
  by_cases hi : i = 0
  · subst hi; rfl
  · simp only [decide_eq_true_eq, if_neg hi]; rfl

/-- A packed coefficient bit `coeffOfFp a` holds at most one set bit. -/
private theorem coeffOfFp_toNat_lt (a : Hex.ZMod64 2) : (coeffOfFp a).toNat < 2 := by
  unfold coeffOfFp
  by_cases h : a = Hex.ZMod64.zero <;> simp [h] <;> decide

/-- The low bit of a packed coefficient records whether the source coefficient
is nonzero. -/
private theorem coeffOfFp_testBit_zero (a : Hex.ZMod64 2) :
    (coeffOfFp a).toNat.testBit 0 = decide (a ≠ 0) := by
  unfold coeffOfFp
  by_cases h : a = Hex.ZMod64.zero
  · have ha0 : a = 0 := h
    rw [if_pos h, ha0]; decide
  · have ha0 : a ≠ 0 := h
    rw [if_neg h]; simp [ha0]

private theorem zmod2_toNat_zero : (0 : Hex.ZMod64 2).toNat = 0 :=
  Hex.ZMod64.toNat_zero

private theorem zmod2_toNat_one : (1 : Hex.ZMod64 2).toNat = 1 := by
  show (Hex.ZMod64.one : Hex.ZMod64 2).toNat = 1
  rw [Hex.ZMod64.toNat_one]

private theorem zmod2_one_ne_zero : (1 : Hex.ZMod64 2) ≠ 0 := by
  intro h
  have := congrArg Hex.ZMod64.toNat h
  rw [zmod2_toNat_one, zmod2_toNat_zero] at this
  exact absurd this (by decide)

/-- Every `ZMod64 2` residue is either `0` or `1`. -/
private theorem zmod2_cases (a : Hex.ZMod64 2) : a = 0 ∨ a = 1 := by
  have hcases : a.toNat = 0 ∨ a.toNat = 1 := by have := a.toNat_lt; omega
  rcases hcases with h | h
  · left; exact Hex.ZMod64.ext_toNat (by rw [h, zmod2_toNat_zero])
  · right; exact Hex.ZMod64.ext_toNat (by rw [h, zmod2_toNat_one])

/-- The `b`-th bit of the partial OR-fold building `packWord` for the first `n`
bit positions is set exactly when `b < n` and the source coefficient at that
position is nonzero. -/
private theorem packWord_foldl_testBit (p : Hex.FpPoly 2) (wordIdx : Nat) :
    ∀ n, n ≤ 64 → ∀ b, b < 64 →
      ((List.range n).foldl
        (fun acc bitIdx =>
          acc ||| (coeffOfFp (p.coeff (64 * wordIdx + bitIdx)) <<< bitIdx.toUInt64)) 0).toNat.testBit b
        = (decide (b < n) && decide (p.coeff (64 * wordIdx + b) ≠ 0)) := by
  intro n
  induction n with
  | zero => intro _ b _; simp [List.range_zero]
  | succ n ih =>
    intro hn b hb
    have hnlt : n < 64 := by omega
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [UInt64.toNat_or, Nat.testBit_or, ih (by omega) b hb]
    have hc2 : (coeffOfFp (p.coeff (64 * wordIdx + n))).toNat < 2 := coeffOfFp_toNat_lt _
    have hshift :
        ((coeffOfFp (p.coeff (64 * wordIdx + n)) <<< n.toUInt64).toNat).testBit b
          = (decide (n ≤ b) &&
              (coeffOfFp (p.coeff (64 * wordIdx + n))).toNat.testBit (b - n)) := by
      rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
      have hnu : (n.toUInt64).toNat % 64 = n := by simp; omega
      rw [hnu]
      simp [hb]
    rw [hshift]
    rcases Nat.lt_trichotomy b n with hbn | hbn | hbn
    · have h1 : ¬ (n ≤ b) := by omega
      simp [hbn, Nat.lt_succ_of_lt hbn, h1]
    · subst hbn
      rw [Nat.sub_self, coeffOfFp_testBit_zero]
      simp [Nat.lt_succ_self]
    · have h1 : ¬ (b < n) := by omega
      have h2 : ¬ (b < n + 1) := by omega
      have h4 : (coeffOfFp (p.coeff (64 * wordIdx + n))).toNat.testBit (b - n) = false := by
        apply Nat.testBit_eq_false_of_lt
        have h2le : (2 : Nat) ≤ 2 ^ (b - n) := by
          calc (2 : Nat) = 2 ^ 1 := rfl
            _ ≤ 2 ^ (b - n) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      simp [h1, h2, h4]

/-- Bit `b` of a single packed word records whether the source coefficient at
that position is nonzero. -/
private theorem packWord_testBit (p : Hex.FpPoly 2) (wordIdx b : Nat) (hb : b < 64) :
    (packWord p wordIdx).toNat.testBit b = decide (p.coeff (64 * wordIdx + b) ≠ 0) := by
  unfold packWord
  rw [packWord_foldl_testBit p wordIdx 64 (le_refl 64) b hb]
  simp [hb]

/-- The `j`-th coefficient of the repacked polynomial records whether the
generic coefficient `p.coeff j` is nonzero. -/
theorem coeff_ofFpPoly (p : Hex.FpPoly 2) (j : Nat) :
    (ofFpPoly p).coeff j = decide (p.coeff j ≠ 0) := by
  unfold ofFpPoly
  rw [Hex.GF2Poly.coeff_ofWords]
  have hbit : j % 64 < 64 := Nat.mod_lt j (by decide : 0 < 64)
  have hdecomp : 64 * (j / 64) + j % 64 = j := Nat.div_add_mod j 64
  by_cases hword : j / 64 < (p.size + 63) / 64
  · have hget :
        (Array.ofFn (fun i : Fin ((p.size + 63) / 64) => packWord p i.1))[j / 64]? =
          some (packWord p (j / 64)) := by
      simp [hword]
    simp [Hex.GF2Poly.coeffWords, hget, Hex.GF2Poly.UInt64.bne_zero_eq_toNat_bne_zero,
      UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hbit,
      bit_eq_one_eq_testBit]
    rw [packWord_testBit p (j / 64) (j % 64) hbit, hdecomp]
    simp
  · have hget :
        (Array.ofFn (fun i : Fin ((p.size + 63) / 64) => packWord p i.1))[j / 64]? = none := by
      rw [Array.getElem?_eq_none_iff]
      simpa [Array.size_ofFn] using Nat.le_of_not_gt hword
    have hsize : p.size ≤ j := by
      have hm : (p.size + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
      have hceil := Nat.div_add_mod (p.size + 63) 64
      have hge : (p.size + 63) / 64 ≤ j / 64 := Nat.le_of_not_gt hword
      have hjd := Nat.div_add_mod j 64
      omega
    have hpc : p.coeff j = (Zero.zero : Hex.ZMod64 2) :=
      Hex.DensePoly.coeff_eq_zero_of_size_le p hsize
    have hz : p.coeff j = 0 := hpc
    simp [Hex.GF2Poly.coeffWords, hget, hz]

@[simp, grind =]
theorem ofFpPoly_toFpPoly (p : Hex.GF2Poly) :
    ofFpPoly (toFpPoly p) = p := by
  apply Hex.GF2Poly.ext_coeff
  intro j
  rw [coeff_ofFpPoly, coeff_toFpPoly]
  cases p.coeff j with
  | false => simp
  | true => simp [zmod2_one_ne_zero]

@[simp, grind =]
theorem toFpPoly_ofFpPoly (p : Hex.FpPoly 2) :
    toFpPoly (ofFpPoly p) = p := by
  apply Hex.DensePoly.ext_coeff
  intro j
  rw [coeff_toFpPoly, coeff_ofFpPoly]
  rcases zmod2_cases (p.coeff j) with hz | ho
  · simp [hz]
  · simp [ho, zmod2_one_ne_zero]

@[simp, grind =]
theorem toFpPoly_add (p q : Hex.GF2Poly) :
    toFpPoly (p + q) = toFpPoly p + toFpPoly q := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [Hex.DensePoly.coeff_add_semiring (toFpPoly p) (toFpPoly q) i,
    coeff_toFpPoly, coeff_toFpPoly, coeff_toFpPoly, Hex.GF2Poly.coeff_add_eq_bne]
  cases p.coeff i <;> cases q.coeff i <;> (try simp) <;> grind

/-- The `ZMod64 2` indicator of a bit, as a canonical residue. -/
private theorem chi_eq_ofNat (b : Bool) :
    (if b then (1 : Hex.ZMod64 2) else 0) = Hex.ZMod64.ofNat 2 (if b then 1 else 0) := by
  cases b <;> rfl

/-- Indicators multiply by the `AND` of the bits (`ZMod64 2` multiplication is
`AND` on `0/1` residues). -/
private theorem chi_mul (b c : Bool) :
    (if b && c then (1 : Hex.ZMod64 2) else 0) =
      (if b then (1 : Hex.ZMod64 2) else 0) * (if c then 1 else 0) := by
  rw [chi_eq_ofNat b, chi_eq_ofNat c, chi_eq_ofNat (b && c)]
  apply Hex.ZMod64.ext_toNat
  simp only [Hex.ZMod64.toNat_mul, Hex.ZMod64.toNat_ofNat]
  cases b <;> cases c <;> decide

/-- Indicators add by the `XOR` of the bits (`ZMod64 2` addition is `XOR` on
`0/1` residues: `1 + 1 = 0`). -/
private theorem chi_xor (b c : Bool) :
    (if (b != c) then (1 : Hex.ZMod64 2) else 0) =
      (if b then (1 : Hex.ZMod64 2) else 0) + (if c then 1 else 0) := by
  rw [chi_eq_ofNat b, chi_eq_ofNat c, chi_eq_ofNat (b != c)]
  apply Hex.ZMod64.ext_toNat
  simp only [Hex.ZMod64.toNat_add, Hex.ZMod64.toNat_ofNat]
  cases b <;> cases c <;> decide

/-- `ZMod64 2` is an additive monoid with `0` on the right. -/
private theorem zmod2_add_zero (x : Hex.ZMod64 2) : x + 0 = x := by grind

/-- Left absorption in `ZMod64 2`. -/
private theorem zmod2_zero_mul (x : Hex.ZMod64 2) : (0 : Hex.ZMod64 2) * x = 0 := by grind

/-- The `ZMod64 2` indicator of an XOR-fold equals the running sum of the
per-bit indicators: addition realizes the parity fold. -/
private theorem chi_foldl_aux (l : List Bool) (init : Bool) :
    (if (l.foldl (fun a b => a != b) init) then (1 : Hex.ZMod64 2) else 0) =
      l.foldl (fun acc b => acc + (if b then (1 : Hex.ZMod64 2) else 0))
        (if init then 1 else 0) := by
  induction l generalizing init with
  | nil => rfl
  | cons b bs ih =>
      show (if (bs.foldl (fun a b => a != b) (init != b)) then (1 : Hex.ZMod64 2) else 0) =
        bs.foldl (fun acc b => acc + (if b then (1 : Hex.ZMod64 2) else 0))
          ((if init then (1 : Hex.ZMod64 2) else 0) + (if b then 1 else 0))
      rw [ih (init != b), chi_xor init b]

private theorem chi_foldl (l : List Bool) :
    (if (l.foldl (fun a b => a != b) false) then (1 : Hex.ZMod64 2) else 0) =
      l.foldl (fun acc b => acc + (if b then (1 : Hex.ZMod64 2) else 0)) 0 := by
  have h := chi_foldl_aux l false
  simpa using h

/-- Congruence for an additive fold: step functions that agree on the list
elements produce equal folds. -/
private theorem foldl_add_congr (l : List Nat) (f g : Nat → Hex.ZMod64 2)
    (h : ∀ s ∈ l, f s = g s) (init : Hex.ZMod64 2) :
    l.foldl (fun acc s => acc + f s) init = l.foldl (fun acc s => acc + g s) init := by
  induction l generalizing init with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.foldl_cons]
      rw [h s (by simp)]
      exact ih (fun x hx => h x (by simp [hx])) _

/-- Extending an additive fold past a point where every term vanishes leaves the
sum unchanged. -/
private theorem foldl_add_range_reduce (term : Nat → Hex.ZMod64 2) (m : Nat)
    (hzero : ∀ i, m ≤ i → term i = 0) :
    ∀ d, (List.range (m + d)).foldl (fun acc i => acc + term i) 0 =
      (List.range m).foldl (fun acc i => acc + term i) 0
  | 0 => by simp
  | d + 1 => by
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hzero (m + d) (by omega), zmod2_add_zero,
        foldl_add_range_reduce term m hzero d]

private theorem foldl_add_range_eq_of_ge (term : Nat → Hex.ZMod64 2) (A B m : Nat)
    (hzero : ∀ i, m ≤ i → term i = 0) (hA : m ≤ A) (hB : m ≤ B) :
    (List.range A).foldl (fun acc i => acc + term i) 0 =
      (List.range B).foldl (fun acc i => acc + term i) 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, A = m + a := ⟨A - m, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = m + b := ⟨B - m, by omega⟩
  rw [foldl_add_range_reduce term m hzero a, foldl_add_range_reduce term m hzero b]

@[simp, grind =]
theorem toFpPoly_mul (p q : Hex.GF2Poly) :
    toFpPoly (p * q) = toFpPoly p * toFpPoly q := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [coeff_toFpPoly, Hex.GF2Poly.coeff_mul_diagonal, Hex.FpPoly.coeff_mul]
  -- `coeff_mul_diagonal` reports its parity through the private `xorBoolList`
  -- wrapper, definitionally the raw XOR fold that `chi_foldl` rewrites; the
  -- `show` exposes that fold so the rewrite fires.
  show (if (List.map (fun s => p.coeff s && q.coeff (n - s)) (List.range (n + 1))).foldl
          (fun a b => a != b) false then (1 : Hex.ZMod64 2) else 0) =
      (toFpPoly p).mulCoeffSum (toFpPoly q) n
  rw [chi_foldl]
  simp only [List.foldl_map]
  have hterm : ∀ s ∈ List.range (n + 1),
      (if (p.coeff s && q.coeff (n - s)) then (1 : Hex.ZMod64 2) else 0) =
        Hex.FpPoly.mulCoeffTerm (toFpPoly p) (toFpPoly q) n s := by
    intro s hs
    have hsn : s ≤ n := by have := List.mem_range.mp hs; omega
    rw [chi_mul, ← coeff_toFpPoly, ← coeff_toFpPoly]
    unfold Hex.FpPoly.mulCoeffTerm
    rw [if_neg (by omega : ¬ n < s)]
  rw [foldl_add_congr (List.range (n + 1)) _ _ hterm 0]
  have hzero : ∀ i, min ((toFpPoly p).size) (n + 1) ≤ i →
      Hex.FpPoly.mulCoeffTerm (toFpPoly p) (toFpPoly q) n i = 0 := by
    intro i hi
    unfold Hex.FpPoly.mulCoeffTerm
    by_cases hni : n < i
    · rw [if_pos hni]
    · rw [if_neg hni]
      have hcase : (toFpPoly p).size ≤ i ∨ n + 1 ≤ i := by
        rcases Nat.le_total ((toFpPoly p).size) (n + 1) with hle | hle
        · left; rw [Nat.min_eq_left hle] at hi; exact hi
        · right; rw [Nat.min_eq_right hle] at hi; exact hi
      rcases hcase with h | h
      · rw [Hex.DensePoly.coeff_eq_zero_of_size_le (toFpPoly p) h]
        exact zmod2_zero_mul _
      · exact absurd (by omega : n < i) hni
  unfold Hex.FpPoly.mulCoeffSum
  exact foldl_add_range_eq_of_ge
    (fun i => Hex.FpPoly.mulCoeffTerm (toFpPoly p) (toFpPoly q) n i)
    (n + 1) ((toFpPoly p).size) (min ((toFpPoly p).size) (n + 1))
    hzero (Nat.min_le_right _ _) (Nat.min_le_left _ _)

/-- The packed `GF2Poly` representation is ring-equivalent to the generic
degree-normalized `FpPoly 2` representation. -/
def equiv : Hex.GF2Poly ≃+* Hex.FpPoly 2 where
  toFun := toFpPoly
  invFun := ofFpPoly
  left_inv := ofFpPoly_toFpPoly
  right_inv := toFpPoly_ofFpPoly
  map_mul' := toFpPoly_mul
  map_add' := toFpPoly_add

@[simp, grind =]
theorem equiv_apply (p : Hex.GF2Poly) :
    equiv p = toFpPoly p := by
  rfl

@[simp, grind =]
theorem equiv_symm_apply (p : Hex.FpPoly 2) :
    RingEquiv.symm equiv p = ofFpPoly p := by
  rfl

/-- `toFpPoly` is injective: `ofFpPoly` is a left inverse. -/
theorem toFpPoly_injective : Function.Injective toFpPoly :=
  Function.LeftInverse.injective ofFpPoly_toFpPoly

/-- A dense polynomial over `ZMod64 2` whose coefficient at `d` is nonzero and
which vanishes strictly above `d` has degree exactly `d`. -/
private theorem fpPoly_degree?_eq_some_of_coeff (q : Hex.FpPoly 2) {d : Nat}
    (hd : q.coeff d ≠ 0) (hgt : ∀ n, d < n → q.coeff n = 0) :
    q.degree? = some d := by
  have hdlt : d < q.size := by
    by_contra h
    exact hd (Hex.DensePoly.coeff_eq_zero_of_size_le q (Nat.le_of_not_lt h))
  have hpos : 0 < q.size := Nat.lt_of_le_of_lt (Nat.zero_le d) hdlt
  have hlast := Hex.DensePoly.coeff_last_ne_zero_of_pos_size q hpos
  have hle : q.size - 1 ≤ d := by
    by_contra h
    exact hlast (hgt (q.size - 1) (Nat.lt_of_not_le h))
  have hsize : q.size - 1 = d := by omega
  rw [Hex.DensePoly.degree?_eq_some_of_pos_size q hpos, hsize]

/-- `toFpPoly` preserves `degree?`: the high bit of a packed polynomial becomes
the leading `ZMod64 2` coefficient, and everything above it vanishes. -/
theorem degree?_toFpPoly (p : Hex.GF2Poly) :
    (toFpPoly p).degree? = p.degree? := by
  by_cases hz : p.isZero = true
  · rw [Hex.GF2Poly.eq_zero_of_isZero hz, toFpPoly_zero,
      Hex.DensePoly.degree?_zero, Hex.GF2Poly.degree?_zero]
  · have hzf : p.isZero = false := by
      cases hb : p.isZero with
      | false => rfl
      | true => exact absurd hb hz
    obtain ⟨d, hd⟩ := Hex.GF2Poly.degree?_isSome_of_isZero_false hzf
    rw [hd]
    apply fpPoly_degree?_eq_some_of_coeff
    · rw [coeff_toFpPoly, Hex.GF2Poly.coeff_eq_true_of_degree?_eq_some hd]
      simpa using zmod2_one_ne_zero
    · intro n hn
      rw [coeff_toFpPoly, Hex.GF2Poly.coeff_eq_false_of_degree?_lt hd hn]
      rfl

/-- Packed `GF(2)` irreducibility transports to `FpPoly 2` irreducibility across
`toFpPoly`. Both predicates are the project-local executable `def`s, so the
transport runs through the conversion layer directly. -/
theorem irreducible_toFpPoly {p : Hex.GF2Poly} (h : Hex.GF2Poly.Irreducible p) :
    Hex.FpPoly.Irreducible (toFpPoly p) := by
  obtain ⟨hp_ne, hp_factor⟩ := h
  refine ⟨?_, ?_⟩
  · intro hzero
    exact hp_ne (toFpPoly_injective (by rw [hzero, toFpPoly_zero]))
  · intro a b hab
    have hmul : ofFpPoly a * ofFpPoly b = p := by
      apply toFpPoly_injective
      rw [toFpPoly_mul, toFpPoly_ofFpPoly, toFpPoly_ofFpPoly, hab]
    have ha_ne : ofFpPoly a ≠ 0 := fun h0 => hp_ne (by
      rw [← hmul, h0, Hex.GF2Poly.zero_mul])
    have hb_ne : ofFpPoly b ≠ 0 := fun h0 => hp_ne (by
      rw [← hmul, h0, Hex.GF2Poly.mul_zero])
    have hupgrade : ∀ q : Hex.FpPoly 2, ofFpPoly q ≠ 0 →
        (ofFpPoly q).degree = 0 → q.degree? = some 0 := by
      intro q hq hdeg
      have hzf : (ofFpPoly q).isZero = false := by
        cases hb : (ofFpPoly q).isZero with
        | false => rfl
        | true => exact absurd (Hex.GF2Poly.eq_zero_of_isZero hb) hq
      obtain ⟨d, hd⟩ := Hex.GF2Poly.degree?_isSome_of_isZero_false hzf
      have hdd : (ofFpPoly q).degree = d := Hex.GF2Poly.degree_eq_of_degree?_eq_some hd
      rw [hdd] at hdeg
      subst hdeg
      calc q.degree? = (toFpPoly (ofFpPoly q)).degree? := by rw [toFpPoly_ofFpPoly]
        _ = (ofFpPoly q).degree? := degree?_toFpPoly _
        _ = some 0 := hd
    rcases hp_factor (ofFpPoly a) (ofFpPoly b) hmul with hda | hdb
    · exact Or.inl (hupgrade a ha_ne hda)
    · exact Or.inr (hupgrade b hb_ne hdb)

/-- Interpret a packed polynomial as the natural number with the same binary
coefficient bits. This gives correspondence modules a finite index for
bounded-degree representatives without changing the executable `HexGF2`
representation. -/
private def wordsToNatAux : List UInt64 → Nat → Nat
  | [], _ => 0
  | w :: ws, i => w.toNat * 2 ^ (64 * i) + wordsToNatAux ws (i + 1)

def toNat (p : Hex.GF2Poly) : Nat :=
  wordsToNatAux p.toWords.toList 0

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
