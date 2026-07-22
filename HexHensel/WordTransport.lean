/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.WordStep

public section

/-!
The polynomial reduction map `toWP : ZPoly → DensePoly (WordMod ctx)` (reduce every
coefficient into the residue ring) and its readback `ofWP`, together with the ring
homomorphism laws modulo the working modulus `M := m.toNat`.

`toWP` commutes with `+`, `-`, `*`, `0`, `1`; it kills the canonical reduction
(`reduceModPow _ _ 2`); and `ofWP ∘ toWP` is that canonical reduction. These are
the transport laws that carry the executable bignum Hensel step, coefficient by
coefficient, into `WordMod` arithmetic.
-/

namespace Hex
namespace ZPoly

open Hex.DensePoly

variable {m : UInt64} (ctx : _root_.MontCtx m)

/-- Reduce an integer polynomial coefficientwise into `WordMod ctx`. -/
def toWP (x : ZPoly) : DensePoly (WordMod ctx) :=
  DensePoly.ofCoeffs (x.toArray.map (fun c => WordMod.ofNat (ZPoly.intModNat c m.toNat)))

/-- Read the canonical `[0, M)` residues of a `WordMod` polynomial back into `ZPoly`. -/
def ofWP (p : DensePoly (WordMod ctx)) : ZPoly :=
  DensePoly.ofCoeffs (p.toArray.map (fun w => (Int.ofNat w.toNat : Int)))

@[simp] theorem coeff_toWP (x : ZPoly) (j : Nat) :
    (toWP ctx x).coeff j = WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat) := by
  have h0 : WordMod.ofNat (ctx := ctx) (ZPoly.intModNat 0 m.toNat) = 0 := by
    have : ZPoly.intModNat 0 m.toNat = 0 := by simp [ZPoly.intModNat]
    rw [this]; rfl
  rw [toWP, DensePoly.coeff_ofCoeffs]
  show (x.toArray.map (fun c => WordMod.ofNat (ctx := ctx) (ZPoly.intModNat c m.toNat))).getD j 0
    = WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat)
  rw [show x.coeff j = x.toArray.getD j 0 from rfl]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases x.toArray[j]? with
  | none => simpa using h0.symm
  | some v => simp

@[simp] theorem coeff_ofWP (p : DensePoly (WordMod ctx)) (j : Nat) :
    (ofWP ctx p).coeff j = Int.ofNat (p.coeff j).toNat := by
  rw [ofWP, DensePoly.coeff_ofCoeffs]
  show (p.toArray.map (fun w => (Int.ofNat w.toNat : Int))).getD j 0 = Int.ofNat (p.coeff j).toNat
  rw [show p.coeff j = p.toArray.getD j 0 from rfl]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases p.toArray[j]? with
  | none => simp [WordMod.toNat_zero]
  | some w => simp

/-- `toWP` is well-defined on congruence classes modulo `M`. -/
theorem toWP_congr {x y : ZPoly} (h : ZPoly.congr x y m.toNat) : toWP ctx x = toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  rw [coeff_toWP, coeff_toWP]
  apply WordMod.toNat_injective
  rw [WordMod.toNat_ofNat, WordMod.toNat_ofNat]
  have hc : (x.coeff j - y.coeff j) % (m.toNat : Int) = 0 := h j
  have hxy : x.coeff j % (m.toNat : Int) = y.coeff j % (m.toNat : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hc
  have : ZPoly.intModNat (x.coeff j) m.toNat = ZPoly.intModNat (y.coeff j) m.toNat := by
    simp [ZPoly.intModNat, hxy]
  rw [this]

@[simp] theorem toWP_zero : toWP ctx 0 = 0 := by
  apply DensePoly.ext_coeff
  intro j
  rw [coeff_toWP]
  have : ZPoly.intModNat ((0 : ZPoly).coeff j) m.toNat = 0 := by
    rw [DensePoly.coeff_zero]; simp [ZPoly.intModNat]
  rw [this, DensePoly.coeff_zero]; rfl

theorem toWP_add (x y : ZPoly) : toWP ctx (x + y) = toWP ctx x + toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  have hz : (0 : WordMod ctx) + 0 = 0 := by rw [WordMod.eq_iff_toNat]; simp
  rw [DensePoly.coeff_add _ _ j hz, coeff_toWP, coeff_toWP, coeff_toWP]
  apply WordMod.toNat_injective
  rw [WordMod.toNat_add, WordMod.toNat_ofNat, WordMod.toNat_ofNat, WordMod.toNat_ofNat,
    DensePoly.coeff_add x y j (by rfl), ZPoly.intModNat_add _ _ ctx.p_pos,
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (x.coeff j) ctx.p_pos),
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (y.coeff j) ctx.p_pos), Nat.mod_mod]

theorem toWP_sub (x y : ZPoly) : toWP ctx (x - y) = toWP ctx x - toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  have hz : (0 : WordMod ctx) - 0 = 0 := by rw [WordMod.eq_iff_toNat]; simp
  rw [DensePoly.coeff_sub _ _ j hz, coeff_toWP, coeff_toWP, coeff_toWP]
  apply WordMod.toNat_injective
  rw [WordMod.toNat_sub, WordMod.toNat_ofNat, WordMod.toNat_ofNat, WordMod.toNat_ofNat,
    DensePoly.coeff_sub x y j (by rfl), ZPoly.intModNat_sub _ _ ctx.p_pos,
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (x.coeff j) ctx.p_pos),
    Nat.mod_eq_of_lt (ZPoly.intModNat_lt' (y.coeff j) ctx.p_pos), Nat.mod_mod]

theorem intModNat_one {M : Nat} (hM : 0 < M) : ZPoly.intModNat 1 M = 1 % M := by
  have h : ((ZPoly.intModNat 1 M : Nat) : Int) = ((1 % M : Nat) : Int) := by
    rw [ZPoly.intModNat_cast 1 hM]; exact_mod_cast rfl
  exact_mod_cast h

@[simp] theorem toWP_one : toWP ctx 1 = 1 := by
  apply DensePoly.ext_coeff
  intro j
  rw [coeff_toWP, WordMod.eq_iff_toNat, WordMod.toNat_ofNat,
    show (1 : ZPoly) = DensePoly.C 1 from rfl,
    show (1 : DensePoly (WordMod ctx)) = DensePoly.C 1 from rfl,
    DensePoly.coeff_C, DensePoly.coeff_C]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [if_pos rfl, if_pos rfl, WordMod.toNat_one, intModNat_one ctx.p_pos, Nat.mod_mod]
  · rw [if_neg (Nat.ne_of_gt hj), if_neg (Nat.ne_of_gt hj),
      show (Zero.zero : WordMod ctx) = 0 from rfl, WordMod.toNat_zero,
      show (Zero.zero : Int) = 0 from rfl, ZPoly.intModNat]
    simp

/-- The canonical reduction `reduceModPow _ p k` vanishes under `toWP` when the
working modulus is exactly `p^k`. -/
theorem toWP_reduceModPow {p k : Nat} (hM : m.toNat = p ^ k) (hpk : 0 < p ^ k) (x : ZPoly) :
    toWP ctx (ZPoly.reduceModPow x p k) = toWP ctx x := by
  apply toWP_congr
  have := ZPoly.congr_reduceModPow x p k hpk
  rwa [← hM] at this

theorem size_toWP_le (x : ZPoly) : (toWP ctx x).size ≤ x.size := by
  rw [toWP]
  calc (DensePoly.ofCoeffs _).size ≤ (x.toArray.map _).size := DensePoly.size_ofCoeffs_le _
    _ = x.size := by rw [Array.size_map, DensePoly.toArray_size]

end ZPoly

/-! ### Common-range normalisation of `mulCoeffSum` -/

namespace DensePoly

variable {R : Type _} [Lean.Grind.CommRing R] [DecidableEq R]

/-- An inner schoolbook step past the divisor's support is the identity. -/
theorem mulCoeffStep_ge (p q : DensePoly R) (n i : Nat) (acc : R) (j : Nat) (hj : q.size ≤ j) :
    mulCoeffStep p q n i acc j = acc := by
  unfold mulCoeffStep
  by_cases h : i + j = n
  · rw [if_pos h, coeff_eq_zero_of_size_le q hj, show (Zero.zero : R) = 0 from rfl,
      Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
  · rw [if_neg h]

/-- Extending the inner fold past `q.size` changes nothing. -/
theorem mulCoeffStep_inner_extend (p q : DensePoly R) (n i : Nat) (acc : R) (t : Nat)
    (ht : q.size ≤ t) :
    (List.range t).foldl (mulCoeffStep p q n i) acc
      = (List.range q.size).foldl (mulCoeffStep p q n i) acc := by
  obtain ⟨d, rfl⟩ : ∃ d, t = q.size + d := ⟨t - q.size, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [mulCoeffStep_ge p q n i _ (q.size + d) (by omega), ih (by omega)]

/-- Past `p.size`, the whole inner fold is the identity. -/
theorem mulCoeffStep_inner_all_zero (p q : DensePoly R) (n i : Nat) (acc : R) (hi : p.size ≤ i)
    (L : List Nat) : L.foldl (mulCoeffStep p q n i) acc = acc := by
  induction L generalizing acc with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldl_cons]
      rw [show mulCoeffStep p q n i acc j = acc from by
        unfold mulCoeffStep
        by_cases h : i + j = n
        · rw [if_pos h, coeff_eq_zero_of_size_le p hi, show (Zero.zero : R) = 0 from rfl,
            Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.add_zero]
        · rw [if_neg h], ih]

/-- Extending the outer fold past `p.size` changes nothing. -/
theorem mulCoeffStep_outer_extend (p q : DensePoly R) (n : Nat) (acc : R) (s : Nat)
    (hs : p.size ≤ s) :
    (List.range s).foldl (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc) acc
      = (List.range p.size).foldl (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc) acc := by
  obtain ⟨d, rfl⟩ : ∃ d, s = p.size + d := ⟨s - p.size, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [mulCoeffStep_inner_all_zero p q n (p.size + d) _ (by omega), ih (by omega)]

/-- `mulCoeffSum` computed over any large enough common range `s × t`. -/
theorem mulCoeffSum_norm (p q : DensePoly R) (n s t : Nat) (hs : p.size ≤ s) (ht : q.size ≤ t) :
    mulCoeffSum p q n
      = (List.range s).foldl (fun acc i => (List.range t).foldl (mulCoeffStep p q n i) acc) 0 := by
  have hfun : (fun (acc : R) (i : Nat) => (List.range t).foldl (mulCoeffStep p q n i) acc)
            = (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc) := by
    funext acc i; exact mulCoeffStep_inner_extend p q n i acc t ht
  rw [hfun, show mulCoeffSum p q n
      = (List.range p.size).foldl (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc) 0
      from rfl]
  exact (mulCoeffStep_outer_extend p q n 0 s hs).symm

end DensePoly

/-! ### Multiplicative transport -/

namespace ZPoly

open Hex.DensePoly

variable {m : UInt64} (ctx : _root_.MontCtx m)

/-- `M ∣ (a - a % M)`. -/
private theorem selfdvd (M : Nat) (a : Int) : (M : Int) ∣ (a - a % (M : Int)) := by
  apply Int.dvd_of_emod_eq_zero
  rw [Int.sub_emod, Int.emod_emod_of_dvd a ⟨1, (Int.mul_one _).symm⟩, Int.sub_self, Int.zero_emod]

/-- Residue-agreement modulo `M` between a `WordMod` value and an `Int`. -/
private def Res (w : WordMod ctx) (z : Int) : Prop :=
  (Int.ofNat w.toNat - z) % (m.toNat : Int) = 0

private theorem Res_zero : Res ctx 0 0 := by
  show (Int.ofNat (0 : WordMod ctx).toNat - 0) % (m.toNat : Int) = 0
  rw [WordMod.toNat_zero]; simp

private theorem Res_add {w w' : WordMod ctx} {z z' : Int}
    (h : Res ctx w z) (h' : Res ctx w' z') : Res ctx (w + w') (z + z') := by
  show (Int.ofNat (w + w').toNat - (z + z')) % (m.toNat : Int) = 0
  rw [show Int.ofNat (w + w').toNat = (Int.ofNat w.toNat + Int.ofNat w'.toNat) % (m.toNat : Int)
      from by rw [WordMod.toNat_add]; exact_mod_cast rfl]
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero h with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero h' with ⟨d, hd⟩
  rcases selfdvd m.toNat (Int.ofNat w.toNat + Int.ofNat w'.toNat) with ⟨e, he⟩
  exact ⟨c + d - e, by grind⟩

private theorem Res_mul {w w' : WordMod ctx} {z z' : Int}
    (h : Res ctx w z) (h' : Res ctx w' z') : Res ctx (w * w') (z * z') := by
  show (Int.ofNat (w * w').toNat - z * z') % (m.toNat : Int) = 0
  rw [show Int.ofNat (w * w').toNat = (Int.ofNat w.toNat * Int.ofNat w'.toNat) % (m.toNat : Int)
      from by rw [WordMod.toNat_mul]; exact_mod_cast rfl]
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero h with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero h' with ⟨d, hd⟩
  rcases selfdvd m.toNat (Int.ofNat w.toNat * Int.ofNat w'.toNat) with ⟨e, he⟩
  exact ⟨Int.ofNat w.toNat * d + z' * c - e, by grind⟩

private theorem Res_coeff_toWP (x : ZPoly) (i : Nat) :
    Res ctx ((toWP ctx x).coeff i) (x.coeff i) := by
  show (Int.ofNat ((toWP ctx x).coeff i).toNat - x.coeff i) % (m.toNat : Int) = 0
  rw [coeff_toWP, WordMod.toNat_ofNat, Nat.mod_eq_of_lt (ZPoly.intModNat_lt' _ ctx.p_pos),
    Int.ofNat_eq_natCast, ZPoly.intModNat_cast _ ctx.p_pos]
  rw [Int.sub_emod, Int.emod_emod_of_dvd _ ⟨1, (Int.mul_one _).symm⟩, Int.sub_self, Int.zero_emod]

private theorem toNat_eq_intModNat_of_Res {w : WordMod ctx} {z : Int} (h : Res ctx w z) :
    w.toNat = ZPoly.intModNat z m.toNat := by
  have hlt : (w.toNat : Int) < m.toNat := by exact_mod_cast WordMod.toNat_lt w
  have hnn : (0 : Int) ≤ w.toNat := Int.natCast_nonneg _
  have hmod : (w.toNat : Int) % m.toNat = z % m.toNat := by
    have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr h
    rwa [Int.ofNat_eq_natCast] at this
  have hz : (w.toNat : Int) = z % (m.toNat : Int) := by rw [← hmod, Int.emod_eq_of_lt hnn hlt]
  rw [ZPoly.intModNat, Int.ofNat_eq_natCast, ← hz]; simp

private theorem Res_inner_fold (x y : ZPoly) (n i : Nat) (L : List Nat) :
    ∀ (w : WordMod ctx) (z : Int), Res ctx w z →
      Res ctx (L.foldl (mulCoeffStep (toWP ctx x) (toWP ctx y) n i) w)
        (L.foldl (mulCoeffStep x y n i) z) := by
  induction L with
  | nil => intro w z h; simpa using h
  | cons a L ih =>
      intro w z h
      simp only [List.foldl_cons]
      apply ih
      unfold mulCoeffStep
      by_cases hc : i + a = n
      · rw [if_pos hc, if_pos hc]
        exact Res_add ctx h (Res_mul ctx (Res_coeff_toWP ctx x i) (Res_coeff_toWP ctx y a))
      · rw [if_neg hc, if_neg hc]; exact h

private theorem Res_outer_fold (x y : ZPoly) (n t : Nat) (L : List Nat) :
    ∀ (w : WordMod ctx) (z : Int), Res ctx w z →
      Res ctx
        (L.foldl (fun acc i =>
          (List.range t).foldl (mulCoeffStep (toWP ctx x) (toWP ctx y) n i) acc) w)
        (L.foldl (fun acc i => (List.range t).foldl (mulCoeffStep x y n i) acc) z) := by
  induction L with
  | nil => intro w z h; simpa using h
  | cons a L ih =>
      intro w z h
      simp only [List.foldl_cons]
      exact ih _ _ (Res_inner_fold ctx x y n a (List.range t) w z h)

private theorem Res_mulCoeffSum (x y : ZPoly) (j : Nat) :
    Res ctx (mulCoeffSum (toWP ctx x) (toWP ctx y) j) (mulCoeffSum x y j) := by
  rw [DensePoly.mulCoeffSum_norm (toWP ctx x) (toWP ctx y) j x.size y.size
        (size_toWP_le ctx x) (size_toWP_le ctx y),
      DensePoly.mulCoeffSum_norm x y j x.size y.size (Nat.le_refl _) (Nat.le_refl _)]
  exact Res_outer_fold ctx x y j y.size (List.range x.size) 0 0 (Res_zero ctx)

theorem toWP_mul (x y : ZPoly) : toWP ctx (x * y) = toWP ctx x * toWP ctx y := by
  apply DensePoly.ext_coeff
  intro j
  apply WordMod.toNat_injective
  rw [coeff_toWP, WordMod.toNat_ofNat, Nat.mod_eq_of_lt (ZPoly.intModNat_lt' _ ctx.p_pos),
    DensePoly.coeff_mul, DensePoly.coeff_mul]
  exact (toNat_eq_intModNat_of_Res ctx (Res_mulCoeffSum ctx x y j)).symm

end ZPoly
end Hex
