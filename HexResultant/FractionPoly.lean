/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Fraction
public import HexResultant.PseudoDivMod

public section

/-!
Coefficient embedding from dense polynomials over an exact-division domain to
dense polynomials over its fraction field.

This module is retained as proof infrastructure: `SubresultantMinor` maps
generalized Sylvester minors through `Fraction.map` for its image
certificates, and the manual embeds the pseudo-division transport and
scalar-quotient pullback theorems.
-/

namespace Hex

namespace Fraction.NonzeroOne

universe u

/-- A nonzero dense polynomial supplies a nonzero coefficient and hence a
nontrivial coefficient ring. -/
theorem of_poly_ne_zero {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) (hp : p ≠ 0) : Hex.Fraction.NonzeroOne R := by
  have hpos : 0 < p.size := Nat.pos_of_ne_zero fun hzero =>
    hp ((DensePoly.size_eq_zero_iff p).mp hzero)
  exact of_ne_zero (DensePoly.leadingCoeff_ne_zero_of_pos_size p hpos)

end Fraction.NonzeroOne

namespace DensePoly
namespace Fraction

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
  [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]

/-- Embed every coefficient of a dense polynomial into the fraction field. -/
@[expose]
noncomputable def map (p : DensePoly R) : DensePoly (Hex.Fraction R) :=
  ofList (p.toList.map Hex.Fraction.ofCoeff)

omit [DecidableEq R] in
private theorem list_getD_map (xs : List R) (n : Nat) :
    (xs.map Hex.Fraction.ofCoeff).getD n (Hex.Fraction.ofCoeff (0 : R)) =
      Hex.Fraction.ofCoeff (xs.getD n (0 : R)) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n => exact ih n

/-- Coefficients commute with the fraction-field embedding. -/
@[simp]
theorem coeff_map (p : DensePoly R) (n : Nat) :
    (map p).coeff n = Hex.Fraction.ofCoeff (p.coeff n) := by
  rw [map, coeff_ofList]
  change (p.toList.map Hex.Fraction.ofCoeff).getD n
      (Hex.Fraction.ofCoeff (0 : R)) = Hex.Fraction.ofCoeff (p.coeff n)
  rw [list_getD_map]
  exact congrArg Hex.Fraction.ofCoeff (toList_getD_eq_coeff p n)

/-- Fraction embedding preserves the normalized dense size. -/
@[simp]
theorem size_map (p : DensePoly R) : (map p).size = p.size := by
  have hle : (map p).size ≤ p.size := by
    exact Nat.le_trans (size_ofList_le _)
      (by simp [length_toList])
  by_cases hp : p.size = 0
  · omega
  have hpos : 0 < p.size := Nat.pos_of_ne_zero hp
  have hcoeff : (map p).coeff (p.size - 1) ≠ (0 : Hex.Fraction R) := by
    rw [coeff_map]
    intro hzero
    have hz := (Hex.Fraction.ofCoeff_eq_zero_iff _).mp hzero
    exact (coeff_last_ne_zero_of_pos_size p hpos) hz
  apply Nat.le_antisymm hle
  apply Nat.le_of_not_gt
  intro hlt
  exact hcoeff (coeff_eq_zero_of_size_le (map p) (by omega))

/-- Fraction embedding preserves the leading coefficient. -/
@[simp]
theorem leadingCoeff_map (p : DensePoly R) :
    (map p).leadingCoeff = Hex.Fraction.ofCoeff p.leadingCoeff := by
  by_cases hp : p.size = 0
  · have hp0 : p = 0 := (size_eq_zero_iff p).mp hp
    have hmap0 : map p = 0 := (size_eq_zero_iff (map p)).mp (by
      rw [size_map, hp])
    rw [hmap0, hp0,
      show (0 : DensePoly (Hex.Fraction R)).leadingCoeff = 0 from
        leadingCoeff_zero,
      show (0 : DensePoly R).leadingCoeff = 0 from leadingCoeff_zero]
    exact Hex.Fraction.ofCoeff_zero.symm
  · have hpos : 0 < p.size := Nat.pos_of_ne_zero hp
    rw [leadingCoeff_eq_coeff_last (map p) (by simpa using hpos), size_map,
      coeff_map, leadingCoeff_eq_coeff_last p hpos]

/-- Fraction embedding reflects polynomial zero. -/
theorem map_eq_zero_iff (p : DensePoly R) : map p = 0 ↔ p = 0 := by
  rw [← size_eq_zero_iff, size_map, size_eq_zero_iff]

/-- Fraction embedding is injective. -/
theorem map_injective {p q : DensePoly R} (h : map p = map q) : p = q := by
  apply ext_coeff
  intro n
  apply Hex.Fraction.ofCoeff_injective
  simpa only [coeff_map] using congrArg (fun x => x.coeff n) h

/-- Fraction embedding preserves zero. -/
@[simp]
theorem map_zero : map (0 : DensePoly R) = 0 := by
  exact (map_eq_zero_iff 0).mpr rfl

/-- Fraction embedding preserves constants. -/
@[simp]
theorem map_C (a : R) : map (C a) = C (Hex.Fraction.ofCoeff a) := by
  apply ext_coeff
  intro n
  rw [coeff_map, coeff_C, coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    exact Hex.Fraction.ofCoeff_zero

/-- Fraction embedding preserves addition. -/
@[simp]
theorem map_add (p q : DensePoly R) : map (p + q) = map p + map q := by
  apply ext_coeff
  intro n
  simp only [coeff_map, coeff_add_semiring, Hex.Fraction.ofCoeff_add]

/-- Fraction embedding preserves negation. -/
@[simp]
theorem map_neg (p : DensePoly R) : map (-p) = -map p := by
  apply ext_coeff
  intro n
  simp only [coeff_map, coeff_neg_ring, Hex.Fraction.ofCoeff_neg]

/-- Fraction embedding preserves subtraction. -/
@[simp]
theorem map_sub (p q : DensePoly R) : map (p - q) = map p - map q := by
  apply ext_coeff
  intro n
  simp only [coeff_map, coeff_sub_ring, Hex.Fraction.ofCoeff_sub]

/-- Fraction embedding preserves scalar multiplication. -/
@[simp]
theorem map_scale (a : R) (p : DensePoly R) :
    map (scale a p) = scale (Hex.Fraction.ofCoeff a) (map p) := by
  apply ext_coeff
  intro n
  simp only [coeff_map, coeff_scale_semiring, Hex.Fraction.ofCoeff_mul]

private theorem step_map (p q : DensePoly R) (n i j : Nat) (acc : R) :
    Hex.Fraction.ofCoeff (mulCoeffStep p q n i acc j) =
      mulCoeffStep (map p) (map q) n i (Hex.Fraction.ofCoeff acc) j := by
  unfold mulCoeffStep
  by_cases h : i + j = n
  · simp only [h, ite_true, coeff_map, Hex.Fraction.ofCoeff_add,
      Hex.Fraction.ofCoeff_mul]
  · simp only [h, ite_false]

private theorem inner_map (p q : DensePoly R) (n i : Nat) (xs : List Nat)
    (acc : R) :
    Hex.Fraction.ofCoeff (xs.foldl (mulCoeffStep p q n i) acc) =
      xs.foldl (mulCoeffStep (map p) (map q) n i)
        (Hex.Fraction.ofCoeff acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, ← step_map]

private theorem outer_map (p q : DensePoly R) (n : Nat) (xs : List Nat)
    (acc : R) :
    Hex.Fraction.ofCoeff
        (xs.foldl
          (fun acc i => (List.range q.size).foldl (mulCoeffStep p q n i) acc)
          acc) =
      xs.foldl
        (fun acc i =>
          (List.range (map q).size).foldl
            (mulCoeffStep (map p) (map q) n i) acc)
        (Hex.Fraction.ofCoeff acc) := by
  rw [size_map]
  induction xs generalizing acc with
  | nil => rfl
  | cons i is ih =>
      simp only [List.foldl_cons]
      rw [ih, ← inner_map]

private theorem sum_map (p q : DensePoly R) (n : Nat) :
    Hex.Fraction.ofCoeff (mulCoeffSum p q n) =
      mulCoeffSum (map p) (map q) n := by
  unfold mulCoeffSum
  simpa only [size_map, Hex.Fraction.ofCoeff_zero] using
    outer_map p q n (List.range p.size) (Zero.zero : R)

/-- Fraction embedding preserves polynomial multiplication. -/
@[simp]
theorem map_mul (p q : DensePoly R) : map (p * q) = map p * map q := by
  apply ext_coeff
  intro n
  rw [coeff_map, coeff_mul, coeff_mul, sum_map]

/-- Pseudo-division commutes with the fraction-field embedding on an ordered
nonzero input pair. -/
theorem map_pseudoDivMod (f g : DensePoly R) (hg : g ≠ 0)
    (hgf : g.size ≤ f.size) :
    pseudoDivMod (map f) (map g) =
      (map (pseudoDivMod f g).1, map (pseudoDivMod f g).2) := by
  have hgmap : map g ≠ 0 := by
    intro hzero
    exact hg ((map_eq_zero_iff g).mp hzero)
  have hrec := pseudoDivMod_reconstruct f g hg hgf
  have hrecMap := congrArg map hrec
  have hcandidate :
      scale ((map g).leadingCoeff ^ ((map f).size - (map g).size + 1))
          (map f) =
        map (pseudoDivMod f g).1 * map g + map (pseudoDivMod f g).2 := by
    simpa only [size_map, leadingCoeff_map, map_scale, map_mul, map_add,
      Hex.Fraction.ofCoeff_pow] using hrecMap
  apply pseudoDivMod_unique (map f) (map g) (map (pseudoDivMod f g).1)
    (map (pseudoDivMod f g).2) hgmap (by simpa only [size_map] using hgf)
    hcandidate
  simpa only [size_map] using pseudoDivMod_remainder_lt f g hg

/-- Pull coefficientwise exact scalar division back from the fraction field.

The image hypothesis is the integrality certificate later supplied by a
generalized subresultant minor. -/
theorem divScalar_pullback (p q : DensePoly R) {b : R} (hb : b ≠ 0)
    (h : map q = divScalar (map p) (Hex.Fraction.ofCoeff b)) :
    divScalar p b = q := by
  have hbmap : Hex.Fraction.ofCoeff b ≠ (0 : Hex.Fraction R) := by
    intro hzero
    exact hb ((Hex.Fraction.ofCoeff_eq_zero_iff b).mp hzero)
  apply ext_coeff
  intro n
  rw [coeff_divScalar p hb]
  apply Hex.Fraction.div_pullback hb
  have hcoeff := congrArg (fun r : DensePoly (Hex.Fraction R) => r.coeff n) h
  simpa only [coeff_map, coeff_divScalar _ hbmap] using hcoeff

/-- Coefficientwise integrality in the fraction field proves that executable
scalar division reconstructs the original polynomial. -/
theorem divScalar_exact (p : DensePoly R) {b : R} (hb : b ≠ 0)
    (h : ∀ n, ∃ c : R,
      Hex.Fraction.ofCoeff c =
        Hex.Fraction.ofCoeff (p.coeff n) / Hex.Fraction.ofCoeff b) :
    p = scale b (divScalar p b) := by
  apply ext_coeff
  intro n
  rw [coeff_scale_semiring, coeff_divScalar p hb]
  have hexact := Hex.Fraction.div_exact hb (h n)
  simpa only [Lean.Grind.CommRing.mul_comm] using hexact.symm

/-! Compile-time check for the concrete polynomial instance graph. -/

private instance : Hex.Fraction.NonzeroOne Int := ⟨by decide⟩

example : Lean.Grind.CommRing (DensePoly (Hex.Fraction Int)) := inferInstance

end Fraction
end DensePoly
end Hex
