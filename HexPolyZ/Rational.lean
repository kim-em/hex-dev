/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public import HexPolyZ.Core
import all HexPolyZ.Core

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Rational-coefficient machinery for the primitive-square-free pipeline:
`normalizePrimitiveSign` / `ratPolyPrimitivePart` properties, the `rat_*`
DensePoly arithmetic, and the `ratDivModLaws` / `ratGcdLaws` instances.
-/
namespace Hex

namespace ZPoly
/-- The primitive field of `primitiveSquareFreeDecomposition f` is the primitive
part of `f`. -/
theorem primitiveSquareFreeDecomposition_primitive (f : ZPoly) :
    (primitiveSquareFreeDecomposition f).primitive = primitivePart f := by
  by_cases hzero : (primitivePart f).isZero = true
  · simp [primitiveSquareFreeDecomposition, hzero]
  · by_cases hderivative : (DensePoly.derivative (toRatPoly (primitivePart f))).isZero = true
    · simp [primitiveSquareFreeDecomposition, hzero, hderivative]
    · simp [primitiveSquareFreeDecomposition, hzero, hderivative]

/-- Sign-normalization fixes the zero polynomial: `normalizePrimitiveSign 0 = 0`,
the base case characterising the transform on a degenerate input. -/
private theorem normalizePrimitiveSign_zero :
    normalizePrimitiveSign (0 : ZPoly) = 0 := by
  unfold normalizePrimitiveSign
  split
  · exact DensePoly.scale_neg_one_zero
  · rfl

/-- Normalizing the primitive sign makes the leading coefficient nonnegative. -/
theorem leadingCoeff_normalizePrimitiveSign_nonneg (p : ZPoly) :
    0 ≤ DensePoly.leadingCoeff (normalizePrimitiveSign p) := by
  unfold normalizePrimitiveSign
  by_cases hlead : DensePoly.leadingCoeff p < 0
  · rw [if_pos hlead]
    rw [leadingCoeff_scale_of_nonzero (-1 : Int) p (by decide)]
    omega
  · rw [if_neg hlead]
    omega

/-- A nonzero integer polynomial has nonzero leading coefficient. -/
theorem leadingCoeff_ne_zero_of_ne_zero (p : ZPoly) (hp : p ≠ 0) :
    DensePoly.leadingCoeff p ≠ 0 := by
  have hp_pos : 0 < p.size := size_pos_of_ne_zero p hp
  rw [DensePoly.leadingCoeff_eq_coeff_last p hp_pos]
  exact DensePoly.coeff_last_ne_zero_of_pos_size p hp_pos

/-- Sign-normalization preserves nonzeroness: scaling by `-1` cannot collapse a
nonzero polynomial, so `normalizePrimitiveSign p ≠ 0` whenever `p ≠ 0`. -/
private theorem normalizePrimitiveSign_ne_zero_of_ne_zero (p : ZPoly) (hp : p ≠ 0) :
    normalizePrimitiveSign p ≠ 0 := by
  unfold normalizePrimitiveSign
  by_cases hlead : DensePoly.leadingCoeff p < 0
  · rw [if_pos hlead]
    intro hzero
    have hsize : p.size = 0 := by
      have hscaled_size : (DensePoly.scale (-1 : Int) p).size = p.size :=
        scale_size_of_nonzero (-1 : Int) p (by decide)
      rw [hzero, DensePoly.size_zero] at hscaled_size
      omega
    apply hp
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le p (by omega)
  · rw [if_neg hlead]
    exact hp

/-- Normalizing the primitive sign of a nonzero polynomial makes the leading
coefficient positive. -/
theorem leadingCoeff_normalizePrimitiveSign_pos_of_ne_zero (p : ZPoly)
    (hp : p ≠ 0) :
    0 < DensePoly.leadingCoeff (normalizePrimitiveSign p) := by
  have hnonneg := leadingCoeff_normalizePrimitiveSign_nonneg p
  have hne : DensePoly.leadingCoeff (normalizePrimitiveSign p) ≠ 0 :=
    leadingCoeff_ne_zero_of_ne_zero (normalizePrimitiveSign p)
      (normalizePrimitiveSign_ne_zero_of_ne_zero p hp)
  omega

/-- Sign-normalization is the identity on a polynomial whose leading coefficient
is already nonnegative, since the negating branch is not taken. -/
private theorem normalizePrimitiveSign_eq_self_of_leadingCoeff_nonneg
    (p : ZPoly) (h : 0 ≤ DensePoly.leadingCoeff p) :
    normalizePrimitiveSign p = p := by
  unfold normalizePrimitiveSign
  rw [if_neg (by omega)]

/-- The rational primitive part has nonnegative integer leading coefficient. -/
theorem leadingCoeff_ratPolyPrimitivePart_nonneg (p : DensePoly Rat) :
    0 ≤ DensePoly.leadingCoeff (ratPolyPrimitivePart p) := by
  unfold ratPolyPrimitivePart
  exact leadingCoeff_normalizePrimitiveSign_nonneg _

/-- The rational primitive part of a nonzero rational polynomial has positive
integer leading coefficient. -/
theorem leadingCoeff_ratPolyPrimitivePart_pos_of_ne_zero (p : DensePoly Rat)
    (hp : p ≠ 0) :
    0 < DensePoly.leadingCoeff (ratPolyPrimitivePart p) := by
  unfold ratPolyPrimitivePart
  apply leadingCoeff_normalizePrimitiveSign_pos_of_ne_zero
  intro hpart_zero
  have hcleared_zero : ratPolyPrimitivePartCleared p = 0 := by
    change DensePoly.primitivePart (ratPolyPrimitivePartCleared p) = 0 at hpart_zero
    rw [← DensePoly.content_mul_primitivePart (ratPolyPrimitivePartCleared p)]
    change DensePoly.scale (DensePoly.content (ratPolyPrimitivePartCleared p))
        (DensePoly.primitivePart (ratPolyPrimitivePartCleared p)) = 0
    rw [hpart_zero]
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale (R := Int) (DensePoly.content (ratPolyPrimitivePartCleared p))
      (0 : ZPoly) n (Int.mul_zero _)]
    rw [DensePoly.coeff_zero]
    exact Int.mul_zero _
  have hrat_zero : toRatPoly (ratPolyPrimitivePartCleared p) = 0 := by
    rw [hcleared_zero, toRatPoly_zero]
  have hscaled_zero :
      DensePoly.scale (ratCommonDen p.toArray.toList : Rat) p = 0 := by
    simpa [toRatPoly_ratPolyPrimitivePartCleared] using hrat_zero
  have hden_ne : (ratCommonDen p.toArray.toList : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (ratCommonDen_pos p.toArray.toList)
  apply hp
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun q : DensePoly Rat => q.coeff n) hscaled_zero
  change (DensePoly.scale (ratCommonDen p.toArray.toList : Rat) p).coeff n =
    (0 : DensePoly Rat).coeff n at hcoeff
  rw [DensePoly.coeff_scale (R := Rat) (ratCommonDen p.toArray.toList : Rat) p n
    (Rat.mul_zero _)] at hcoeff
  rw [DensePoly.coeff_zero] at hcoeff ⊢
  rcases Rat.mul_eq_zero.mp hcoeff with hden_zero | hp_zero
  · exact False.elim (hden_ne hden_zero)
  · exact hp_zero

/-- Sign-normalization preserves primitivity: negating by `-1` leaves the content
unchanged, so the sign-normalized primitive part of `f` is still primitive whenever
its content is nonzero. -/
private theorem normalizePrimitiveSign_primitivePart_primitive (f : ZPoly)
    (h : content (normalizePrimitiveSign (primitivePart f)) ≠ 0) :
    Primitive (normalizePrimitiveSign (primitivePart f)) := by
  have hcontent_ne : content f ≠ 0 := by
    intro hcontent
    have hpart_zero : primitivePart f = 0 := by
      simpa [primitivePart] using
        DensePoly.primitivePart_eq_zero_of_content_eq_zero f (by simpa [content] using hcontent)
    apply h
    rw [hpart_zero, normalizePrimitiveSign_zero]
    simp [content, DensePoly.content_zero]
  by_cases hlead : DensePoly.leadingCoeff (primitivePart f) < 0
  · rw [normalizePrimitiveSign, if_pos hlead, Primitive, content,
      DensePoly.content_scale_neg_one]
    simpa [Primitive, content] using primitivePart_primitive f hcontent_ne
  · rw [normalizePrimitiveSign, if_neg hlead]
    exact primitivePart_primitive f hcontent_ne

/-- The rational primitive part is primitive when its content is nonzero. -/
theorem ratPolyPrimitivePart_primitive (f : DensePoly Rat)
    (h : content (ratPolyPrimitivePart f) ≠ 0) :
    Primitive (ratPolyPrimitivePart f) := by
  unfold ratPolyPrimitivePart at h ⊢
  exact normalizePrimitiveSign_primitivePart_primitive _ h

/-- A rational polynomial is a rational scalar multiple of the rationalization
of its integer primitive part. -/
theorem ratPolyPrimitivePart_rational_associate (f : DensePoly Rat) :
    ∃ unit : Rat, f = DensePoly.scale unit (toRatPoly (ratPolyPrimitivePart f)) := by
  exact ratPolyPrimitivePart_rational_associate_core f

/--
Gauss-style cancellation: if two primitive nonzero integer polynomials are
rational associates with rational factor `unit`, then `unit` is `±1`.
-/
theorem rational_associate_primitive_unit
    {p q : ZPoly} (hp : Primitive p) (_hp_ne : p ≠ 0)
    (hq : Primitive q) (_hq_ne : q ≠ 0)
    {unit : Rat}
    (hunit : toRatPoly p = DensePoly.scale unit (toRatPoly q)) :
    unit = 1 ∨ unit = -1 := by
  -- Step 1: `unit.den * unit = unit.num` (as Rat).
  have hden_rat_ne : ((unit.den : Nat) : Rat) ≠ 0 := by
    exact_mod_cast unit.den_nz
  have hunit_den_mul :
      ((unit.den : Nat) : Rat) * unit = ((unit.num : Int) : Rat) := by
    have h0 := unit.num_divInt_den
    rw [Rat.divInt_eq_div] at h0
    have h : ((unit.num : Int) : Rat) / ((unit.den : Nat) : Rat) = unit := by
      push_cast at h0 ⊢
      exact h0
    have hdiv := Rat.div_mul_cancel
      (a := ((unit.num : Int) : Rat)) (b := ((unit.den : Nat) : Rat)) hden_rat_ne
    rw [h] at hdiv
    rw [Rat.mul_comm]
    exact hdiv
  -- Step 2: clear denominators to obtain an integer-polynomial equation.
  have hscale_eq :
      DensePoly.scale ((unit.den : Nat) : Int) p =
        DensePoly.scale unit.num q := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale (R := Int) ((unit.den : Nat) : Int) p n
      (Int.mul_zero _)]
    rw [DensePoly.coeff_scale (R := Int) unit.num q n (Int.mul_zero _)]
    have hcoeff_n :=
      congrArg (fun r : DensePoly Rat => r.coeff n) hunit
    change (toRatPoly p).coeff n =
      (DensePoly.scale unit (toRatPoly q)).coeff n at hcoeff_n
    rw [coeff_toRatPoly] at hcoeff_n
    rw [DensePoly.coeff_scale (R := Rat) unit (toRatPoly q) n
      (Rat.mul_zero unit)] at hcoeff_n
    rw [coeff_toRatPoly] at hcoeff_n
    have hmul_eq :
        ((unit.den : Nat) : Rat) * ((p.coeff n : Int) : Rat) =
          ((unit.den : Nat) : Rat) * (unit * ((q.coeff n : Int) : Rat)) := by
      rw [hcoeff_n]
    rw [← Rat.mul_assoc, hunit_den_mul] at hmul_eq
    -- Lift back to Int.
    have hcast :
        ((((unit.den : Nat) : Int) * p.coeff n : Int) : Rat) =
          ((unit.num * q.coeff n : Int) : Rat) := by
      push_cast
      exact hmul_eq
    exact_mod_cast hcast
  -- Step 3: equate contents.
  have hcontent_eq :
      DensePoly.content (DensePoly.scale ((unit.den : Nat) : Int) p) =
        DensePoly.content (DensePoly.scale unit.num q) := by
    rw [hscale_eq]
  rw [DensePoly.content_scale_int, DensePoly.content_scale_int] at hcontent_eq
  have hcontent_p : DensePoly.content p = 1 := hp
  have hcontent_q : DensePoly.content q = 1 := hq
  rw [hcontent_p, hcontent_q, Int.mul_one, Int.mul_one] at hcontent_eq
  rw [Int.natAbs_natCast] at hcontent_eq
  have hden_eq_natAbs : unit.den = unit.num.natAbs := by
    have h : ((unit.den : Nat) : Int) = ((unit.num.natAbs : Nat) : Int) := hcontent_eq
    exact_mod_cast h
  -- Step 4: use the reduced-form invariant.
  have hreduced : Nat.gcd unit.num.natAbs unit.den = 1 := unit.reduced
  rw [hden_eq_natAbs, Nat.gcd_self] at hreduced
  -- hreduced : unit.num.natAbs = 1
  have hden_one : unit.den = 1 := by rw [hden_eq_natAbs]; exact hreduced
  rcases Int.natAbs_eq unit.num with hpos | hneg
  · left
    apply Rat.ext
    · show unit.num = (1 : Rat).num
      rw [hpos, hreduced]
      rfl
    · show unit.den = (1 : Rat).den
      rw [hden_one]
      rfl
  · right
    apply Rat.ext
    · show unit.num = (-1 : Rat).num
      rw [hneg, hreduced]
      rfl
    · show unit.den = (-1 : Rat).den
      rw [hden_one]
      rfl

/-- Scaling a rational dense polynomial by `0` yields the zero polynomial. -/
private theorem rat_scale_zero (p : DensePoly Rat) :
    DensePoly.scale 0 p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) 0 p n (Rat.mul_zero 0), DensePoly.coeff_zero]
  exact Rat.zero_mul (p.coeff n)

/-- Scaling the zero rational dense polynomial by any unit `u` yields the zero polynomial. -/
private theorem rat_scale_zero_right (u : Rat) :
    DensePoly.scale u (0 : DensePoly Rat) = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) u (0 : DensePoly Rat) n (Rat.mul_zero u),
    DensePoly.coeff_zero]
  exact Rat.mul_zero u

/-- Scaling a rational dense polynomial by `1` leaves it unchanged. -/
private theorem rat_scale_one (p : DensePoly Rat) :
    DensePoly.scale 1 p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) 1 p n (Rat.mul_zero 1)]
  exact Rat.one_mul (p.coeff n)

/-- Reading `(List.range size).map f` at index `n` returns `f n` when `n < size` and `0` past it. -/
private theorem rat_list_getD_map_range (size n : Nat) (f : Nat → Rat) :
    ((List.range size).map f).getD n 0 =
      if n < size then f n else 0 := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

/-- The `n`-th coefficient of `DensePoly.derivative p` is `(n + 1) * p.coeff (n + 1)`. -/
private theorem rat_coeff_derivative (p : DensePoly Rat) (n : Nat) :
    (DensePoly.derivative p).coeff n = ((n + 1 : Nat) : Rat) * p.coeff (n + 1) := by
  unfold DensePoly.derivative
  rw [DensePoly.coeff_ofCoeffs_list]
  change
    ((List.range (p.size - 1)).map
        (fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1))).getD n 0 =
      ((n + 1 : Nat) : Rat) * p.coeff (n + 1)
  rw [rat_list_getD_map_range]
  by_cases hn : n < p.size - 1
  · simp [hn]
  · have hp : p.size ≤ n + 1 := by omega
    have hcoeff : p.coeff (n + 1) = 0 :=
      DensePoly.coeff_eq_zero_of_size_le p hp
    simp [hn, hcoeff]

/-- Differentiation commutes with scaling a rational dense polynomial by a unit `u`. -/
private theorem rat_derivative_scale (u : Rat) (p : DensePoly Rat) :
    DensePoly.derivative (DensePoly.scale u p) =
      DensePoly.scale u (DensePoly.derivative p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [rat_coeff_derivative,
    DensePoly.coeff_scale (R := Rat) u (DensePoly.derivative p) n (Rat.mul_zero u),
    rat_coeff_derivative, DensePoly.coeff_scale (R := Rat) u p (n + 1) (Rat.mul_zero u)]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The Leibniz product rule `derivative (p * q) = derivative p * q + p * derivative q` for rational dense polynomials. -/
private theorem rat_derivative_mul (p q : DensePoly Rat) :
    DensePoly.derivative (p * q) =
      DensePoly.derivative p * q + p * DensePoly.derivative q := by
  apply DensePoly.ext_coeff
  intro n
  rw [rat_coeff_derivative, DensePoly.coeff_mul p q (n + 1)]
  rw [DensePoly.coeff_add (DensePoly.derivative p * q) (p * DensePoly.derivative q) n
    (by exact Rat.zero_add (0 : Rat))]
  rw [DensePoly.coeff_mul (DensePoly.derivative p) q n,
    DensePoly.coeff_mul p (DensePoly.derivative q) n]
  exact DensePoly.rat_mulCoeffSum_derivative_product_rule p q n

/-- If `d` divides `p`, then `d` divides the left multiple `q * p`. -/
private theorem rat_dvd_mul_left {d p : DensePoly Rat} (q : DensePoly Rat) :
    d ∣ p → d ∣ q * p := by
  intro h
  rcases h with ⟨a, ha⟩
  refine ⟨q * a, ?_⟩
  rw [ha, ← DensePoly.mul_assoc_poly q d a, DensePoly.mul_comm_poly q d,
    DensePoly.mul_assoc_poly d q a]

/-- If `d` divides `p`, then `d` divides the right multiple `p * q`. -/
private theorem rat_dvd_mul_right {d p : DensePoly Rat} (q : DensePoly Rat) :
    d ∣ p → d ∣ p * q := by
  intro h
  rw [DensePoly.mul_comm_poly p q]
  exact rat_dvd_mul_left q h

/-- Divisibility by `d` is closed under addition of rational dense polynomials. -/
private theorem rat_dvd_add {d p q : DensePoly Rat} :
    d ∣ p → d ∣ q → d ∣ p + q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb, DensePoly.mul_add_right_poly]

/-- Divisibility by `d` is closed under subtraction of rational dense polynomials. -/
private theorem rat_dvd_sub {d p q : DensePoly Rat} :
    d ∣ p → d ∣ q → d ∣ p - q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + (0 - b), ?_⟩
  rw [DensePoly.sub_eq_add_neg_poly, ha, hb, DensePoly.mul_add_right_poly,
    DensePoly.mul_sub_zero_comm, DensePoly.mul_comm_poly b d]

/-- The rational image of `p` is a `±1` scalar multiple of the rational image of its sign-normalized primitive part. -/
private theorem toRatPoly_normalizePrimitiveSign_rational_associate (p : ZPoly) :
    ∃ unit : Rat, toRatPoly p = DensePoly.scale unit (toRatPoly (normalizePrimitiveSign p)) := by
  by_cases hlead : DensePoly.leadingCoeff p < 0
  · refine ⟨-1, ?_⟩
    rw [normalizePrimitiveSign, if_pos hlead]
    have h := rat_scale_toRatPoly_neg_int (1 : Rat) p
    rw [rat_scale_one] at h
    simpa using h
  · refine ⟨1, ?_⟩
    rw [normalizePrimitiveSign, if_neg hlead]
    exact (rat_scale_one (toRatPoly p)).symm

/-- Folding a step that discards each element leaves the initial accumulator `init` unchanged. -/
private theorem rat_list_foldl_ignore {α : Type _} (xs : List Nat) (init : α) :
    xs.foldl (fun acc _ => acc) init = init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons _ xs ih =>
      simpa using ih init

/-- Scaling a rational dense polynomial by a nonzero unit `u` preserves its dense size. -/
private theorem rat_scale_size_of_ne_zero {u : Rat} (hu : u ≠ 0) (p : DensePoly Rat) :
    (DensePoly.scale u p).size = p.size := by
  apply Nat.le_antisymm
  · by_cases hle : (DensePoly.scale u p).size ≤ p.size
    · exact hle
    · have hlt : p.size < (DensePoly.scale u p).size := Nat.lt_of_not_ge hle
      let i := (DensePoly.scale u p).size - 1
      have hscaled_ne : (DensePoly.scale u p).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.scale u p) (by omega)
      have hp_zero : p.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le p (by
        unfold i
        omega)
      exfalso
      apply hscaled_ne
      rw [DensePoly.coeff_scale (R := Rat) u p i (Rat.mul_zero u), hp_zero, Rat.mul_zero]
  · by_cases hle : p.size ≤ (DensePoly.scale u p).size
    · exact hle
    · have hlt : (DensePoly.scale u p).size < p.size := Nat.lt_of_not_ge hle
      let i := p.size - 1
      have hp_ne : p.coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size p (by omega)
      have hscaled_zero : (DensePoly.scale u p).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale u p) (by
          unfold i
          omega)
      exfalso
      apply hp_ne
      have hmul_zero : u * p.coeff i = 0 := by
        rw [← DensePoly.coeff_scale (R := Rat) u p i (Rat.mul_zero u)]
        exact hscaled_zero
      exact (Rat.mul_eq_zero.mp hmul_zero).resolve_left hu

/-- `rat_scale_mulCoeffStep`: scaling the factors by `u` and `v` pulls the
`u * v` factor out through one `mulCoeffStep` term of the coefficient
convolution. -/
private theorem rat_scale_mulCoeffStep (u v : Rat) (p q : DensePoly Rat)
    (n i : Nat) (a : Rat) (j : Nat) :
    DensePoly.mulCoeffStep (DensePoly.scale u p) (DensePoly.scale v q) n i
        ((u * v) * a) j =
      (u * v) * DensePoly.mulCoeffStep p q n i a j := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · rw [if_pos hij, if_pos hij]
    rw [DensePoly.coeff_scale (R := Rat) u p i (Rat.mul_zero u),
      DensePoly.coeff_scale (R := Rat) v q j (Rat.mul_zero v)]
    grind
  · rw [if_neg hij, if_neg hij]

/-- `rat_scale_mulCoeffStep_fold`: the `u * v` factor pulls out through the
inner `mulCoeffStep` fold that accumulates one output coefficient. -/
private theorem rat_scale_mulCoeffStep_fold (u v : Rat) (p q : DensePoly Rat)
    (n i : Nat) (xs : List Nat) (a : Rat) :
    xs.foldl
        (DensePoly.mulCoeffStep (DensePoly.scale u p) (DensePoly.scale v q) n i)
        ((u * v) * a) =
      (u * v) * xs.foldl (DensePoly.mulCoeffStep p q n i) a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [rat_scale_mulCoeffStep]
      exact ih (DensePoly.mulCoeffStep p q n i a j)

/-- `rat_scale_mulCoeffOuter_fold`: the `u * v` factor pulls out through the
outer coefficient fold over the rows of the convolution. -/
private theorem rat_scale_mulCoeffOuter_fold (u v : Rat) (p q : DensePoly Rat)
    (n : Nat) (xs : List Nat) (a : Rat) :
    xs.foldl
        (fun acc i =>
          (List.range q.size).foldl
            (DensePoly.mulCoeffStep (DensePoly.scale u p) (DensePoly.scale v q) n i) acc)
        ((u * v) * a) =
      (u * v) *
        xs.foldl
          (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc)
          a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [rat_scale_mulCoeffStep_fold]
      exact ih ((List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a)

/-- `rat_scale_mulCoeffSum_of_ne_zero`: for nonzero scalars the convolution
sum of the scaled factors equals `u * v` times the unscaled sum, using that
nonzero scaling preserves the operand sizes. -/
private theorem rat_scale_mulCoeffSum_of_ne_zero {u v : Rat} (hu : u ≠ 0) (hv : v ≠ 0)
    (p q : DensePoly Rat) (n : Nat) :
    DensePoly.mulCoeffSum (DensePoly.scale u p) (DensePoly.scale v q) n =
      (u * v) * DensePoly.mulCoeffSum p q n := by
  unfold DensePoly.mulCoeffSum
  rw [rat_scale_size_of_ne_zero hu p, rat_scale_size_of_ne_zero hv q]
  have key := rat_scale_mulCoeffOuter_fold u v p q n (List.range p.size) 0
  simp only [Rat.mul_zero] at key
  exact key

/-- `rat_scale_mul_scale`: scaling distributes over the product, so
`scale u p * scale v q = scale (u * v) (p * q)`. -/
private theorem rat_scale_mul_scale (u v : Rat) (p q : DensePoly Rat) :
    DensePoly.scale u p * DensePoly.scale v q =
      DensePoly.scale (u * v) (p * q) := by
  by_cases hu : u = 0
  · subst u
    rw [rat_scale_zero, Rat.zero_mul, rat_scale_zero]
    rfl
  · by_cases hv : v = 0
    · subst v
      rw [rat_scale_zero, Rat.mul_zero, rat_scale_zero]
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_mul, DensePoly.coeff_zero]
      unfold DensePoly.mulCoeffSum
      exact rat_list_foldl_ignore (List.range (DensePoly.scale u p).size) (0 : Rat)
    · apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_mul, rat_scale_mulCoeffSum_of_ne_zero hu hv,
        DensePoly.coeff_scale (R := Rat) (u * v) (p * q) n (Rat.mul_zero (u * v)),
        DensePoly.coeff_mul]

/-- `rat_dvd_scale_of_dvd`: a divisor of `p` also divides any scalar multiple
`scale u p`, since the witness scales along with the dividend. -/
private theorem rat_dvd_scale_of_dvd (u : Rat) {d p : DensePoly Rat} :
    d ∣ p → d ∣ DensePoly.scale u p := by
  intro hdp
  rcases hdp with ⟨a, ha⟩
  refine ⟨DensePoly.scale u a, ?_⟩
  rw [ha]
  have hscale := rat_scale_mul_scale (1 : Rat) u d a
  rw [rat_scale_one, Rat.one_mul] at hscale
  exact hscale.symm

/-- `rat_leadingCoeff_ne_zero_of_pos_size`: a polynomial of positive size has a
nonzero leading coefficient, identifying it with the last stored coefficient. -/
private theorem rat_leadingCoeff_ne_zero_of_pos_size (p : DensePoly Rat) (hpos : 0 < p.size) :
    p.leadingCoeff ≠ 0 := by
  have hidx : p.coeffs.size - 1 < p.coeffs.size := by
    simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
  have hlead_eq : p.leadingCoeff = p.coeff (p.size - 1) := by
    simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
  rw [hlead_eq]
  exact DensePoly.coeff_last_ne_zero_of_pos_size p hpos

/-- `rat_div_mul_cancel_of_ne`: for a nonzero `Rat` divisor, `a / b * b = a`,
stated as `a - (a / b) * b = 0` for the remainder-degree argument below. -/
private theorem rat_div_mul_cancel_of_ne (a b : Rat) (hb : b ≠ 0) :
    a - (a / b) * b = 0 := by
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- `rat_divMod_remainder_degree_lt_core`: over `DensePoly Rat`, the
`divMod` remainder has strictly smaller degree than a positive-degree
divisor. -/
private theorem rat_divMod_remainder_degree_lt_core (p q : DensePoly Rat)
    (hdegree : 0 < q.degree?.getD 0) :
    (DensePoly.divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  apply DensePoly.divMod_remainder_degree_lt_of_pos_degree_core p q hdegree
  intro a
  apply rat_div_mul_cancel_of_ne
  apply rat_leadingCoeff_ne_zero_of_pos_size
  by_cases hq : q.size = 0
  · have hdeg : q.degree?.getD 0 = 0 := by
      simp [DensePoly.degree?, hq]
    omega
  · exact Nat.pos_of_ne_zero hq

/-- `rat_divMod_spec_core`: the `DensePoly Rat` reconstruction identity
`qr.1 * q + qr.2 = p` for `DensePoly.divMod` (holds unconditionally). -/
private theorem rat_divMod_spec_core (p q : DensePoly Rat) :
    let qr := DensePoly.divMod p q
    qr.1 * q + qr.2 = p := by
  by_cases hq : q.size = 0
  · have hrem := DensePoly.divMod_remainder_eq_self_of_size_zero_core p q hq
    have hqzero : q = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_eq_zero_of_size_le q (by omega), DensePoly.coeff_zero]
      rfl
    change (DensePoly.divMod p q).1 * q + (DensePoly.divMod p q).2 = p
    rw [hrem, hqzero]
    rw [DensePoly.mul_comm_poly ((DensePoly.divMod p (0 : DensePoly Rat)).1)
      (0 : DensePoly Rat)]
    rw [DensePoly.zero_mul, DensePoly.zero_add]
  · have hcancel :
        ∀ a : Rat, a - (a / q.leadingCoeff) * q.leadingCoeff = 0 := by
      intro a
      apply rat_div_mul_cancel_of_ne
      exact rat_leadingCoeff_ne_zero_of_pos_size q (Nat.pos_of_ne_zero hq)
    by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
    · rw [DensePoly.divMod_eq_zero_self_of_degree_lt p q hlt]
      change (0 : DensePoly Rat) * q + p = p
      rw [DensePoly.zero_mul, DensePoly.zero_add]
    · unfold DensePoly.divMod
      rw [if_neg hlt]
      exact DensePoly.divModArray_reconstruction p q
        (fun coeff : Rat => coeff / q.leadingCoeff) hcancel

/-- `rat_divMod_spec_core_of_not_isZero`: the `DensePoly Rat`
reconstruction identity `qr.1 * q + qr.2 = p` for `DensePoly.divMod`
under a nonzero-divisor hypothesis. -/
private theorem rat_divMod_spec_core_of_not_isZero (p q : DensePoly Rat)
    (hqzero : ¬ q.isZero) :
    let qr := DensePoly.divMod p q
    qr.1 * q + qr.2 = p := by
  unfold DensePoly.divMod
  by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
  · simp [hlt]
    rw [DensePoly.zero_mul, DensePoly.zero_add]
  · rw [if_neg hlt]
    exact DensePoly.divModArray_reconstruction p q
      (fun coeff => coeff / q.leadingCoeff)
      (fun a => rat_div_mul_cancel_of_ne a q.leadingCoeff
        (rat_leadingCoeff_ne_zero_of_pos_size q (by
          have hcoeffs : q.coeffs.size ≠ 0 := by
            intro hcoeffs
            apply hqzero
            simpa [DensePoly.isZero, Array.isEmpty_iff_size_eq_zero] using hcoeffs
          simpa [DensePoly.size, Nat.pos_iff_ne_zero] using hcoeffs)))

/-- `rat_mod_remainder_degree_lt_core`: over `DensePoly Rat`, the `mod`
remainder `p % q` has strictly smaller degree than a positive-degree
divisor. -/
private theorem rat_mod_remainder_degree_lt_core (p q : DensePoly Rat)
    (hdegree : 0 < q.degree?.getD 0) :
    (p % q).degree?.getD 0 < q.degree?.getD 0 := by
  exact rat_divMod_remainder_degree_lt_core p q hdegree

/-- `rat_mod_zero_right_of_size_zero`: over `DensePoly Rat`, `p % m = p`
when the divisor `m` has size zero. -/
private theorem rat_mod_zero_right_of_size_zero (p m : DensePoly Rat)
    (hm : m.size = 0) :
    p % m = p := by
  exact DensePoly.divMod_remainder_eq_self_of_size_zero_core p m hm

/-- `rat_mod_sub_self_eq_mul_neg_div_of_not_isZero`: over `DensePoly Rat`
with a nonzero divisor, `p % m - p = m * (0 - p / m)`. -/
private theorem rat_mod_sub_self_eq_mul_neg_div_of_not_isZero (p m : DensePoly Rat)
    (hmzero : ¬ m.isZero) :
    p % m - p = m * (0 - p / m) := by
  have hdiv : (p / m) * m + (p % m) = p := by
    exact rat_divMod_spec_core_of_not_isZero p m hmzero
  calc
    p % m - p = 0 - (p / m) * m := by
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun x : DensePoly Rat => x.coeff n) hdiv
      have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
      have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
      change (((p / m) * m + (p % m)).coeff n = p.coeff n) at hcoeff
      rw [DensePoly.coeff_add ((p / m) * m) (p % m) n hzero_add] at hcoeff
      rw [DensePoly.coeff_sub (p % m) p n hzero_sub,
        DensePoly.coeff_sub 0 ((p / m) * m) n hzero_sub, DensePoly.coeff_zero]
      grind
    _ = m * (0 - (p / m)) := by
      exact (DensePoly.mul_sub_zero_comm m (p / m)).symm

/-- `rat_congr_mod_core`: over `DensePoly Rat`, the remainder `p % m` is
congruent to `p` modulo `m`, i.e. `DensePoly.Congr (p % m) p m`. -/
private theorem rat_congr_mod_core (p m : DensePoly Rat) :
    DensePoly.Congr (p % m) p m := by
  by_cases hmzero : m.isZero
  · refine ⟨0, ?_⟩
    have hmsize : m.size = 0 := by
      simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hmzero
    have hmod : p % m = p := rat_mod_zero_right_of_size_zero p m hmsize
    have hm_eq_zero : m = 0 := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le m (by omega)
    rw [hmod, hm_eq_zero]
    apply DensePoly.ext_coeff
    intro i
    have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
    rw [DensePoly.coeff_sub p p i hzero_sub, DensePoly.zero_mul, DensePoly.coeff_zero]
    grind
  · exact ⟨0 - (p / m), rat_mod_sub_self_eq_mul_neg_div_of_not_isZero p m hmzero⟩

/-- `rat_eq_add_mul_of_sub_eq_mul`: rearranges the remainder relation `p - q = m * r`
into `p = q + m * r`, the additive form used when reconstructing a `DensePoly Rat`
dividend from its remainder and recorded multiplier. -/
private theorem rat_eq_add_mul_of_sub_eq_mul {p q m r : DensePoly Rat}
    (hsub : p - q = m * r) :
    p = q + m * r := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly Rat => x.coeff n) hsub
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
  change (p - q).coeff n = (m * r).coeff n at hcoeff
  rw [DensePoly.coeff_sub p q n hzero_sub] at hcoeff
  rw [DensePoly.coeff_add q (m * r) n hzero_add]
  grind

/-- `rat_add_sub_add_right`: the coefficientwise regrouping
`(a + b) - (c + d) = (a - c) + (b - d)` for `DensePoly Rat`, splitting a difference of
sums into the matching pair of differences in the remainder-delta calculations. -/
private theorem rat_add_sub_add_right (a b c d : DensePoly Rat) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) (c + d) n hzero_sub, DensePoly.coeff_add a b n hzero_add,
    DensePoly.coeff_add c d n hzero_add, DensePoly.coeff_add (a - c) (b - d) n hzero_add,
    DensePoly.coeff_sub a c n hzero_sub, DensePoly.coeff_sub b d n hzero_sub]
  grind

/-- `rat_sub_zero_right`: subtracting the zero polynomial leaves `p` unchanged,
`p - 0 = p` over `DensePoly Rat`. -/
private theorem rat_sub_zero_right (p : DensePoly Rat) :
    p - 0 = p := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  rw [DensePoly.coeff_sub p 0 n hzero_sub, DensePoly.coeff_zero]
  grind

/-- `rat_zero_mod_eq_zero`: the zero polynomial reduces to zero under any modulus,
`(0 : DensePoly Rat) % m = 0`. -/
private theorem rat_zero_mod_eq_zero (m : DensePoly Rat) :
    (0 : DensePoly Rat) % m = 0 :=
  DensePoly.zero_mod_eq_zero_core m

/-- `rat_sub_self_right_add`: cancels the shared left summand, `(a + b) - a = b` over
`DensePoly Rat`, used to discard the `p * q` term in the remainder-delta product
expansion. -/
private theorem rat_sub_self_right_add (a b : DensePoly Rat) :
    (a + b) - a = b := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) a n hzero_sub, DensePoly.coeff_add a b n hzero_add]
  grind

/-- `rat_mul_left_remainder_delta`: expresses the difference between the product of
remainders and the product `p * q` as a multiple of `m`,
`(p % m * (q % m)) - (p * q) = m * (rp * (q % m) + p * rq)`, given the recorded
multipliers `rp`, `rq`; this exhibits `m` as a divisor of the product remainder gap. -/
private theorem rat_mul_left_remainder_delta
    (p q m rp rq : DensePoly Rat)
    (hp : p % m = p + m * rp)
    (hq : q % m = q + m * rq) :
    (p % m * (q % m)) - (p * q) = m * (rp * (q % m) + p * rq) := by
  have hleft :
      (p + m * rp) * (q % m) =
        p * (q % m) + (m * rp) * (q % m) :=
    DensePoly.mul_add_left_poly p (m * rp) (q % m)
  have hright :
      p * (q % m) = p * q + p * (m * rq) := by
    rw [hq]
    exact DensePoly.mul_add_right_poly p q (m * rq)
  calc
    (p % m * (q % m)) - (p * q)
        = ((p + m * rp) * (q % m)) - (p * q) := by rw [hp]
    _ = (p * (q % m) + (m * rp) * (q % m)) - (p * q) := by rw [hleft]
    _ = ((p * q + p * (m * rq)) + (m * rp) * (q % m)) - (p * q) := by
      rw [hright]
    _ = (p * q + (p * (m * rq) + (m * rp) * (q % m))) - (p * q) := by
      exact congrArg (fun x => x - p * q)
        (DensePoly.add_assoc_poly (p * q) (p * (m * rq)) ((m * rp) * (q % m)))
    _ = p * (m * rq) + (m * rp) * (q % m) := by
      rw [rat_sub_self_right_add]
    _ = m * (p * rq) + (m * rp) * (q % m) := by
      apply congrArg (fun x => x + (m * rp) * (q % m))
      calc
        p * (m * rq) = (p * m) * rq := by
          exact (DensePoly.mul_assoc_poly p m rq).symm
        _ = (m * p) * rq := by
          exact congrArg (fun x => x * rq) (DensePoly.mul_comm_poly p m)
        _ = m * (p * rq) := by
          exact DensePoly.mul_assoc_poly m p rq
    _ = m * (p * rq) + m * (rp * (q % m)) := by
      exact congrArg (fun x => m * (p * rq) + x)
        (DensePoly.mul_assoc_poly m rp (q % m))
    _ = m * (p * rq + rp * (q % m)) := by
      exact (DensePoly.mul_add_right_poly m (p * rq) (rp * (q % m))).symm
    _ = m * (rp * (q % m) + p * rq) := by
      exact congrArg (fun x => m * x)
        (DensePoly.add_comm_poly (p * rq) (rp * (q % m)))

/-- `rat_foldl_mulCoeffStep_select`: evaluates the `mulCoeffStep` left-fold over
`List.range m`, showing it adds to `acc` the single surviving summand
`f.coeff i * g.coeff (n - i)` exactly when `i ≤ n` and `n - i < m`, and zero otherwise. -/
private theorem rat_foldl_mulCoeffStep_select
    (f g : DensePoly Rat) (n i m : Nat) (acc : Rat) :
    (List.range m).foldl (DensePoly.mulCoeffStep f g n i) acc =
      acc + (if n < i then 0
        else if n - i < m then f.coeff i * g.coeff (n - i) else 0) := by
  induction m generalizing acc with
  | zero =>
      simp
      grind
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
            grind
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- `rat_foldl_mulCoeffStep_outer`: rewrites the outer index fold over `xs` by replacing
each inner `mulCoeffStep` fold over `List.range g.size` with its selected summand from
`rat_foldl_mulCoeffStep_select`. -/
private theorem rat_foldl_mulCoeffStep_outer
    (f g : DensePoly Rat) (n : Nat) (xs : List Nat) (acc : Rat) :
    xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc =
      xs.foldl
        (fun acc i =>
          acc + (if n < i then 0
            else if n - i < g.size then f.coeff i * g.coeff (n - i) else 0))
        acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [rat_foldl_mulCoeffStep_select]
      exact ih _

/-- `rat_foldl_select_index`: a left-fold over `List.range m` adding `x` only at the
matching index `k` yields `acc + x` when `k < m` and `acc` otherwise. -/
private theorem rat_foldl_select_index
    (k m : Nat) (x : Rat) (acc : Rat) :
    (List.range m).foldl
        (fun acc i => acc + if i = k then x else 0) acc =
      if k < m then acc + x else acc := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      by_cases hk : k < m
      · have hne : m ≠ k := by omega
        have hk' : k < m + 1 := by omega
        simp [hk, hne, hk']
        grind
      · by_cases hkm : m = k
        · subst k
          have hkk : ¬ m < m := by omega
          have hmm : m < m + 1 := by omega
          simp [hkk, hmm]
        · have hk' : ¬ k < m + 1 := by omega
          simp [hk, hk', hkm]
          grind

/-- `rat_coeff_mul_at_top`: the top coefficient of a `DensePoly Rat` product is the
product of the factors' top coefficients,
`(f * g).coeff (f.size - 1 + (g.size - 1)) = f.coeff (f.size - 1) * g.coeff (g.size - 1)`. -/
private theorem rat_coeff_mul_at_top
    (f g : DensePoly Rat) (hf : 0 < f.size) (hg : 0 < g.size) :
    (f * g).coeff (f.size - 1 + (g.size - 1)) =
      f.coeff (f.size - 1) * g.coeff (g.size - 1) := by
  rw [DensePoly.coeff_mul]
  unfold DensePoly.mulCoeffSum
  rw [rat_foldl_mulCoeffStep_outer]
  have hfold_eq : ∀ (xs : List Nat) (acc : Rat),
      (∀ i ∈ xs, i < f.size) →
      xs.foldl
          (fun acc i => acc + (if f.size - 1 + (g.size - 1) < i then 0
            else if f.size - 1 + (g.size - 1) - i < g.size then
              f.coeff i * g.coeff (f.size - 1 + (g.size - 1) - i) else 0)) acc =
        xs.foldl
          (fun acc i => acc + if i = f.size - 1 then
            f.coeff (f.size - 1) * g.coeff (g.size - 1) else 0) acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons j xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        have hj : j < f.size := hxs j (by simp)
        have hnj : ¬ f.size - 1 + (g.size - 1) < j := by omega
        by_cases heq : j = f.size - 1
        · subst j
          have hsub : f.size - 1 + (g.size - 1) - (f.size - 1) = g.size - 1 := by omega
          have hbound : g.size - 1 < g.size := by omega
          simp [hnj, hsub, hbound]
          exact ih (acc + f.coeff (f.size - 1) * g.coeff (g.size - 1))
            (fun k hk => hxs k (by simp [hk]))
        · have hjlt : j < f.size - 1 := by omega
          have hnotbound : ¬ f.size - 1 + (g.size - 1) - j < g.size := by omega
          simp [hnj, hnotbound, heq]
          exact ih (acc + 0) (fun k hk => hxs k (by simp [hk]))
  rw [hfold_eq (List.range f.size) (Zero.zero : Rat)
    (by intro i hi; exact List.mem_range.mp hi)]
  rw [rat_foldl_select_index]
  have hfm1 : f.size - 1 < f.size := by omega
  simp [hfm1]
  show (0 : Rat) + _ = _
  grind

private theorem rat_eq_zero_of_size_zero (p : DensePoly Rat) (hsize : p.size = 0) :
    p = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_zero]
  exact DensePoly.coeff_eq_zero_of_size_le p (by omega)

private theorem rat_mul_zero_right (p : DensePoly Rat) :
    p * 0 = 0 := by
  rw [DensePoly.mul_comm_poly p (0 : DensePoly Rat)]
  exact DensePoly.zero_mul p

private theorem rat_product_size_gt_top
    (f g : DensePoly Rat) (hf : 0 < f.size) (hg : 0 < g.size) :
    f.size - 1 + (g.size - 1) < (f * g).size := by
  have htop := rat_coeff_mul_at_top f g hf hg
  have hf_ne : f.coeff (f.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size f hf
  have hg_ne : g.coeff (g.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size g hg
  have hprod_ne :
      f.coeff (f.size - 1) * g.coeff (g.size - 1) ≠ 0 := by
    intro hprod
    rcases Rat.mul_eq_zero.mp hprod with hf_zero | hg_zero
    · exact hf_ne hf_zero
    · exact hg_ne hg_zero
  have hcoeff_ne :
      (f * g).coeff (f.size - 1 + (g.size - 1)) ≠ 0 := by
    rw [htop]
    exact hprod_ne
  rcases Nat.lt_or_ge (f.size - 1 + (g.size - 1)) (f * g).size with hlt | hle
  · exact hlt
  · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le (f * g) hle))

/-- A nonzero rational polynomial divisor has size at most the size of the
nonzero polynomial it divides. -/
theorem rat_size_le_of_dvd_nonzero
    {d r : DensePoly Rat} (hd : d.size ≠ 0) (hr : r.size ≠ 0) :
    d ∣ r → d.size ≤ r.size := by
  intro hdiv
  rcases hdiv with ⟨k, hk⟩
  by_cases hk_zero : k.size = 0
  · have hk_eq : k = 0 := rat_eq_zero_of_size_zero k hk_zero
    have hr_eq_zero : r = 0 := by
      rw [hk_eq, rat_mul_zero_right] at hk
      exact hk
    have hr_size_zero : r.size = 0 := by
      rw [hr_eq_zero]
      exact DensePoly.size_zero
    contradiction
  · have hd_pos : 0 < d.size := Nat.pos_of_ne_zero hd
    have hk_pos : 0 < k.size := Nat.pos_of_ne_zero hk_zero
    have htop := rat_product_size_gt_top d k hd_pos hk_pos
    have hsize_eq : (d * k).size = r.size := by rw [← hk]
    rw [hsize_eq] at htop
    omega

/-- Uniqueness of the canonical remainder representative: if `r` and `s` both
have degree strictly below `m`'s degree and are congruent modulo `m`, they are
equal. Their difference `r - s` is a multiple of `m` yet has degree below `m`,
forcing the multiplier (hence `r - s`) to be zero. -/
private theorem rat_canonical_remainder_unique_of_pos_degree
    (r s m : DensePoly Rat)
    (hr : r.degree?.getD 0 < m.degree?.getD 0)
    (hs : s.degree?.getD 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr r s m) :
    r = s := by
  rcases hcongr with ⟨k, hk⟩
  have hm_pos : 0 < m.degree?.getD 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  have hm_size_ge : 2 ≤ m.size := by
    by_cases hms : m.size = 0
    · simp [DensePoly.degree?, hms] at hm_pos
    · have hdeg_eq : m.degree?.getD 0 = m.size - 1 := by
        simp [DensePoly.degree?, hms]
      rw [hdeg_eq] at hm_pos
      omega
  have hm_deg : m.degree?.getD 0 = m.size - 1 := by
    have hms : m.size ≠ 0 := by omega
    simp [DensePoly.degree?, hms]
  have hr_size_le : r.size ≤ m.size - 1 := by
    by_cases hrs : r.size = 0
    · omega
    · have hr_deg : r.degree?.getD 0 = r.size - 1 := by simp [DensePoly.degree?, hrs]
      rw [hr_deg, hm_deg] at hr
      omega
  have hs_size_le : s.size ≤ m.size - 1 := by
    by_cases hss : s.size = 0
    · omega
    · have hs_deg : s.degree?.getD 0 = s.size - 1 := by simp [DensePoly.degree?, hss]
      rw [hs_deg, hm_deg] at hs
      omega
  have hzero_sub : (0 : Rat) - 0 = 0 := by grind
  have hrs_top_zero : ∀ i, max r.size s.size ≤ i → (r - s).coeff i = 0 := by
    intro i hi
    rw [DensePoly.coeff_sub r s i hzero_sub]
    have hr_zero := DensePoly.coeff_eq_zero_of_size_le r (by omega : r.size ≤ i)
    have hs_zero := DensePoly.coeff_eq_zero_of_size_le s (by omega : s.size ≤ i)
    rw [hr_zero, hs_zero]
    grind
  have hmax_le : max r.size s.size ≤ m.size - 1 :=
    Nat.max_le.mpr ⟨hr_size_le, hs_size_le⟩
  have hrs_size_le : (r - s).size ≤ m.size - 1 := by
    by_cases hrs_zero : (r - s).size = 0
    · omega
    · have hrs_pos : 0 < (r - s).size := Nat.pos_of_ne_zero hrs_zero
      have htop := DensePoly.coeff_last_ne_zero_of_pos_size (r - s) hrs_pos
      have hbound : (r - s).size - 1 < max r.size s.size := by
        rcases Nat.lt_or_ge ((r - s).size - 1) (max r.size s.size) with h | hge
        · exact h
        · exact False.elim (htop (hrs_top_zero ((r - s).size - 1) hge))
      have hsub_lt : (r - s).size - 1 < m.size - 1 := Nat.lt_of_lt_of_le hbound hmax_le
      omega
  by_cases hk_zero : k.size = 0
  · have hk_eq : k = 0 := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le k (by omega)
    have hmul_zero : m * (0 : DensePoly Rat) = 0 := by
      have hcomm := DensePoly.mul_comm_poly m (0 : DensePoly Rat)
      have hzm := DensePoly.zero_mul m
      exact hcomm.trans hzm
    rw [hk_eq] at hk
    rw [hmul_zero] at hk
    apply DensePoly.ext_coeff
    intro i
    have hcoeff := congrArg (fun x : DensePoly Rat => x.coeff i) hk
    change (r - s).coeff i = (0 : DensePoly Rat).coeff i at hcoeff
    rw [DensePoly.coeff_sub r s i hzero_sub, DensePoly.coeff_zero] at hcoeff
    grind
  · have hk_pos : 0 < k.size := Nat.pos_of_ne_zero hk_zero
    have hm_pos_size : 0 < m.size := by omega
    have htop := rat_coeff_mul_at_top m k hm_pos_size hk_pos
    have hm_lead_ne : m.coeff (m.size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size m hm_pos_size
    have hk_lead_ne : k.coeff (k.size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size k hk_pos
    have hprod_ne : m.coeff (m.size - 1) * k.coeff (k.size - 1) ≠ 0 := by
      intro hprod
      rcases Rat.mul_eq_zero.mp hprod with hh | hh
      · exact hm_lead_ne hh
      · exact hk_lead_ne hh
    have hcoeff_ne : (m * k).coeff (m.size - 1 + (k.size - 1)) ≠ 0 := by
      rw [htop]
      exact hprod_ne
    have hmk_size_gt : m.size - 1 + (k.size - 1) < (m * k).size := by
      rcases Nat.lt_or_ge (m.size - 1 + (k.size - 1)) (m * k).size with h | hle
      · exact h
      · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le (m * k) hle))
    have hmk_eq_rs : (m * k).size = (r - s).size := by rw [← hk]
    omega

/-- Congruence descends to remainders: if `p ≡ q (mod m)` then the remainders
`p % m` and `q % m` are themselves congruent modulo `m`. The witnessing
multiplier is assembled from those of `p ≡ p % m`, `q ≡ q % m`, and `p ≡ q`. -/
private theorem rat_mod_remainders_congr_of_congr (p q m : DensePoly Rat)
    (hcongr : DensePoly.Congr p q m) :
    DensePoly.Congr (p % m) (q % m) m := by
  rcases rat_congr_mod_core p m with ⟨rp, hp⟩
  rcases rat_congr_mod_core q m with ⟨rq, hq⟩
  rcases hcongr with ⟨k, hk⟩
  refine ⟨(k + rp) + (0 - rq), ?_⟩
  have hp_add : p % m = p + m * rp := rat_eq_add_mul_of_sub_eq_mul hp
  have hq_add : q % m = q + m * rq := rat_eq_add_mul_of_sub_eq_mul hq
  have hneg_mul : (0 : DensePoly Rat) - m * rq =
      m * ((0 : DensePoly Rat) - rq) := by
    calc
      (0 : DensePoly Rat) - m * rq =
          (0 : DensePoly Rat) - rq * m := by
        exact congrArg (fun x : DensePoly Rat => (0 : DensePoly Rat) - x)
          (DensePoly.mul_comm_poly m rq)
      _ = m * ((0 : DensePoly Rat) - rq) := by
        exact (DensePoly.mul_sub_zero_comm m rq).symm
  calc
    (p % m) - (q % m)
        = (p + m * rp) - (q + m * rq) := by rw [hp_add, hq_add]
    _ = (p - q) + ((m * rp) - (m * rq)) := by
      exact rat_add_sub_add_right p (m * rp) q (m * rq)
    _ = m * k + ((m * rp) - (m * rq)) := by rw [hk]
    _ = m * k + (m * rp + ((0 : DensePoly Rat) - m * rq)) := by
      exact congrArg (fun x : DensePoly Rat => m * k + x)
        (DensePoly.sub_eq_add_neg_poly (m * rp) (m * rq))
    _ = m * k + (m * rp + m * ((0 : DensePoly Rat) - rq)) := by rw [hneg_mul]
    _ = (m * k + m * rp) + m * ((0 : DensePoly Rat) - rq) := by
      exact (DensePoly.add_assoc_poly (m * k) (m * rp)
        (m * ((0 : DensePoly Rat) - rq))).symm
    _ = m * (k + rp) + m * ((0 : DensePoly Rat) - rq) := by
      exact congrArg
        (fun x : DensePoly Rat => x + m * ((0 : DensePoly Rat) - rq))
        (DensePoly.mul_add_right_poly m k rp).symm
    _ = m * ((k + rp) + ((0 : DensePoly Rat) - rq)) := by
      exact (DensePoly.mul_add_right_poly m (k + rp)
        ((0 : DensePoly Rat) - rq)).symm

/-- When `m` has positive degree, congruent polynomials have equal remainders
modulo `m`. Both remainders have degree below `m` and are congruent (by
`rat_mod_remainders_congr_of_congr`), so uniqueness of the canonical remainder
makes them equal. -/
private theorem rat_mod_eq_mod_of_congr_pos_degree (p q m : DensePoly Rat)
    (hdegree : 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr p q m) :
    p % m = q % m := by
  apply rat_canonical_remainder_unique_of_pos_degree
  · exact rat_mod_remainder_degree_lt_core p m hdegree
  · exact rat_mod_remainder_degree_lt_core q m hdegree
  · exact rat_mod_remainders_congr_of_congr p q m hcongr

/-- Coefficientwise cancellation: if `p - q = 0` then `p = q`. -/
private theorem rat_eq_of_sub_eq_zero (p q : DensePoly Rat)
    (hsub : p - q = 0) :
    p = q := by
  apply DensePoly.ext_coeff
  intro i
  have hcoeff := congrArg (fun x : DensePoly Rat => x.coeff i) hsub
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  change (p - q).coeff i = (0 : DensePoly Rat).coeff i at hcoeff
  rw [DensePoly.coeff_sub p q i hzero_sub, DensePoly.coeff_zero] at hcoeff
  grind

/-- When `m` has non-positive degree, congruent polynomials still have equal
remainders modulo `m`. If `m = 0` both remainders are the inputs themselves,
which the congruence forces equal; if `m` is a nonzero constant both remainders
are zero. -/
private theorem rat_mod_eq_mod_of_congr_not_pos_degree (p q m : DensePoly Rat)
    (hdegree : ¬ 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr p q m) :
    p % m = q % m := by
  by_cases hm_zero : m.size = 0
  · rw [rat_mod_zero_right_of_size_zero p m hm_zero,
      rat_mod_zero_right_of_size_zero q m hm_zero]
    rcases hcongr with ⟨k, hk⟩
    have hm_eq_zero : m = 0 := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le m (by omega)
    have hmk_zero : m * k = 0 := by
      rw [hm_eq_zero]
      exact DensePoly.zero_mul k
    apply rat_eq_of_sub_eq_zero p q
    rw [hk, hmk_zero]
  · have hm_size : m.size = 1 := by
      have hm_pos : 0 < m.size := Nat.pos_of_ne_zero hm_zero
      have hdeg : m.degree?.getD 0 = m.size - 1 := by
        simp [DensePoly.degree?, hm_zero]
      rw [hdeg] at hdegree
      omega
    have hlead_ne : m.leadingCoeff ≠ (Zero.zero : Rat) := by
      exact rat_leadingCoeff_ne_zero_of_pos_size m (by omega)
    have hpmod :
        p % m = 0 := by
      exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core p m hm_size
        (fun a => rat_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    have hqmod :
        q % m = 0 := by
      exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core q m hm_size
        (fun a => rat_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    rw [hpmod, hqmod]

/-- Congruent polynomials always have equal remainders modulo `m`, obtained by
case-splitting on whether `m` has positive degree and dispatching to the two
preceding lemmas. This is the workhorse behind the `mod_eq_mod_of_congr` law. -/
private theorem rat_mod_eq_mod_of_congr_core (p q m : DensePoly Rat)
    (hcongr : DensePoly.Congr p q m) :
    p % m = q % m := by
  by_cases hdegree : 0 < m.degree?.getD 0
  · exact rat_mod_eq_mod_of_congr_pos_degree p q m hdegree hcongr
  · exact rat_mod_eq_mod_of_congr_not_pos_degree p q m hdegree hcongr

/-- Divisibility makes the remainder vanish: if `q ∣ p` then `p % q = 0`. Since
`q ∣ p` gives `p ≡ 0 (mod q)`, the remainders of `p` and `0` agree, and `0 % q`
is `0`. -/
private theorem rat_mod_eq_zero_of_dvd_core (p q : DensePoly Rat)
    (hdiv : q ∣ p) :
    p % q = 0 := by
  rcases hdiv with ⟨r, hr⟩
  rw [← rat_zero_mod_eq_zero q]
  apply rat_mod_eq_mod_of_congr_core
  exact ⟨r, by
    rw [rat_sub_zero_right, hr]⟩

/-- Dividing by a nonzero constant leaves no remainder: when `q` is nonzero but
has non-positive degree (so `q` is a nonzero constant), the remainder component
of `divMod p q` is zero, because the leading coefficient is invertible. -/
private theorem rat_divMod_remainder_eq_zero_of_not_pos_degree (p q : DensePoly Rat)
    (hqfalse : q.isZero = false)
    (hdegree : ¬ 0 < q.degree?.getD 0) :
    (DensePoly.divMod p q).2 = 0 := by
  have hqsize_ne : q.size ≠ 0 := by
    intro hsize
    have hzero : q.isZero = true := by
      simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hsize
    rw [hzero] at hqfalse
    contradiction
  have hqsize : q.size = 1 := by
    have hdeg : q.degree?.getD 0 = q.size - 1 := by
      simp [DensePoly.degree?, hqsize_ne]
    rw [hdeg] at hdegree
    omega
  have hlead_ne : q.leadingCoeff ≠ (Zero.zero : Rat) := by
    exact rat_leadingCoeff_ne_zero_of_pos_size q (by omega)
  exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core p q hqsize
    (fun a => rat_div_mul_cancel_of_ne a q.leadingCoeff hlead_ne)

private instance ratDivModLaws : DensePoly.DivModLaws Rat where
  divMod_spec := by
    intro p q
    exact rat_divMod_spec_core p q
  divMod_remainder_degree_lt_of_pos_degree := by
    intro p q hdegree
    exact rat_divMod_remainder_degree_lt_core p q hdegree
  divModMonic_eq_divMod_of_monic := by
    intro p q hmonic
    by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
    · rw [DensePoly.divMod_eq_zero_self_of_degree_lt p q hlt]
      unfold DensePoly.divModMonic
      exact DensePoly.divModArray_eq_zero_self_of_degree_lt p q id hlt
    · apply DensePoly.divModMonic_eq_divMod_of_monic_core p q hmonic hlt
      intro a
      rw [hmonic]
      grind [Rat.div_def]
  mod_self_eq_zero := by
    intro p
    apply rat_mod_eq_zero_of_dvd_core
    exact ⟨1, (DensePoly.mul_one_right_poly p).symm⟩
  mod_eq_zero_of_dvd := by
    intro p q hdiv
    exact rat_mod_eq_zero_of_dvd_core p q hdiv
  mod_mod_of_not_pos_degree := by
    intro p q hdegree
    exact rat_mod_eq_mod_of_congr_core (p % q) p q (rat_congr_mod_core p q)
  mod_eq_mod_of_congr := by
    intro p q m hcongr
    exact rat_mod_eq_mod_of_congr_core p q m hcongr
  mod_add_mod := by
    intro p q m
    apply Eq.symm
    apply rat_mod_eq_mod_of_congr_core
    rcases rat_congr_mod_core p m with ⟨rp, hp⟩
    rcases rat_congr_mod_core q m with ⟨rq, hq⟩
    exact ⟨rp + rq, by
      calc
        (p % m + q % m) - (p + q)
            = (p % m - p) + (q % m - q) :=
              rat_add_sub_add_right (p % m) (q % m) p q
        _ = m * rp + m * rq := by rw [hp, hq]
        _ = m * (rp + rq) := by
          exact (DensePoly.mul_add_right_poly m rp rq).symm⟩
  mod_mul_mod := by
    intro p q m
    apply Eq.symm
    apply rat_mod_eq_mod_of_congr_core
    rcases rat_congr_mod_core p m with ⟨rp, hp⟩
    rcases rat_congr_mod_core q m with ⟨rq, hq⟩
    exact ⟨rp * (q % m) + p * rq, by
      have hp' : p % m = p + m * rp := rat_eq_add_mul_of_sub_eq_mul hp
      have hq' : q % m = q + m * rq := rat_eq_add_mul_of_sub_eq_mul hq
      exact rat_mul_left_remainder_delta p q m rp rq hp' hq'⟩

instance ratGcdLaws : DensePoly.GcdLaws Rat where
  gcd_dvd_left := by
    intro f g
    exact DensePoly.gcd_dvd_left_of_divModLaws
      rat_divMod_remainder_eq_zero_of_not_pos_degree f g
  gcd_dvd_right := by
    intro f g
    exact DensePoly.gcd_dvd_right_of_divModLaws
      rat_divMod_remainder_eq_zero_of_not_pos_degree f g
  dvd_gcd := by
    intro d f g hdf hdg
    exact DensePoly.dvd_gcd_of_divModLaws d f g hdf hdg
  xgcd_bezout := by
    intro f g
    exact DensePoly.xgcd_bezout_of_divModLaws f g

private theorem rat_gcd_size_ne_zero_of_left_ne_zero
    (p q : DensePoly Rat) (hp : p ≠ 0) :
    (DensePoly.gcd p q).size ≠ 0 := by
  intro hsize
  have hgcd_zero : DensePoly.gcd p q = 0 :=
    rat_eq_zero_of_size_zero (DensePoly.gcd p q) hsize
  rcases DensePoly.gcd_dvd_left p q with ⟨a, ha⟩
  apply hp
  rw [hgcd_zero, DensePoly.zero_mul] at ha
  exact ha

private theorem rat_squareFree_of_rational_associate
    {p q : DensePoly Rat} {u : Rat}
    (_hu : u ≠ 0) (hp : p ≠ 0)
    (hassoc : p = DensePoly.scale u q)
    (hsq : (DensePoly.gcd p (DensePoly.derivative p)).size ≤ 1) :
    (DensePoly.gcd q (DensePoly.derivative q)).size ≤ 1 := by
  let d := DensePoly.gcd q (DensePoly.derivative q)
  by_cases hdle : d.size ≤ 1
  · simpa [d]
  · exfalso
    have hdgt : 1 < d.size := Nat.lt_of_not_ge hdle
    have hddq : d ∣ q := by
      simpa [d] using DensePoly.gcd_dvd_left q (DensePoly.derivative q)
    have hddq' : d ∣ DensePoly.derivative q := by
      simpa [d] using DensePoly.gcd_dvd_right q (DensePoly.derivative q)
    have hdp : d ∣ p := by
      rw [hassoc]
      exact rat_dvd_scale_of_dvd u hddq
    have hdp' : d ∣ DensePoly.derivative p := by
      rw [hassoc, rat_derivative_scale]
      exact rat_dvd_scale_of_dvd u hddq'
    have hdg : d ∣ DensePoly.gcd p (DensePoly.derivative p) :=
      DensePoly.dvd_gcd d p (DensePoly.derivative p) hdp hdp'
    have hd_ne : d.size ≠ 0 := by omega
    have hg_ne : (DensePoly.gcd p (DensePoly.derivative p)).size ≠ 0 :=
      rat_gcd_size_ne_zero_of_left_ne_zero p (DensePoly.derivative p) hp
    have hsize_le :
        d.size ≤ (DensePoly.gcd p (DensePoly.derivative p)).size :=
      rat_size_le_of_dvd_nonzero hd_ne hg_ne hdg
    omega

private theorem rat_div_gcd_mul_reconstruct (f df : DensePoly Rat) :
    (f / DensePoly.gcd f df) * DensePoly.gcd f df = f := by
  have hspec := DensePoly.div_mul_add_mod f (DensePoly.gcd f df)
  have hmod :
      f % DensePoly.gcd f df = 0 :=
    DensePoly.mod_eq_zero_of_dvd f (DensePoly.gcd f df)
      (DensePoly.gcd_dvd_left f df)
  rw [hmod] at hspec
  rw [DensePoly.add_zero_poly] at hspec
  exact hspec

private theorem rat_common_divisor_quotient_derivative_dvd_repeated
    (ratPrimitive : DensePoly Rat) :
    let derivative := DensePoly.derivative ratPrimitive
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    ∀ d : DensePoly Rat,
      d ∣ quotientRat →
      d ∣ DensePoly.derivative quotientRat →
      d ∣ repeatedRat := by
  intro derivative repeatedRat quotientRat d hdq hdq'
  have hrec : quotientRat * repeatedRat = ratPrimitive := by
    simpa [quotientRat, repeatedRat, derivative] using
      rat_div_gcd_mul_reconstruct ratPrimitive derivative
  have hdfactor :
      d ∣ quotientRat * repeatedRat := rat_dvd_mul_right repeatedRat hdq
  have hdf : d ∣ ratPrimitive := by
    simpa [hrec] using hdfactor
  have hderivative_factor :
      d ∣ DensePoly.derivative (quotientRat * repeatedRat) := by
    rw [rat_derivative_mul]
    apply rat_dvd_add
    · exact rat_dvd_mul_right repeatedRat hdq'
    · exact rat_dvd_mul_right (DensePoly.derivative repeatedRat) hdq
  have hddf : d ∣ derivative := by
    simpa [derivative, hrec] using hderivative_factor
  simpa [repeatedRat] using DensePoly.dvd_gcd d ratPrimitive derivative hdf hddf

/-- If `d` divides the derivative of a product `d * a`, then `d` divides
`a * d'` (where `d' = derivative d`). This is the characteristic-zero
"derivative cofactor" identity used in iterated divisibility arguments
for the square-free quotient. -/
private theorem rat_dvd_cofactor_derivative
    (d a : DensePoly Rat)
    (hdq' : d ∣ DensePoly.derivative (d * a)) :
    d ∣ a * DensePoly.derivative d := by
  rw [rat_derivative_mul] at hdq'
  have hda' : d ∣ d * DensePoly.derivative a :=
    ⟨DensePoly.derivative a, rfl⟩
  have hsub := rat_dvd_sub hdq' hda'
  have heq :
      DensePoly.derivative d * a + d * DensePoly.derivative a -
        d * DensePoly.derivative a =
        DensePoly.derivative d * a := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_add_semiring]
    grind
  rw [heq] at hsub
  rw [DensePoly.mul_comm_poly]
  exact hsub

/-- Iterated polynomial power for `DensePoly Rat`. We avoid relying on a generic
`Monoid` instance and define this directly by recursion. -/
private def ratPolyPow (d : DensePoly Rat) : Nat → DensePoly Rat
  | 0 => 1
  | n + 1 => d * ratPolyPow d n

@[simp, grind =] private theorem ratPolyPow_zero (d : DensePoly Rat) :
    ratPolyPow d 0 = 1 := rfl

@[simp, grind =] private theorem ratPolyPow_succ (d : DensePoly Rat) (n : Nat) :
    ratPolyPow d (n + 1) = d * ratPolyPow d n := rfl

private theorem ratPolyPow_one (d : DensePoly Rat) :
    ratPolyPow d 1 = d := by
  show d * ratPolyPow d 0 = d
  show d * (1 : DensePoly Rat) = d
  exact DensePoly.mul_one_right_poly d

private theorem ratPolyPow_size_lower_of_nonconstant
    (d : DensePoly Rat) (hd : 1 < d.size) :
    ∀ m : Nat, m + 2 ≤ (ratPolyPow d (m + 1)).size := by
  intro m
  induction m with
  | zero =>
      rw [ratPolyPow_one]
      omega
  | succ k ih =>
      show k + 3 ≤ (d * ratPolyPow d (k + 1)).size
      have hpow_pos : 0 < (ratPolyPow d (k + 1)).size := by omega
      have htop := rat_product_size_gt_top d (ratPolyPow d (k + 1)) (by omega) hpow_pos
      omega

/-- Cofactor extension to powers: if `d ∣ a * d'` then
`ratPolyPow d (m + 1) ∣ a * derivative (ratPolyPow d (m + 1))`. -/
private theorem ratPolyPow_succ_dvd_a_mul_derivative
    {d a : DensePoly Rat}
    (h : d ∣ a * DensePoly.derivative d) (m : Nat) :
    ratPolyPow d (m + 1) ∣
      a * DensePoly.derivative (ratPolyPow d (m + 1)) := by
  induction m with
  | zero =>
    rw [ratPolyPow_one]
    exact h
  | succ k ih =>
    show d * ratPolyPow d (k + 1) ∣
      a * DensePoly.derivative (d * ratPolyPow d (k + 1))
    rw [rat_derivative_mul, DensePoly.mul_add_right_poly]
    apply rat_dvd_add
    · rcases h with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← DensePoly.mul_assoc_poly, hc, DensePoly.mul_assoc_poly d c (ratPolyPow d (k + 1)),
        DensePoly.mul_comm_poly c (ratPolyPow d (k + 1)), ← DensePoly.mul_assoc_poly]
    · rcases ih with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly a d, DensePoly.mul_assoc_poly, hc,
        ← DensePoly.mul_assoc_poly]

/-- Iterated power-divisibility: if `d` divides both the square-free quotient
and its derivative, then every power `d^(n+1)` divides the repeated factor. -/
private theorem rat_pow_dvd_repeated_of_quotient_common_divisor
    (ratPrimitive d : DensePoly Rat) :
    let derivative := DensePoly.derivative ratPrimitive
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    d ∣ quotientRat →
    d ∣ DensePoly.derivative quotientRat →
    ∀ n : Nat, ratPolyPow d (n + 1) ∣ repeatedRat := by
  intro derivative repeatedRat quotientRat hdq hdq'
  rcases hdq with ⟨a, ha⟩
  have hcofactor : d ∣ a * DensePoly.derivative d := by
    apply rat_dvd_cofactor_derivative d a
    rw [← ha]
    exact hdq'
  have hrec : quotientRat * repeatedRat = ratPrimitive := by
    simpa [quotientRat, repeatedRat, derivative] using
      rat_div_gcd_mul_reconstruct ratPrimitive derivative
  intro n
  induction n with
  | zero =>
    show d * ratPolyPow d 0 ∣ repeatedRat
    show d * (1 : DensePoly Rat) ∣ repeatedRat
    rw [DensePoly.mul_one_right_poly]
    exact rat_common_divisor_quotient_derivative_dvd_repeated ratPrimitive d
      ⟨a, ha⟩ hdq'
  | succ k ih =>
    show d * ratPolyPow d (k + 1) ∣ repeatedRat
    rcases ih with ⟨Q, hQ⟩
    apply DensePoly.dvd_gcd
    · refine ⟨a * Q, ?_⟩
      have h1 : ratPrimitive = quotientRat * repeatedRat := hrec.symm
      rw [h1, ha, hQ, DensePoly.mul_assoc_poly d a (ratPolyPow d (k + 1) * Q),
        ← DensePoly.mul_assoc_poly a (ratPolyPow d (k + 1)) Q,
        DensePoly.mul_comm_poly a (ratPolyPow d (k + 1)),
        DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) a Q,
        ← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1)) (a * Q)]
    · have hd_eq : derivative =
          DensePoly.derivative quotientRat * repeatedRat +
            quotientRat * DensePoly.derivative repeatedRat := by
        show DensePoly.derivative ratPrimitive =
          DensePoly.derivative quotientRat * repeatedRat +
            quotientRat * DensePoly.derivative repeatedRat
        rw [← hrec]
        exact rat_derivative_mul quotientRat repeatedRat
      rw [hd_eq]
      apply rat_dvd_add
      · rcases hdq' with ⟨a', ha'⟩
        refine ⟨a' * Q, ?_⟩
        rw [ha', hQ, DensePoly.mul_assoc_poly d a' (ratPolyPow d (k + 1) * Q),
          ← DensePoly.mul_assoc_poly a' (ratPolyPow d (k + 1)) Q,
          DensePoly.mul_comm_poly a' (ratPolyPow d (k + 1)),
          DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) a' Q,
          ← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1)) (a' * Q)]
      · rw [ha, hQ]
        rw [rat_derivative_mul, DensePoly.mul_add_right_poly]
        apply rat_dvd_add
        · have haux := ratPolyPow_succ_dvd_a_mul_derivative hcofactor k
          rcases haux with ⟨c, hc⟩
          refine ⟨c * Q, ?_⟩
          rw [DensePoly.mul_assoc_poly d a
            (DensePoly.derivative (ratPolyPow d (k + 1)) * Q)]
          rw [← DensePoly.mul_assoc_poly a
            (DensePoly.derivative (ratPolyPow d (k + 1))) Q]
          rw [hc, DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) c Q,
            ← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1)) (c * Q)]
        · refine ⟨a * DensePoly.derivative Q, ?_⟩
          rw [DensePoly.mul_assoc_poly d a
            (ratPolyPow d (k + 1) * DensePoly.derivative Q)]
          rw [← DensePoly.mul_assoc_poly a (ratPolyPow d (k + 1))
            (DensePoly.derivative Q)]
          rw [DensePoly.mul_comm_poly a (ratPolyPow d (k + 1))]
          rw [DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) a
            (DensePoly.derivative Q)]
          rw [← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1))
            (a * DensePoly.derivative Q)]

private theorem rat_div_eq_zero_of_right_size_zero
    (p q : DensePoly Rat) (hq : q.size = 0) :
    p / q = 0 := by
  change DensePoly.div p q = 0
  simpa [DensePoly.div] using
    congrArg Prod.fst (DensePoly.divMod_eq_zero_self_of_size_zero_core p q hq)

private theorem rat_quotient_derivative_squareFree
    (ratPrimitive : DensePoly Rat) :
    let derivative := DensePoly.derivative ratPrimitive
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    (DensePoly.gcd quotientRat (DensePoly.derivative quotientRat)).size ≤ 1 := by
  intro derivative repeatedRat quotientRat
  let d := DensePoly.gcd quotientRat (DensePoly.derivative quotientRat)
  by_cases hdle : d.size ≤ 1
  · simpa [d]
  · exfalso
    have hdgt : 1 < d.size := Nat.lt_of_not_ge hdle
    have hd_ne : d.size ≠ 0 := by omega
    have hdq : d ∣ quotientRat := by
      simpa [d] using DensePoly.gcd_dvd_left quotientRat (DensePoly.derivative quotientRat)
    have hdq' : d ∣ DensePoly.derivative quotientRat := by
      simpa [d] using DensePoly.gcd_dvd_right quotientRat (DensePoly.derivative quotientRat)
    have hpow :=
      rat_pow_dvd_repeated_of_quotient_common_divisor ratPrimitive d hdq hdq'
    by_cases hrepeated_zero : repeatedRat.size = 0
    · have hquot_zero : quotientRat = 0 := by
        simpa [quotientRat] using
          rat_div_eq_zero_of_right_size_zero ratPrimitive repeatedRat hrepeated_zero
      have hd_zero : d = 0 := by
        dsimp [d]
        rw [hquot_zero, DensePoly.derivative_zero]
        exact DensePoly.gcd_zero_zero
      have hd_size_zero : d.size = 0 := by
        rw [hd_zero]
        exact DensePoly.size_zero
      omega
    · have hpow_dvd : ratPolyPow d (repeatedRat.size + 1) ∣ repeatedRat :=
        hpow repeatedRat.size
      have hpow_ne : (ratPolyPow d (repeatedRat.size + 1)).size ≠ 0 := by
        have hlower := ratPolyPow_size_lower_of_nonconstant d hdgt repeatedRat.size
        omega
      have hpow_size_le :
          (ratPolyPow d (repeatedRat.size + 1)).size ≤ repeatedRat.size :=
        rat_size_le_of_dvd_nonzero hpow_ne hrepeated_zero hpow_dvd
      have hlower := ratPolyPow_size_lower_of_nonconstant d hdgt repeatedRat.size
      omega

private theorem densePoly_eq_zero_of_isZero_true {R : Type _} [Zero R] [DecidableEq R]
    (p : DensePoly R) (h : p.isZero = true) :
    p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : p.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using h
  rw [DensePoly.coeff_eq_zero_of_size_le p (by omega), DensePoly.coeff_zero]
  rfl

private theorem rat_coeff_succ_eq_zero_of_derivative_zero {p : DensePoly Rat}
    (hderivative : DensePoly.derivative p = 0) (n : Nat) :
    p.coeff (n + 1) = 0 := by
  have hcoeff := congrArg (fun q : DensePoly Rat => q.coeff n) hderivative
  change (DensePoly.derivative p).coeff n = (0 : DensePoly Rat).coeff n at hcoeff
  rw [rat_coeff_derivative, DensePoly.coeff_zero] at hcoeff
  have hnat : ((n + 1 : Nat) : Rat) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact (Rat.mul_eq_zero.mp hcoeff).resolve_left hnat

private theorem rat_size_le_one_of_derivative_zero (p : DensePoly Rat)
    (hderivative : DensePoly.derivative p = 0) :
    p.size ≤ 1 := by
  by_cases hle : p.size ≤ 1
  · exact hle
  · exfalso
    have hgt : 1 < p.size := Nat.lt_of_not_ge hle
    let i := p.size - 1
    have hlast_ne : p.coeff i ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size p (by omega)
    have hi : i = (p.size - 2) + 1 := by
      unfold i
      omega
    have hzero : p.coeff i = 0 := by
      rw [hi]
      exact rat_coeff_succ_eq_zero_of_derivative_zero hderivative (p.size - 2)
    exact hlast_ne hzero

private theorem size_le_one_of_toRatPoly_derivative_zero (p : ZPoly)
    (hderivative : DensePoly.derivative (toRatPoly p) = 0) :
    p.size ≤ 1 := by
  have hrat := rat_size_le_one_of_derivative_zero (toRatPoly p) hderivative
  simpa [size_toRatPoly p] using hrat

private theorem rat_derivative_size_le_pred (p : DensePoly Rat) :
    (DensePoly.derivative p).size ≤ p.size - 1 := by
  unfold DensePoly.derivative
  have hle := DensePoly.size_ofCoeffs_le
    ((List.range (p.size - 1)).map
      (fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1))).toArray
  have hlen :
      ((List.range (p.size - 1)).map
        (fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1))).toArray.size =
      p.size - 1 := by
    simp
  omega

private theorem rat_derivative_zero_of_size_le_one (p : DensePoly Rat)
    (hp : p.size ≤ 1) :
    DensePoly.derivative p = 0 := by
  have hle := rat_derivative_size_le_pred p
  apply rat_eq_zero_of_size_zero
  omega

private theorem densePoly_eq_C_coeff_zero_of_size_le_one {R : Type _} [Zero R] [DecidableEq R]
    (p : DensePoly R) (hsize : p.size ≤ 1) :
    p = DensePoly.C (p.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  cases n with
  | zero =>
      simp
  | succ n =>
      have hp_zero : p.coeff (n + 1) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le p (by omega)
      rw [hp_zero]
      rfl

private theorem size_le_one_of_degree_getD_zero {R : Type _} [Zero R] [DecidableEq R]
    (p : DensePoly R) (hdegree : p.degree?.getD 0 = 0) :
    p.size ≤ 1 := by
  unfold DensePoly.degree? at hdegree
  by_cases hzero : p.size = 0
  · omega
  · simp [hzero] at hdegree
    omega

private theorem content_C_int (c : Int) :
    content (DensePoly.C c) = Int.ofNat c.natAbs :=
  DensePoly.content_C c

private theorem int_scale_zero (p : ZPoly) :
    DensePoly.scale (0 : Int) p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) (0 : Int) p n (Int.zero_mul 0), DensePoly.coeff_zero]
  exact Int.zero_mul (p.coeff n)

private theorem content_ne_zero_of_ne_zero (p : ZPoly) (hp : p ≠ 0) :
    content p ≠ 0 := by
  intro hcontent
  apply hp
  have hpart_zero : primitivePart p = 0 := by
    simpa [primitivePart] using
      DensePoly.primitivePart_eq_zero_of_content_eq_zero p
        (by simpa [content] using hcontent)
  have hreconstruct := content_mul_primitivePart p
  rw [hcontent, hpart_zero, int_scale_zero] at hreconstruct
  exact hreconstruct.symm


end ZPoly
end Hex
