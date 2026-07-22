/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly

public section
set_option backward.proofsInPublic true

/-!
Core `ZPoly` (integer dense polynomial) definitions: the `ZPoly`
abbreviation and law instances, the congruence predicate, content /
primitive part / `toRatPoly`, the decomposition definitions, content
multiplicativity, and integer degree/divMod arithmetic.
-/
namespace Hex
/-- Integer polynomials represented by the dense normalized coefficient type
from `HexPoly`. -/
abbrev ZPoly := DensePoly Int

/-- `ZPoly` is a multiplicative monoid for `Std`, so the shared
`List.foldl_mul_*` algebra and core's `List.foldl_assoc` apply to fold-products
of integer polynomials. -/
instance : Std.Associative (· * · : ZPoly → ZPoly → ZPoly) :=
  ⟨DensePoly.mul_assoc_poly⟩

instance : Std.LawfulIdentity (· * · : ZPoly → ZPoly → ZPoly) 1 where
  left_id p := (DensePoly.mul_comm_poly 1 p).trans (DensePoly.mul_one_right_poly p)
  right_id := DensePoly.mul_one_right_poly

instance : DensePoly.AddZeroLaw Int where
  add_zero_zero := rfl

instance : DensePoly.SubZeroLaw Int where
  sub_zero_zero := rfl

instance : DensePoly.ZeroSubNegLaw Int where
  zero_sub_eq_neg := by
    intro a
    exact Int.zero_sub a

instance : DensePoly.AddZeroLaw Rat where
  add_zero_zero := by grind

instance : DensePoly.SubZeroLaw Rat where
  sub_zero_zero := by grind

instance : DensePoly.ZeroSubNegLaw Rat where
  zero_sub_eq_neg := by intro a; grind

namespace ZPoly

/-- Coefficientwise congruence modulo `m`. -/
@[expose]
def congr (f g : ZPoly) (m : Nat) : Prop :=
  ∀ i, (f.coeff i - g.coeff i) % (m : Int) = 0

/-- Two integer polynomials are coprime mod `p` when they admit a Bezout
combination congruent to `1` modulo `p`. -/
@[expose]
def coprimeModP (f g : ZPoly) (p : Nat) : Prop :=
  ∃ s t : ZPoly, congr (s * f + t * g) 1 p

/-- The nonnegative gcd of the coefficients of `f`. -/
@[expose]
def content (f : ZPoly) : Int :=
  DensePoly.content f

/-- Divide every coefficient by the content to obtain a primitive polynomial. -/
@[expose]
def primitivePart (f : ZPoly) : ZPoly :=
  DensePoly.primitivePart f

/-- Substitute the variable `X ↦ c * X`: the `i`-th coefficient is multiplied by
`c ^ i`.

On a monic transform `c^(d-1) · core(X / c)` (the polynomial built by
`toMonic`), this is the inverse of the integer-scaling substitution: it maps a
monic factor `g` of the transform to `g(c · X)`, an integer multiple of the
corresponding factor of `core`. Composing with `primitivePart` recovers the
primitive integer factor of `core`. This is *not* the same as `DensePoly.scale`,
which multiplies the whole polynomial by a constant. -/
@[expose]
def dilate (c : Int) (p : ZPoly) : ZPoly :=
  DensePoly.ofCoeffs <| ((List.range p.size).map fun i => c ^ i * p.coeff i).toArray

/-- The `n`-th coefficient of `dilate c p` is `c ^ n` times the `n`-th
coefficient of `p`. -/
theorem coeff_dilate (c : Int) (p : ZPoly) (n : Nat) :
    (dilate c p).coeff n = c ^ n * p.coeff n := by
  unfold dilate
  rw [DensePoly.coeff_ofCoeffs_list, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hn : n < p.size
  · rw [List.getElem?_range hn]; rfl
  · have hzero : p.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_lt hn)
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn), hzero, Int.mul_zero]
    rfl

/-- Dilation by `1` is the identity: `dilate 1 p = p`. The simp normal form for
the trivial dilation. -/
@[simp, grind =] theorem dilate_one (p : ZPoly) : dilate 1 p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_dilate, Int.one_pow, Int.one_mul]

/-- A `ZPoly` is primitive when its content is `1`. -/
@[expose]
def Primitive (f : ZPoly) : Prop :=
  content f = 1

/-- A `ZPoly` is a unit iff it is the constant polynomial `1` or `-1`. -/
@[expose]
def IsUnit (f : ZPoly) : Prop :=
  f = DensePoly.C 1 ∨ f = DensePoly.C (-1)

/-- `IsUnit` is decidable: it reduces to equality with the constant polynomials
`C 1` or `C (-1)`, both of which are decidable. -/
instance instDecidableIsUnit (f : ZPoly) : Decidable (IsUnit f) := by
  unfold IsUnit
  infer_instance

/-- The `IsUnit` predicate is exactly equality with the constant polynomial `1`
or the constant polynomial `-1`. -/
theorem isUnit_iff (f : ZPoly) :
    IsUnit f ↔ f = DensePoly.C 1 ∨ f = DensePoly.C (-1) := by
  rfl

/-- The polynomial `1` is a unit, since `(1 : ZPoly)` is the constant polynomial
`C 1`. -/
@[simp, grind .] theorem isUnit_one : IsUnit (1 : ZPoly) := by
  left
  rfl

/-- The constant polynomial `C 1` is a unit. -/
@[simp, grind .] theorem isUnit_C_one : IsUnit (DensePoly.C (1 : Int)) := by
  left
  rfl

/-- The constant polynomial `C (-1)` is a unit. -/
@[simp, grind .] theorem isUnit_C_neg_one : IsUnit (DensePoly.C (-1 : Int)) := by
  right
  rfl

/-- Equality to `1` is the common constructor form for `IsUnit`. -/
theorem isUnit_of_eq_one {f : ZPoly} (h : f = 1) : IsUnit f := by
  grind

/-- Equality to `-1` is the common constructor form for `IsUnit`. -/
theorem isUnit_of_eq_neg_one {f : ZPoly} (h : f = -1) : IsUnit f := by
  rw [h]
  right
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_neg_ring]
  change -((DensePoly.C (1 : Int)).coeff n) = (DensePoly.C (-1 : Int)).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    change -(0 : Int) = 0
    exact Int.neg_zero

/-- The polynomial `-1` is a unit. -/
@[simp, grind .] theorem isUnit_neg_one : IsUnit (-1 : ZPoly) :=
  isUnit_of_eq_neg_one rfl

/-- View an integer polynomial as a rational polynomial. -/
def toRatPoly (f : ZPoly) : DensePoly Rat :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff : Int => (coeff : Rat)

/-- Coefficients of `toRatPoly f` are the rational casts of the coefficients of
`f`. -/
@[simp, grind =]
theorem coeff_toRatPoly (f : ZPoly) (n : Nat) :
    (toRatPoly f).coeff n = (f.coeff n : Rat) := by
  unfold toRatPoly
  rw [DensePoly.coeff_ofCoeffs]
  unfold DensePoly.coeff DensePoly.toArray
  by_cases hn : n < f.coeffs.size
  · simp [Array.getD, hn]
  · simp [Array.getD, hn]
    change (0 : Rat) = ((0 : Int) : Rat)
    simp

/-- Rational conversion sends the zero integer polynomial to the zero rational
polynomial. The simp normal form for the zero case. -/
@[simp, grind =] theorem toRatPoly_zero :
    toRatPoly (0 : ZPoly) = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  change ((0 : ZPoly).coeff n : Rat) = (0 : DensePoly Rat).coeff n
  rw [DensePoly.coeff_eq_zero_of_size_le (0 : ZPoly) (by simp)]
  exact (DensePoly.coeff_eq_zero_of_size_le (0 : DensePoly Rat) (by simp)).symm

/-- Rational conversion sends the constant integer polynomial `C c` to the
constant rational polynomial `C (c : Rat)`. The simp normal form for the
constant case. -/
@[simp, grind =] theorem toRatPoly_C (c : Int) :
    toRatPoly (DensePoly.C c) = DensePoly.C (c : Rat) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    change ((0 : Int) : Rat) = 0
    simp

/-- Rational conversion sends the unit integer polynomial `1` to the rational
polynomial `1`, since `(1 : ZPoly)` is the constant polynomial `C 1`. The simp
normal form for the one case. -/
@[simp, grind =] theorem toRatPoly_one :
    toRatPoly (1 : ZPoly) = 1 := by
  exact toRatPoly_C 1

/-- Rational conversion commutes with scaling an integer polynomial by an
integer. -/
@[grind =]
theorem toRatPoly_scale_int (c : Int) (f : ZPoly) :
    toRatPoly (DensePoly.scale c f) = DensePoly.scale (c : Rat) (toRatPoly f) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_scale (R := Int) c f n (Int.mul_zero c)]
  rw [DensePoly.coeff_scale (R := Rat) (c : Rat) (toRatPoly f) n (by
    exact Rat.mul_zero (c : Rat))]
  rw [coeff_toRatPoly]
  simp

/-- Rational conversion preserves the dense size of an integer polynomial. -/
@[grind =]
theorem size_toRatPoly (f : ZPoly) :
    (toRatPoly f).size = f.size := by
  apply Nat.le_antisymm
  · by_cases hle : (toRatPoly f).size ≤ f.size
    · exact hle
    · have hlt : f.size < (toRatPoly f).size := Nat.lt_of_not_ge hle
      let i := (toRatPoly f).size - 1
      have hrat_ne : (toRatPoly f).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (toRatPoly f) (by omega)
      have hf_zero : f.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f (by
          unfold i
          omega)
      exfalso
      apply hrat_ne
      rw [coeff_toRatPoly, hf_zero]
      rfl
  · by_cases hle : f.size ≤ (toRatPoly f).size
    · exact hle
    · have hlt : (toRatPoly f).size < f.size := Nat.lt_of_not_ge hle
      let i := f.size - 1
      have hf_ne : f.coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
      have hrat_zero : (toRatPoly f).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (toRatPoly f) (by
          unfold i
          omega)
      exfalso
      apply hf_ne
      have hcast_zero : ((f.coeff i : Int) : Rat) = 0 := by
        rw [← coeff_toRatPoly f i]
        exact hrat_zero
      exact Rat.intCast_eq_zero_iff.mp hcast_zero

/-- A nonzero integer polynomial remains nonzero after coefficientwise rational
casting. -/
theorem toRatPoly_ne_zero_of_ne_zero (f : ZPoly) (hf : f ≠ 0) :
    toRatPoly f ≠ 0 := by
  intro hrat
  apply hf
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_zero]
  have hsize : f.size = 0 := by
    have hrat_size : (toRatPoly f).size = 0 := by
      rw [hrat]
      exact DensePoly.size_zero
    simpa [size_toRatPoly f] using hrat_size
  exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

/-- A single `DensePoly.mulCoeffStep` of the convolution accumulator commutes with
`toRatPoly`: the rational step on the cast polynomials equals the cast of the integer step. -/
private theorem toRatPoly_mulCoeffStep (f g : ZPoly) (n i : Nat) (a : Int) (j : Nat) :
    DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i (a : Rat) j =
      (DensePoly.mulCoeffStep (R := Int) f g n i a j : Rat) := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · simp [hij, coeff_toRatPoly]
  · simp [hij]

/-- Folding `DensePoly.mulCoeffStep` over a list of inner indices commutes with
`toRatPoly`: the rational fold equals the cast of the integer fold. -/
private theorem toRatPoly_mulCoeffStep_fold (f g : ZPoly) (n i : Nat)
    (xs : List Nat) (a : Int) :
    xs.foldl (DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i) (a : Rat) =
      ((xs.foldl (DensePoly.mulCoeffStep (R := Int) f g n i) a : Int) : Rat) := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [toRatPoly_mulCoeffStep]
      exact ih (DensePoly.mulCoeffStep (R := Int) f g n i a j)

/-- The outer convolution fold over outer indices, each running the inner `mulCoeffStep`
fold, commutes with `toRatPoly`: the rational outer fold equals the cast of the integer one. -/
private theorem toRatPoly_mulCoeffOuter_fold (f g : ZPoly) (n : Nat)
    (xs : List Nat) (a : Int) :
    xs.foldl
        (fun acc i =>
          (List.range (toRatPoly g).size).foldl
            (DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i) acc)
        (a : Rat) =
      ((xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep (R := Int) f g n i) acc)
        a : Int) : Rat) := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [size_toRatPoly g, toRatPoly_mulCoeffStep_fold]
      simpa [size_toRatPoly g] using
        ih ((List.range g.size).foldl (DensePoly.mulCoeffStep (R := Int) f g n i) a)

/-- The full convolution coefficient `DensePoly.mulCoeffSum` commutes with `toRatPoly`:
the rational sum equals the cast of the integer sum, the key step for `toRatPoly_mul`. -/
private theorem toRatPoly_mulCoeffSum (f g : ZPoly) (n : Nat) :
    DensePoly.mulCoeffSum (toRatPoly f) (toRatPoly g) n =
      (DensePoly.mulCoeffSum (R := Int) f g n : Rat) := by
  unfold DensePoly.mulCoeffSum
  rw [size_toRatPoly f]
  exact toRatPoly_mulCoeffOuter_fold f g n (List.range f.size) 0

/-- Rational conversion preserves multiplication of integer polynomials. -/
@[grind =]
theorem toRatPoly_mul (f g : ZPoly) :
    toRatPoly (f * g) = toRatPoly f * toRatPoly g := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_mul, DensePoly.coeff_mul]
  exact (toRatPoly_mulCoeffSum f g n).symm

/-- The common denominator of a list of rationals, the `Nat.lcm` of all their
denominators starting from `1`. -/
private def ratCommonDen (coeffs : List Rat) : Nat :=
  coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) 1

/-- Clear a single rational `coeff` against a common denominator `den`, returning the
integer `coeff.num * (den / coeff.den)`. -/
private def ratCoeffToIntWithDen (den : Nat) (coeff : Rat) : Int :=
  coeff.num * Int.ofNat (den / coeff.den)

/-- Negate `f` when its leading coefficient is negative, normalizing a primitive part to
have nonnegative leading sign. -/
@[expose]
def normalizePrimitiveSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

/-- If `d` divides the starting accumulator, it divides the `Nat.lcm` denominator fold over
any list of coefficients. -/
private theorem ratCommonDen_foldl_preserves_dvd (coeffs : List Rat) {d acc : Nat}
    (hacc : d ∣ acc) :
    d ∣ coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) acc := by
  induction coeffs generalizing acc with
  | nil =>
      exact hacc
  | cons coeff coeffs ih =>
      simp only [List.foldl_cons]
      exact ih (acc := Nat.lcm acc coeff.den)
        (Nat.dvd_trans hacc (Nat.dvd_lcm_left acc coeff.den))

/-- Each member coefficient's denominator `q.den` divides the `Nat.lcm` denominator fold
over `coeffs`. -/
private theorem ratCommonDen_foldl_dvd_of_mem (coeffs : List Rat) {q : Rat} {acc : Nat}
    (hq : q ∈ coeffs) :
    q.den ∣ coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) acc := by
  induction coeffs generalizing acc with
  | nil =>
      cases hq
  | cons coeff coeffs ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hq
      cases hq with
      | inl hhead =>
          subst hhead
          exact ratCommonDen_foldl_preserves_dvd coeffs (Nat.dvd_lcm_right acc q.den)
      | inr htail =>
          exact ih (acc := Nat.lcm acc coeff.den) htail

/-- The denominator of any coefficient in `coeffs` divides `ratCommonDen coeffs`. -/
private theorem ratCommonDen_dvd_of_mem (coeffs : List Rat) {q : Rat} (hq : q ∈ coeffs) :
    q.den ∣ ratCommonDen coeffs := by
  unfold ratCommonDen
  exact ratCommonDen_foldl_dvd_of_mem coeffs hq

/-- When `coeff.den ∣ den`, casting `ratCoeffToIntWithDen den coeff` back to `Rat` recovers
`(den : Rat) * coeff`. -/
private theorem ratCoeffToIntWithDen_cast (den : Nat) (coeff : Rat)
    (hden : coeff.den ∣ den) :
    ((ratCoeffToIntWithDen den coeff : Int) : Rat) = (den : Rat) * coeff := by
  rcases hden with ⟨k, rfl⟩
  unfold ratCoeffToIntWithDen
  rw [Nat.mul_div_right _ coeff.den_pos]
  have hden_ne : ((coeff.den : Nat) : Rat) ≠ 0 := by
    simp [coeff.den_nz]
  have hcoeff : ((coeff.num : Rat) / (coeff.den : Rat)) = coeff := by
    simpa [Rat.divInt_eq_div, Rat.intCast_natCast] using coeff.num_divInt_den
  calc
    ((coeff.num * Int.ofNat k : Int) : Rat)
        = (coeff.num : Rat) * (k : Rat) := by
          rw [Rat.intCast_mul, Int.ofNat_eq_natCast, Rat.intCast_natCast]
    _ = ((coeff.num : Rat) * (k : Rat) * (coeff.den : Rat)) / (coeff.den : Rat) := by
          exact (Rat.mul_div_cancel hden_ne).symm
    _ = ((coeff.den * k : Nat) : Rat) * ((coeff.num : Rat) / (coeff.den : Rat)) := by
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    _ = ((coeff.den * k : Nat) : Rat) * coeff := by
          rw [hcoeff]

/-- The common denominator `ratCommonDen coeffs` is positive. -/
private theorem ratCommonDen_pos (coeffs : List Rat) :
    0 < ratCommonDen coeffs := by
  unfold ratCommonDen
  generalize hacc : 1 = acc
  have hpos : 0 < acc := by omega
  clear hacc
  induction coeffs generalizing acc with
  | nil =>
      simpa using hpos
  | cons coeff coeffs ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.lcm acc coeff.den) (Nat.lcm_pos hpos coeff.den_pos)

/-- Clearing the zero coefficient gives `0` for any denominator. -/
private theorem ratCoeffToIntWithDen_zero (den : Nat) :
    ratCoeffToIntWithDen den 0 = 0 := by
  unfold ratCoeffToIntWithDen
  simp

/-- Indexing the cleared-coefficient list commutes with clearing the indexed coefficient:
`getD` of the mapped list (cast to `Rat`) equals the clear of `getD`. -/
private theorem list_getD_map_ratCoeffToIntWithDen (den : Nat) (coeffs : List Rat)
    (n : Nat) :
    (((coeffs.map fun coeff => ratCoeffToIntWithDen den coeff).getD n 0 : Int) : Rat) =
      ((ratCoeffToIntWithDen den (coeffs.getD n 0) : Int) : Rat) := by
  induction coeffs generalizing n with
  | nil =>
      simp [ratCoeffToIntWithDen_zero]
  | cons coeff coeffs ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa using ih n

/-- Indexing `f`'s coefficient array as a list with default `0` agrees with
`DensePoly.coeff`. -/
private theorem list_getD_toArray_eq_coeff (f : DensePoly Rat) (n : Nat) :
    f.toArray.toList.getD n 0 = f.coeff n := by
  unfold DensePoly.toArray DensePoly.coeff Array.getD
  by_cases hn : n < f.coeffs.size
  · simp [hn, Array.getElem_toList]
  · simp [hn]
    rfl

/-- Every coefficient denominator of `f` divides the common denominator of `f`'s coefficient
list, including out-of-range indices where the coefficient is `0`. -/
private theorem ratCommonDen_dvd_coeff (f : DensePoly Rat) (n : Nat) :
    (f.coeff n).den ∣ ratCommonDen f.toArray.toList := by
  by_cases hn : n < f.size
  · apply ratCommonDen_dvd_of_mem
    unfold DensePoly.coeff DensePoly.toArray Array.getD
    simp [show n < f.coeffs.size by simpa [DensePoly.size] using hn]
  · have hcoeff : f.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn)
    rw [hcoeff]
    exact Nat.one_dvd _

/-- Clear every coefficient of the rational polynomial `f` against its common denominator
`ratCommonDen`, producing the integer polynomial that is `f` scaled into `ℤ`. -/
private def ratPolyPrimitivePartCleared (f : DensePoly Rat) : ZPoly :=
  let den := ratCommonDen f.toArray.toList
  DensePoly.ofCoeffs <|
    f.toArray.toList.map (fun coeff => ratCoeffToIntWithDen den coeff) |>.toArray

/-- Casting the cleared integer polynomial back to `Rat` recovers `f` scaled by its common
denominator, certifying `ratPolyPrimitivePartCleared` only rescales `f`. -/
private theorem toRatPoly_ratPolyPrimitivePartCleared (f : DensePoly Rat) :
    toRatPoly (ratPolyPrimitivePartCleared f) =
      DensePoly.scale (ratCommonDen f.toArray.toList : Rat) f := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  unfold ratPolyPrimitivePartCleared
  rw [DensePoly.coeff_ofCoeffs_list]
  change (((f.toArray.toList.map
      (fun coeff => ratCoeffToIntWithDen (ratCommonDen f.toArray.toList) coeff)).getD n
        (0 : Int) : Int) : Rat) =
    (DensePoly.scale (ratCommonDen f.toArray.toList : Rat) f).coeff n
  rw [list_getD_map_ratCoeffToIntWithDen]
  rw [DensePoly.coeff_scale (R := Rat) (ratCommonDen f.toArray.toList : Rat) f n
    (Rat.mul_zero _)]
  rw [list_getD_toArray_eq_coeff]
  exact ratCoeffToIntWithDen_cast (ratCommonDen f.toArray.toList) (f.coeff n)
    (ratCommonDen_dvd_coeff f n)

private theorem rat_scale_div_of_scale_eq {c d : Rat} (hd : d ≠ 0)
    {p q : DensePoly Rat}
    (h : DensePoly.scale c p = DensePoly.scale d q) :
    q = DensePoly.scale (c / d) p := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun r : DensePoly Rat => r.coeff n) h
  change (DensePoly.scale c p).coeff n = (DensePoly.scale d q).coeff n at hcoeff
  rw [DensePoly.coeff_scale (R := Rat) c p n (Rat.mul_zero c)] at hcoeff
  rw [DensePoly.coeff_scale (R := Rat) d q n (Rat.mul_zero d)] at hcoeff
  rw [DensePoly.coeff_scale (R := Rat) (c / d) p n (Rat.mul_zero (c / d))]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

private theorem rat_scale_toRatPoly_neg_int (u : Rat) (p : ZPoly) :
    DensePoly.scale u (toRatPoly p) =
      DensePoly.scale (-u) (toRatPoly (DensePoly.scale (-1 : Int) p)) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) u (toRatPoly p) n (Rat.mul_zero u), toRatPoly_scale_int]
  change u * (toRatPoly p).coeff n =
    (DensePoly.scale (-u) (DensePoly.scale (-1 : Rat) (toRatPoly p))).coeff n
  rw [DensePoly.coeff_scale (R := Rat) (-u)
    (DensePoly.scale (-1 : Rat) (toRatPoly p)) n (Rat.mul_zero (-u))]
  rw [DensePoly.coeff_scale (R := Rat) (-1 : Rat) (toRatPoly p) n (Rat.mul_zero (-1 : Rat))]
  grind

/--
Clear denominators in a rational polynomial and return the primitive integer
representative of the resulting rational associate.
-/
def ratPolyPrimitivePart (f : DensePoly Rat) : ZPoly :=
  normalizePrimitiveSign (primitivePart (ratPolyPrimitivePartCleared f))

private theorem ratPolyPrimitivePart_rational_associate_core (f : DensePoly Rat) :
    ∃ unit : Rat, f = DensePoly.scale unit (toRatPoly (ratPolyPrimitivePart f)) := by
  let den := ratCommonDen f.toArray.toList
  let scaled := ratPolyPrimitivePartCleared f
  have hden_ne : (den : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (ratCommonDen_pos f.toArray.toList))
  have hcleared : toRatPoly scaled = DensePoly.scale (den : Rat) f := by
    simpa [den, scaled] using toRatPoly_ratPolyPrimitivePartCleared f
  have hreconstruct :
      DensePoly.scale ((content scaled : Int) : Rat) (toRatPoly (primitivePart scaled)) =
        DensePoly.scale (den : Rat) f := by
    rw [← toRatPoly_scale_int (content scaled) (primitivePart scaled)]
    change toRatPoly (DensePoly.scale (DensePoly.content scaled) (DensePoly.primitivePart scaled)) =
      DensePoly.scale (den : Rat) f
    rw [DensePoly.content_mul_primitivePart]
    exact hcleared
  have hbase :
      f = DensePoly.scale (((content scaled : Int) : Rat) / (den : Rat))
        (toRatPoly (primitivePart scaled)) := by
    exact rat_scale_div_of_scale_eq hden_ne hreconstruct
  by_cases hlead : DensePoly.leadingCoeff (primitivePart scaled) < 0
  · refine ⟨-(((content scaled : Int) : Rat) / (den : Rat)), ?_⟩
    rw [ratPolyPrimitivePart]
    change f =
      DensePoly.scale (-(((content scaled : Int) : Rat) / (den : Rat)))
        (toRatPoly (normalizePrimitiveSign (primitivePart scaled)))
    rw [normalizePrimitiveSign, if_pos hlead]
    rw [← rat_scale_toRatPoly_neg_int (((content scaled : Int) : Rat) / (den : Rat))
      (primitivePart scaled)]
    exact hbase
  · refine ⟨(((content scaled : Int) : Rat) / (den : Rat)), ?_⟩
    rw [ratPolyPrimitivePart]
    change f =
      DensePoly.scale (((content scaled : Int) : Rat) / (den : Rat))
        (toRatPoly (normalizePrimitiveSign (primitivePart scaled)))
    rw [normalizePrimitiveSign, if_neg hlead]
    exact hbase

/--
Executable primitive square-free decomposition data for integer-polynomial
normalization.

`primitive` is the content-free input. `squareFreeCore` is computed over
`Rat[x]` as `primitive / gcd(primitive, primitive')`, then converted back to a
primitive integer representative. `repeatedPart` records the same rational gcd,
also converted to a primitive integer representative. The proof layer relates
these representatives back to the primitive input up to a rational unit.
-/
structure PrimitiveSquareFreeDecomposition where
  primitive : ZPoly
  squareFreeCore : ZPoly
  repeatedPart : ZPoly

/-- Square-free over `Rat[x]`, up to the executable rational gcd's unit factor. -/
@[expose]
def SquareFreeRat (f : ZPoly) : Prop :=
  (DensePoly.gcd (toRatPoly f) (DensePoly.derivative (toRatPoly f))).size ≤ 1

/-- `SquareFreeRat` is by definition a `Nat` size inequality on the executable
rational gcd, so `Nat.decLe` decides it. Drivers branch on this instance for
the SPEC's admissibility test. -/
instance (f : ZPoly) : Decidable (SquareFreeRat f) :=
  inferInstanceAs (Decidable (_ ≤ 1))

/--
Compute the primitive square-free normalization data needed by the integer
factorization pipeline.
-/
@[expose]
def primitiveSquareFreeDecomposition (f : ZPoly) : PrimitiveSquareFreeDecomposition :=
  let primitive := primitivePart f
  if primitive.isZero then
    { primitive, squareFreeCore := 0, repeatedPart := 0 }
  else
    let ratPrimitive := toRatPoly primitive
    let derivative := DensePoly.derivative ratPrimitive
    if derivative.isZero then
      { primitive, squareFreeCore := normalizePrimitiveSign primitive, repeatedPart := 1 }
    else
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      { primitive
        squareFreeCore := ratPolyPrimitivePart (ratPrimitive / repeatedRat)
        repeatedPart := ratPolyPrimitivePart repeatedRat }

/-- The square-free core projection of `primitiveSquareFreeDecomposition`. -/
@[expose]
def squareFreeCore (f : ZPoly) : ZPoly :=
  (primitiveSquareFreeDecomposition f).squareFreeCore

/-- Coefficientwise congruence modulo `m` is reflexive. -/
theorem congr_refl (f : ZPoly) (m : Nat) : congr f f m := by
  intro i
  simp

/-- Coefficientwise congruence modulo `m` is symmetric. -/
theorem congr_symm (f g : ZPoly) (m : Nat) (hfg : congr f g m) : congr g f m := by
  intro i
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hfg i) with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  grind

/-- Coefficientwise congruence modulo `m` is transitive. -/
theorem congr_trans (f g h : ZPoly) (m : Nat) (hfg : congr f g m) (hgh : congr g h m) :
    congr f h m := by
  intro i
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hfg i) with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero (hgh i) with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  grind

/-- Addition preserves coefficientwise congruence modulo `m` in both inputs. -/
theorem congr_add (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) :
    congr (f + g) (f' + g') m := by
  intro i
  rw [DensePoly.coeff_add (R := Int) (hzero := by rfl),
    DensePoly.coeff_add (R := Int) (hzero := by rfl)]
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hf i) with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero (hg i) with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  grind

/-- `m` divides the product difference `a * c - b * d` whenever it divides each
factor difference `a - b` and `c - d`. -/
private theorem dvd_mul_sub_mul_of_dvd_sub (m a b c d : Int)
    (hab : m ∣ a - b) (hcd : m ∣ c - d) :
    m ∣ a * c - b * d := by
  rcases hab with ⟨u, hu⟩
  rcases hcd with ⟨v, hv⟩
  refine ⟨u * c + b * v, ?_⟩
  grind

/-- `m` divides the difference between corresponding `DensePoly.mulCoeffStep`
updates of congruent inputs, given accumulators that already differ by a
multiple of `m`. -/
private theorem dvd_mulCoeffStep_sub (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) (n i j : Nat) (a b : Int)
    (hab : (m : Int) ∣ a - b) :
    (m : Int) ∣
      DensePoly.mulCoeffStep f g n i a j -
        DensePoly.mulCoeffStep f' g' n i b j := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · simp [hij]
    have hprod : (m : Int) ∣ f.coeff i * g.coeff j - f'.coeff i * g'.coeff j :=
      dvd_mul_sub_mul_of_dvd_sub (m : Int) (f.coeff i) (f'.coeff i) (g.coeff j)
        (g'.coeff j) (Int.dvd_of_emod_eq_zero (hf i)) (Int.dvd_of_emod_eq_zero (hg j))
    rcases hab with ⟨u, hu⟩
    rcases hprod with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    grind
  · simp [hij]
    exact hab

/-- `m` divides the difference between the `DensePoly.mulCoeffStep` inner folds
over `xs` for congruent inputs, propagating the accumulator congruence. -/
private theorem dvd_mulCoeffStep_fold_sub (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) (n i : Nat) (xs : List Nat) (a b : Int)
    (hab : (m : Int) ∣ a - b) :
    (m : Int) ∣
      xs.foldl (DensePoly.mulCoeffStep f g n i) a -
        xs.foldl (DensePoly.mulCoeffStep f' g' n i) b := by
  induction xs generalizing a b with
  | nil =>
      simpa using hab
  | cons j xs ih =>
      simp only [List.foldl_cons]
      exact ih (DensePoly.mulCoeffStep f g n i a j)
        (DensePoly.mulCoeffStep f' g' n i b j)
        (dvd_mulCoeffStep_sub f g f' g' m hf hg n i j a b hab)

/-- Extending the inner `DensePoly.mulCoeffStep` fold past `q.size` adds nothing,
since the extra `q` coefficients vanish. -/
private theorem fold_mulCoeffStep_range_add_zero_tail (p q : ZPoly)
    (n i : Nat) (a : Int) (d : Nat) :
    (List.range (q.size + d)).foldl (DensePoly.mulCoeffStep p q n i) a =
      (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a := by
  induction d with
  | zero =>
      rfl
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      have hcoeff : q.coeff (q.size + d) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le q (by omega)
      by_cases h : i + (q.size + d) = n
      · simp [h, hcoeff]
      · simp [h]

/-- The inner `DensePoly.mulCoeffStep` fold over any range at least `q.size`
agrees with the fold over `q.size`. -/
private theorem fold_mulCoeffStep_range_of_size_le (p q : ZPoly)
    (n i : Nat) (a : Int) {s : Nat} (hs : q.size ≤ s) :
    (List.range s).foldl (DensePoly.mulCoeffStep p q n i) a =
      (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a := by
  have hs' : q.size + (s - q.size) = s := by omega
  rw [← hs']
  exact fold_mulCoeffStep_range_add_zero_tail p q n i a (s - q.size)

/-- When `p.coeff i = 0`, the inner `DensePoly.mulCoeffStep` fold over `q.size`
leaves the accumulator unchanged. -/
private theorem fold_mulCoeffStep_zero_left (p q : ZPoly) (n i : Nat) (a : Int)
    (hi : p.coeff i = 0) :
    (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a = a := by
  induction q.size generalizing a with
  | zero =>
      rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases h : i + k = n
      · simp [h, hi]
      · simp [h]

/-- Extending the outer `DensePoly.mulCoeffStep` fold past `p.size` adds nothing,
since the extra `p` coefficients vanish. -/
private theorem fold_mulCoeffOuter_range_add_zero_tail (p q : ZPoly)
    (n d : Nat) :
    (List.range (p.size + d)).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 =
      (List.range p.size).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 := by
  induction d with
  | zero =>
      rfl
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hcoeff : p.coeff (p.size + d) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le p (by omega)
      exact fold_mulCoeffStep_zero_left p q n (p.size + d)
        ((List.range p.size).foldl
          (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0)
        hcoeff

/-- The outer `DensePoly.mulCoeffStep` fold over any range at least `p.size`
computes `DensePoly.mulCoeffSum p q n`. -/
private theorem mulCoeffSum_eq_outer_range_of_size_le (p q : ZPoly)
    (n : Nat) {s : Nat} (hs : p.size ≤ s) :
    (List.range s).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 =
      DensePoly.mulCoeffSum p q n := by
  unfold DensePoly.mulCoeffSum
  have hs' : p.size + (s - p.size) = s := by omega
  rw [← hs']
  exact fold_mulCoeffOuter_range_add_zero_tail p q n (s - p.size)

/-- `m` divides the difference between the outer `DensePoly.mulCoeffStep` folds
over `xs` for congruent inputs, propagating the accumulator congruence through
each inner fold. -/
private theorem dvd_mulCoeffOuter_fold_sub (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) (n innerBound : Nat)
    (hgb : g.size ≤ innerBound) (hg'b : g'.size ≤ innerBound)
    (xs : List Nat) (a b : Int) (hab : (m : Int) ∣ a - b) :
    (m : Int) ∣
      xs.foldl
          (fun acc i => (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc) a -
        xs.foldl
          (fun acc i => (List.range g'.size).foldl (DensePoly.mulCoeffStep f' g' n i) acc) b := by
  induction xs generalizing a b with
  | nil =>
      simpa using hab
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hnext : (m : Int) ∣
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) a -
            (List.range g'.size).foldl (DensePoly.mulCoeffStep f' g' n i) b := by
        rw [← fold_mulCoeffStep_range_of_size_le f g n i a hgb,
          ← fold_mulCoeffStep_range_of_size_le f' g' n i b hg'b]
        exact dvd_mulCoeffStep_fold_sub f g f' g' m hf hg n i
          (List.range innerBound) a b hab
      exact ih
        ((List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) a)
        ((List.range g'.size).foldl (DensePoly.mulCoeffStep f' g' n i) b)
        hnext

/-- Multiplication preserves coefficientwise congruence modulo `m` in both
inputs. -/
theorem congr_mul (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) :
    congr (f * g) (f' * g') m := by
  intro i
  rw [DensePoly.coeff_mul, DensePoly.coeff_mul]
  apply Int.emod_eq_zero_of_dvd
  let outerBound := max f.size f'.size
  let innerBound := max g.size g'.size
  rw [← mulCoeffSum_eq_outer_range_of_size_le f g i (s := outerBound) (by
    unfold outerBound
    exact Nat.le_max_left f.size f'.size)]
  rw [← mulCoeffSum_eq_outer_range_of_size_le f' g' i (s := outerBound) (by
    unfold outerBound
    exact Nat.le_max_right f.size f'.size)]
  exact dvd_mulCoeffOuter_fold_sub f g f' g' m hf hg i innerBound
    (by
      unfold innerBound
      exact Nat.le_max_left g.size g'.size)
    (by
      unfold innerBound
      exact Nat.le_max_right g.size g'.size)
    (List.range outerBound) 0 0 (by simp)

/-- Scaling the primitive part by the content reconstructs the original integer
polynomial. -/
@[grind =]
theorem content_mul_primitivePart (f : ZPoly) :
    DensePoly.scale (content f) (primitivePart f) = f :=
  DensePoly.content_mul_primitivePart f

/-- The content of an integer polynomial divides every coefficient. -/
theorem content_dvd_coeff (f : ZPoly) (n : Nat) :
    content f ∣ f.coeff n := by
  simpa [content] using DensePoly.content_dvd_coeff f n

/-- If a natural number divides every coefficient, then its integer cast divides
the content. -/
theorem dvd_content_of_nat_dvd_coeff (f : ZPoly) (d : Nat)
    (h : ∀ n, (d : Int) ∣ f.coeff n) :
    (d : Int) ∣ content f := by
  simpa [content] using DensePoly.dvd_content_of_nat_dvd_coeff f d h

/-- Alias for `dvd_content_of_nat_dvd_coeff` with the divisibility conclusion
written for the natural number cast to `Int`. -/
theorem natCast_dvd_content_of_dvd_coeff (f : ZPoly) (d : Nat)
    (h : ∀ n, (d : Int) ∣ f.coeff n) :
    (d : Int) ∣ content f := by
  exact dvd_content_of_nat_dvd_coeff f d h

/-- If the content of `f` is nonzero, then the primitive part of `f` is
primitive. -/
theorem primitivePart_primitive (f : ZPoly) (h : content f ≠ 0) :
    Primitive (primitivePart f) := by
  simpa [Primitive, content, primitivePart] using DensePoly.primitivePart_primitive f h

/-- A primitive integer polynomial is equal to its primitive part. -/
theorem primitivePart_eq_self_of_primitive (f : ZPoly) (h : Primitive f) :
    primitivePart f = f :=
  DensePoly.primitivePart_eq_self_of_content_eq_one f (by simpa [Primitive, content] using h)

/-- The product of primitive integer polynomials is primitive. -/
theorem primitive_mul (p q : ZPoly)
    (hp : Primitive p) (hq : Primitive q) :
    Primitive (p * q) := by
  simpa [Primitive, content] using DensePoly.content_mul_of_primitive p q hp hq

/-- `ZPoly`-level wrapper for `DensePoly.content_mul`: the content of a
product of integer polynomials is the product of their contents. -/
@[grind =]
theorem content_mul (p q : ZPoly) :
    content (p * q) = content p * content q := by
  simpa [content] using DensePoly.content_mul p q

/-- `ZPoly`-level wrapper for `DensePoly.primitivePart_mul` (Gauss's lemma): the
primitive part of a product of integer polynomials is the product of their
primitive parts. -/
@[grind =]
theorem primitivePart_mul (p q : ZPoly) :
    primitivePart (p * q) = primitivePart p * primitivePart q := by
  simpa [primitivePart] using DensePoly.primitivePart_mul p q

/-- The top coefficient of a product of nonzero integer polynomials is the
product of their top coefficients. -/
theorem coeff_mul_top (p q : ZPoly)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).coeff (p.size - 1 + (q.size - 1)) =
      p.coeff (p.size - 1) * q.coeff (q.size - 1) := by
  exact DensePoly.coeff_mul_top_int p q hp hq

/-- The size of a product of nonzero integer polynomials is one less than the
sum of their sizes. -/
theorem mul_size_eq_top_succ_of_nonzero (p q : ZPoly)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).size = p.size + q.size - 1 := by
  have htop := coeff_mul_top p q hp hq
  have hp_lead_ne : p.coeff (p.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size p hp
  have hq_lead_ne : q.coeff (q.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size q hq
  have hprod_ne :
      p.coeff (p.size - 1) * q.coeff (q.size - 1) ≠ 0 := by
    intro hzero
    rcases Int.mul_eq_zero.mp hzero with h | h
    · exact hp_lead_ne h
    · exact hq_lead_ne h
  have hcoeff_ne : (p * q).coeff (p.size - 1 + (q.size - 1)) ≠ 0 := by
    rw [htop]
    exact hprod_ne
  have hlt : p.size - 1 + (q.size - 1) < (p * q).size := by
    rcases Nat.lt_or_ge (p.size - 1 + (q.size - 1)) (p * q).size with h | hle
    · exact h
    · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le (p * q) hle))
  have hle := DensePoly.size_mul_le p q
  omega

/-- A nonzero integer polynomial has positive dense size. -/
theorem size_pos_of_ne_zero (p : ZPoly) (hp : p ≠ 0) :
    0 < p.size := by
  rcases Nat.lt_or_ge 0 p.size with h | h
  · exact h
  · exfalso
    apply hp
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le p (by omega)

/-- The leading coefficient of a product of nonzero integer polynomials is the
product of their leading coefficients. -/
theorem leadingCoeff_mul_of_nonzero (p q : ZPoly)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    DensePoly.leadingCoeff (p * q) =
      DensePoly.leadingCoeff p * DensePoly.leadingCoeff q := by
  have hp_pos : 0 < p.size := size_pos_of_ne_zero p hp
  have hq_pos : 0 < q.size := size_pos_of_ne_zero q hq
  have hpq_size := mul_size_eq_top_succ_of_nonzero p q hp_pos hq_pos
  have hpq_pos : 0 < (p * q).size := by omega
  rw [DensePoly.leadingCoeff_eq_coeff_last (p * q) hpq_pos,
    DensePoly.leadingCoeff_eq_coeff_last p hp_pos, DensePoly.leadingCoeff_eq_coeff_last q hq_pos]
  have hlast : (p * q).size - 1 = p.size - 1 + (q.size - 1) := by omega
  rw [hlast]
  exact coeff_mul_top p q hp_pos hq_pos

/-- A product of integer polynomials with positive leading coefficients has
positive leading coefficient. -/
theorem leadingCoeff_mul_pos_of_pos (p q : ZPoly)
    (hp_pos : 0 < DensePoly.leadingCoeff p)
    (hq_pos : 0 < DensePoly.leadingCoeff q) :
    0 < DensePoly.leadingCoeff (p * q) := by
  have hp_ne : p ≠ 0 := by
    intro hp_zero
    rw [hp_zero] at hp_pos
    rw [DensePoly.leadingCoeff_zero] at hp_pos
    omega
  have hq_ne : q ≠ 0 := by
    intro hq_zero
    rw [hq_zero] at hq_pos
    rw [DensePoly.leadingCoeff_zero] at hq_pos
    omega
  rw [leadingCoeff_mul_of_nonzero p q hp_ne hq_ne]
  exact Int.mul_pos hp_pos hq_pos

private theorem leadingCoeff_one_pos :
    0 < DensePoly.leadingCoeff (1 : ZPoly) := by
  change 0 < DensePoly.leadingCoeff (DensePoly.C (1 : Int))
  simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Int) ≠ 0)]

private theorem fold_mulCoeffStep_C_left_range
    (c : Int) (p : ZPoly) (n m : Nat) (a : Int) :
    (List.range m).foldl (DensePoly.mulCoeffStep (DensePoly.C c) p n 0) a =
      if n < m then a + c * p.coeff n else a := by
  induction m generalizing a with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      rcases Nat.lt_trichotomy n m with hlt | heq | hgt
      · have hn_succ : n < m + 1 := by omega
        have hne : m ≠ n := by omega
        simp [hlt, hn_succ, hne]
      · subst n
        have hnot_m : ¬ m < m := by omega
        have hlt_succ : m < m + 1 := by omega
        simp [hnot_m, hlt_succ]
      · have hnot_m : ¬ n < m := by omega
        have hnot_succ : ¬ n < m + 1 := by omega
        have hne : m ≠ n := by omega
        simp [hnot_m, hnot_succ, hne]

/-- Multiplication by an integer constant agrees with coefficient scaling. -/
@[grind =]
theorem C_mul_eq_scale (c : Int) (p : ZPoly) :
    DensePoly.C c * p = DensePoly.scale c p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_mul, DensePoly.coeff_scale (R := Int) c p n (Int.mul_zero c)]
  unfold DensePoly.mulCoeffSum
  by_cases hc : c = 0
  · subst c
    have hCsize : (DensePoly.C (0 : Int)).size = 0 := by
      simp [DensePoly.size]
    rw [hCsize]
    simp
    change (0 : Int) = 0
    rfl
  · have hCsize : (DensePoly.C c).size = 1 := by
      simp [DensePoly.size, DensePoly.coeffs_C_of_ne_zero hc]
    rw [hCsize]
    simp only [List.range_one, List.foldl_cons, List.foldl_nil]
    rw [fold_mulCoeffStep_C_left_range]
    by_cases hn : n < p.size
    · rw [if_pos hn]
      change (0 : Int) + c * p.coeff n = c * p.coeff n
      omega
    · rw [if_neg hn, DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hn)]
      change (0 : Int) = c * 0
      rw [Int.mul_zero]

private theorem scale_size_of_nonzero_core {c : Int} (hc : c ≠ 0) (p : ZPoly) :
    (DensePoly.scale c p).size = p.size := by
  apply Nat.le_antisymm
  · by_cases hle : (DensePoly.scale c p).size ≤ p.size
    · exact hle
    · have hlt : p.size < (DensePoly.scale c p).size := Nat.lt_of_not_ge hle
      let i := (DensePoly.scale c p).size - 1
      have hscaled_ne : (DensePoly.scale c p).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.scale c p) (by omega)
      have hp_zero : p.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le p (by
        unfold i
        omega)
      exfalso
      apply hscaled_ne
      rw [DensePoly.coeff_scale (R := Int) c p i (Int.mul_zero c), hp_zero, Int.mul_zero]
  · by_cases hle : p.size ≤ (DensePoly.scale c p).size
    · exact hle
    · have hlt : (DensePoly.scale c p).size < p.size := Nat.lt_of_not_ge hle
      let i := p.size - 1
      have hp_ne : p.coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size p (by omega)
      have hscaled_zero : (DensePoly.scale c p).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale c p) (by
          unfold i
          omega)
      exfalso
      apply hp_ne
      have hmul_zero : c * p.coeff i = 0 := by
        rw [← DensePoly.coeff_scale (R := Int) c p i (Int.mul_zero c)]
        exact hscaled_zero
      exact (Int.mul_eq_zero.mp hmul_zero).resolve_left hc

/-- Nonzero integer scalar multiplication preserves the stored size. -/
theorem scale_size_of_nonzero (c : Int) (p : ZPoly) (hc : c ≠ 0) :
    (DensePoly.scale c p).size = p.size :=
  scale_size_of_nonzero_core (c := c) hc p

/-- Leading coefficient after nonzero integer scalar multiplication. -/
theorem leadingCoeff_scale_of_nonzero (c : Int) (p : ZPoly) (hc : c ≠ 0) :
    (DensePoly.scale c p).leadingCoeff = c * p.leadingCoeff := by
  by_cases hp : 0 < p.size
  · rw [DensePoly.leadingCoeff_eq_coeff_last (DensePoly.scale c p)]
    · rw [scale_size_of_nonzero c p hc]
      rw [DensePoly.coeff_scale (R := Int) c p (p.size - 1) (Int.mul_zero c),
        DensePoly.leadingCoeff_eq_coeff_last p hp]
    · rw [scale_size_of_nonzero c p hc]
      exact hp
  · have hpsize : p.size = 0 := by omega
    have hscaled_size : (DensePoly.scale c p).size = 0 := by
      rw [scale_size_of_nonzero c p hc, hpsize]
    have hpzero : p = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le p (by omega)
    rw [hpzero]
    simp

private theorem shift_size_of_nonzero_core (k : Nat) {p : ZPoly} (hp : p ≠ 0) :
    (DensePoly.shift k p).size = k + p.size := by
  have hpos : 0 < p.size := by
    by_cases hpos : 0 < p.size
    · exact hpos
    · exfalso
      apply hp
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le p (by omega)
  apply Nat.le_antisymm
  · by_cases hle : (DensePoly.shift k p).size ≤ k + p.size
    · exact hle
    · have hlt : k + p.size < (DensePoly.shift k p).size := Nat.lt_of_not_ge hle
      let i := (DensePoly.shift k p).size - 1
      have hshift_ne : (DensePoly.shift k p).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.shift k p) (by omega)
      have hpidx : p.size ≤ i - k := by
        unfold i
        omega
      have hcoeff : (DensePoly.shift k p).coeff i = 0 := by
        rw [DensePoly.coeff_shift]
        have hnot : ¬ i < k := by
          unfold i
          omega
        simp [hnot, DensePoly.coeff_eq_zero_of_size_le p hpidx]
        change (0 : Int) = 0
        rfl
      exact False.elim (hshift_ne hcoeff)
  · have hcoeff_ne : (DensePoly.shift k p).coeff (k + p.size - 1) ≠ 0 := by
      rw [DensePoly.coeff_shift]
      have hnot : ¬ k + p.size - 1 < k := by omega
      have hidx : k + p.size - 1 - k = p.size - 1 := by omega
      rw [if_neg hnot, hidx]
      exact DensePoly.coeff_last_ne_zero_of_pos_size p hpos
    by_cases hle : k + p.size ≤ (DensePoly.shift k p).size
    · exact hle
    · have htop : (DensePoly.shift k p).size ≤ k + p.size - 1 := by omega
      exact False.elim
        (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le (DensePoly.shift k p) htop))

/-- Shifting a nonzero polynomial by `x^k` preserves its leading coefficient. -/
theorem leadingCoeff_shift_of_nonzero (k : Nat) (p : ZPoly) (hp : p ≠ 0) :
    (DensePoly.shift k p).leadingCoeff = p.leadingCoeff := by
  have hpos : 0 < p.size := by
    by_cases hpos : 0 < p.size
    · exact hpos
    · exfalso
      apply hp
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le p (by omega)
  rw [DensePoly.leadingCoeff_eq_coeff_last (DensePoly.shift k p)]
  · rw [shift_size_of_nonzero_core k hp]
    rw [DensePoly.coeff_shift]
    have hnot : ¬ k + p.size - 1 < k := by omega
    have hidx : k + p.size - 1 - k = p.size - 1 := by omega
    rw [if_neg hnot, hidx, DensePoly.leadingCoeff_eq_coeff_last p hpos]
  · rw [shift_size_of_nonzero_core k hp]
    omega

/-- Integer dense polynomials have no zero divisors. -/
theorem mul_ne_zero_of_ne_zero (p q : ZPoly)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  exact DensePoly.mul_ne_zero_int p q hp hq

/-- Right cancellation for multiplication by a nonzero integer polynomial. -/
theorem mul_right_cancel_of_ne_zero {p q r : ZPoly}
    (hr : r ≠ 0) (h : p * r = q * r) :
    p = q := by
  apply Classical.byContradiction
  intro hpq
  have hsub_ne : p - q ≠ 0 := by
    intro hsub
    apply hpq
    apply DensePoly.ext_coeff
    intro n
    have hcoeff := congrArg (fun s : ZPoly => s.coeff n) hsub
    have hzero_sub : (0 : Int) - 0 = 0 := by omega
    change (p - q).coeff n = (0 : ZPoly).coeff n at hcoeff
    rw [DensePoly.coeff_sub p q n hzero_sub, DensePoly.coeff_zero] at hcoeff
    omega
  have hmul_ne : (p - q) * r ≠ 0 := mul_ne_zero_of_ne_zero (p - q) r hsub_ne hr
  apply hmul_ne
  rw [DensePoly.sub_eq_add_neg_poly, DensePoly.mul_add_left_poly,
    DensePoly.neg_mul_right_poly, h]
  apply DensePoly.ext_coeff
  intro n
  have hzero_add : (0 : Int) + 0 = 0 := by omega
  have hzero_sub : (0 : Int) - 0 = 0 := by omega
  rw [DensePoly.coeff_add (q * r) (0 - q * r) n hzero_add,
    DensePoly.coeff_sub 0 (q * r) n hzero_sub, DensePoly.coeff_zero]
  omega

/-- A nonzero divisor of a nonzero integer polynomial has no larger dense size. -/
theorem size_le_of_dvd_nonzero {d r : ZPoly}
    (hd : d ≠ 0) (hr : r ≠ 0) :
    d ∣ r → d.size ≤ r.size := by
  intro hdiv
  rcases hdiv with ⟨k, hk⟩
  by_cases hk_zero : k = 0
  · apply False.elim
    apply hr
    rw [hk, hk_zero, DensePoly.mul_comm_poly d (0 : ZPoly), DensePoly.zero_mul]
  · have hd_pos : 0 < d.size := by
      rcases Nat.lt_or_ge 0 d.size with h | h
      · exact h
      · exfalso
        apply hd
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_zero]
        exact DensePoly.coeff_eq_zero_of_size_le d (by omega)
    have hk_pos : 0 < k.size := by
      rcases Nat.lt_or_ge 0 k.size with h | h
      · exact h
      · exfalso
        apply hk_zero
        apply DensePoly.ext_coeff
        intro n
        rw [DensePoly.coeff_zero]
        exact DensePoly.coeff_eq_zero_of_size_le k (by omega)
    have htop := coeff_mul_top d k hd_pos hk_pos
    have hd_lead_ne := DensePoly.coeff_last_ne_zero_of_pos_size d hd_pos
    have hk_lead_ne := DensePoly.coeff_last_ne_zero_of_pos_size k hk_pos
    have hprod_ne :
        d.coeff (d.size - 1) * k.coeff (k.size - 1) ≠ 0 := by
      intro hzero
      rcases Int.mul_eq_zero.mp hzero with h | h
      · exact hd_lead_ne h
      · exact hk_lead_ne h
    have hcoeff_ne : (d * k).coeff (d.size - 1 + (k.size - 1)) ≠ 0 := by
      rw [htop]
      exact hprod_ne
    have htop_lt : d.size - 1 + (k.size - 1) < (d * k).size := by
      rcases Nat.lt_or_ge (d.size - 1 + (k.size - 1)) (d * k).size with h | hle
      · exact h
      · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le (d * k) hle))
    have hsize_eq : (d * k).size = r.size := by rw [hk]
    omega

/-- Euclidean reconstruction for a monic integer divisor: the executable
dense-polynomial division recomposes the dividend, `quot * candidate + rem =
target`, for any dividend. This is the monic specialization over `Int` of
`DensePoly.divMod_reconstruction`; the leading-coefficient cancellation
invariant it requires holds because a monic divisor has leading coefficient `1`.
Unlike `divMod_eq_of_monic_mul_eq`, no exact-multiple hypothesis is needed, so
the remainder may be nonzero. -/
theorem divMod_reconstruction_of_monic (target candidate : ZPoly)
    (hmonic : DensePoly.Monic candidate) :
    (DensePoly.divMod target candidate).1 * candidate
      + (DensePoly.divMod target candidate).2 = target := by
  have hcancel :
      ∀ a : Int, a - (a / candidate.leadingCoeff) * candidate.leadingCoeff = 0 := by
    intro a
    rw [hmonic]
    omega
  simpa using DensePoly.divMod_reconstruction target candidate hcancel

/-- If a monic positive-degree integer divisor has an exact product witness,
the executable dense-polynomial division returns zero remainder. -/
theorem divMod_remainder_eq_zero_of_monic_mul_eq
    (target candidate quotient : ZPoly)
    (hmonic : DensePoly.Monic candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    (DensePoly.divMod target candidate).2 = 0 := by
  let qr := DensePoly.divMod target candidate
  have hcancel :
      ∀ a : Int, a - (a / candidate.leadingCoeff) * candidate.leadingCoeff = 0 := by
    intro a
    rw [hmonic]
    omega
  have hrecon : qr.1 * candidate + qr.2 = target := by
    simpa [qr] using divMod_reconstruction_of_monic target candidate hmonic
  rw [← hmul] at hrecon
  have hcandidate_ne : candidate ≠ 0 := by
    intro hzero
    have hdeg : candidate.degree?.getD 0 = 0 := by
      rw [hzero]
      simp [DensePoly.degree?]
    omega
  have hrem_degree :
      qr.2.degree?.getD 0 < candidate.degree?.getD 0 := by
    simpa [qr] using
      DensePoly.divMod_remainder_degree_lt_of_pos_degree_core target candidate hdegree hcancel
  by_cases hrem_zero : qr.2 = 0
  · simpa [qr] using hrem_zero
  · have hrem_dvd : candidate ∣ qr.2 := by
      refine ⟨quotient - qr.1, ?_⟩
      rw [DensePoly.mul_comm_poly candidate (quotient - qr.1)]
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun s : ZPoly => s.coeff n) hrecon
      have hzero_add : (0 : Int) + 0 = 0 := by omega
      have hzero_sub : (0 : Int) - 0 = 0 := by omega
      change (qr.1 * candidate + qr.2).coeff n = (quotient * candidate).coeff n at hcoeff
      rw [DensePoly.coeff_add (qr.1 * candidate) qr.2 n hzero_add] at hcoeff
      rw [DensePoly.coeff_mul] at hcoeff
      rw [DensePoly.coeff_mul] at hcoeff
      rw [DensePoly.sub_eq_add_neg_poly, DensePoly.mul_add_left_poly,
        DensePoly.neg_mul_right_poly]
      rw [DensePoly.coeff_add (quotient * candidate) (0 - qr.1 * candidate) n hzero_add,
        DensePoly.coeff_sub 0 (qr.1 * candidate) n hzero_sub, DensePoly.coeff_zero,
        DensePoly.coeff_mul, DensePoly.coeff_mul]
      omega
    have hsize_le : candidate.size ≤ qr.2.size :=
      size_le_of_dvd_nonzero hcandidate_ne hrem_zero hrem_dvd
    have hcandidate_size_ne : candidate.size ≠ 0 := by
      intro hsize
      simp [DensePoly.degree?, hsize] at hdegree
    have hrem_size_ne : qr.2.size ≠ 0 := by
      intro hsize
      apply hrem_zero
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le qr.2 (by omega)
    have hcandidate_deg : candidate.degree?.getD 0 = candidate.size - 1 := by
      simp [DensePoly.degree?, hcandidate_size_ne]
    have hrem_deg : qr.2.degree?.getD 0 = qr.2.size - 1 := by
      simp [DensePoly.degree?, hrem_size_ne]
    rw [hrem_deg, hcandidate_deg] at hrem_degree
    omega

/-- If a monic positive-degree integer divisor has an exact product witness,
the executable dense-polynomial division returns the witnessed quotient and
zero remainder. -/
theorem divMod_eq_of_monic_mul_eq
    (target candidate quotient : ZPoly)
    (hmonic : DensePoly.Monic candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    DensePoly.divMod target candidate = (quotient, 0) := by
  let qr := DensePoly.divMod target candidate
  have hrem : qr.2 = 0 := by
    simpa [qr] using
      divMod_remainder_eq_zero_of_monic_mul_eq target candidate quotient hmonic hdegree hmul
  have hrecon : qr.1 * candidate + qr.2 = target := by
    simpa [qr] using divMod_reconstruction_of_monic target candidate hmonic
  rw [hrem, DensePoly.add_zero_poly, ← hmul] at hrecon
  have hcandidate_ne : candidate ≠ 0 := by
    intro hzero
    have hdeg : candidate.degree?.getD 0 = 0 := by
      rw [hzero]
      simp [DensePoly.degree?]
    omega
  have hquot : qr.1 = quotient :=
    mul_right_cancel_of_ne_zero hcandidate_ne hrecon
  change qr = (quotient, 0)
  exact Prod.ext hquot hrem

/-- Non-monic exact-multiple divMod identity: if the divisor `candidate` has positive
leading coefficient and positive degree, and the dividend factors as
`quotient * candidate`, the executable dense-polynomial division returns the
witnessed quotient and zero remainder. Sits one level above
`divMod_eq_of_monic_mul_eq`, dropping the monic requirement at the cost of
needing `0 < candidate.leadingCoeff` to discharge the integer-division exactness
side-conditions. -/
theorem divMod_eq_of_pos_lc_pos_degree_mul_eq
    (target candidate quotient : ZPoly)
    (hpos_lc : 0 < DensePoly.leadingCoeff candidate)
    (hdegree : 0 < candidate.degree?.getD 0)
    (hmul : quotient * candidate = target) :
    DensePoly.divMod target candidate = (quotient, 0) := by
  have hlc_ne : DensePoly.leadingCoeff candidate ≠ 0 := by omega
  apply DensePoly.divMod_eq_of_polynomial_mul target candidate quotient hdegree
  · intro a
    exact Int.mul_ediv_cancel a hlc_ne
  · intro a ha hzero
    rcases Int.mul_eq_zero.mp hzero with h | h
    · exact ha h
    · exact hlc_ne h
  · exact hmul


end ZPoly
end Hex
