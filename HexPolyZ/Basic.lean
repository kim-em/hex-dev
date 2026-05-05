import HexPoly

/-!
Core `ZPoly` definitions for `hex-poly-z`.

This module specializes the generic dense-polynomial library to integer
coefficients, adds the shared congruence predicate used by Hensel lifting,
and exposes the content/primitive-part operations expected from the
`hex-poly-z` root library.
-/
namespace Hex

/-- Integer polynomials represented by the dense normalized coefficient type
from `HexPoly`. -/
abbrev ZPoly := DensePoly Int

namespace ZPoly

/-- Coefficientwise congruence modulo `m`. -/
def congr (f g : ZPoly) (m : Nat) : Prop :=
  ∀ i, (f.coeff i - g.coeff i) % (m : Int) = 0

/-- Two integer polynomials are coprime mod `p` when they admit a Bezout
combination congruent to `1` modulo `p`. -/
def coprimeModP (f g : ZPoly) (p : Nat) : Prop :=
  ∃ s t : ZPoly, congr (s * f + t * g) 1 p

/-- The nonnegative gcd of the coefficients of `f`. -/
def content (f : ZPoly) : Int :=
  DensePoly.content f

/-- Divide every coefficient by the content to obtain a primitive polynomial. -/
def primitivePart (f : ZPoly) : ZPoly :=
  DensePoly.primitivePart f

/-- A `ZPoly` is primitive when its content is `1`. -/
def Primitive (f : ZPoly) : Prop :=
  content f = 1

/-- View an integer polynomial as a rational polynomial. -/
def toRatPoly (f : ZPoly) : DensePoly Rat :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff : Int => (coeff : Rat)

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

theorem toRatPoly_zero :
    toRatPoly (0 : ZPoly) = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  change ((0 : ZPoly).coeff n : Rat) = (0 : DensePoly Rat).coeff n
  rw [DensePoly.coeff_eq_zero_of_size_le (0 : ZPoly) (by simp)]
  exact (DensePoly.coeff_eq_zero_of_size_le (0 : DensePoly Rat) (by simp)).symm

theorem toRatPoly_C (c : Int) :
    toRatPoly (DensePoly.C c) = DensePoly.C (c : Rat) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    change ((0 : Int) : Rat) = 0
    simp

theorem toRatPoly_one :
    toRatPoly (1 : ZPoly) = 1 := by
  exact toRatPoly_C 1

theorem toRatPoly_scale_int (c : Int) (f : ZPoly) :
    toRatPoly (DensePoly.scale c f) = DensePoly.scale (c : Rat) (toRatPoly f) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  rw [DensePoly.coeff_scale (R := Int) c f n (Int.mul_zero c)]
  rw [DensePoly.coeff_scale (R := Rat) (c : Rat) (toRatPoly f) n (by
    exact Rat.mul_zero (c : Rat))]
  rw [coeff_toRatPoly]
  simp

private theorem size_toRatPoly (f : ZPoly) :
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

private theorem toRatPoly_mulCoeffStep (f g : ZPoly) (n i : Nat) (a : Int) (j : Nat) :
    DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i (a : Rat) j =
      (DensePoly.mulCoeffStep (R := Int) f g n i a j : Rat) := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · simp [hij, coeff_toRatPoly]
  · simp [hij]

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
      rw [size_toRatPoly g]
      rw [toRatPoly_mulCoeffStep_fold]
      simpa [size_toRatPoly g] using
        ih ((List.range g.size).foldl (DensePoly.mulCoeffStep (R := Int) f g n i) a)

private theorem toRatPoly_mulCoeffSum (f g : ZPoly) (n : Nat) :
    DensePoly.mulCoeffSum (toRatPoly f) (toRatPoly g) n =
      (DensePoly.mulCoeffSum (R := Int) f g n : Rat) := by
  unfold DensePoly.mulCoeffSum
  rw [size_toRatPoly f]
  exact toRatPoly_mulCoeffOuter_fold f g n (List.range f.size) 0

theorem toRatPoly_mul (f g : ZPoly) :
    toRatPoly (f * g) = toRatPoly f * toRatPoly g := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_mul, DensePoly.coeff_mul]
  exact (toRatPoly_mulCoeffSum f g n).symm

private def ratCommonDen (coeffs : List Rat) : Nat :=
  coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) 1

private def ratCoeffToIntWithDen (den : Nat) (coeff : Rat) : Int :=
  coeff.num * Int.ofNat (den / coeff.den)

private def normalizePrimitiveSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

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

private theorem ratCommonDen_dvd_of_mem (coeffs : List Rat) {q : Rat} (hq : q ∈ coeffs) :
    q.den ∣ ratCommonDen coeffs := by
  unfold ratCommonDen
  exact ratCommonDen_foldl_dvd_of_mem coeffs hq

private theorem ratCoeffToIntWithDen_cast (den : Nat) (coeff : Rat)
    (hden : coeff.den ∣ den) :
    ((ratCoeffToIntWithDen den coeff : Int) : Rat) = (den : Rat) * coeff := by
  rcases hden with ⟨k, rfl⟩
  unfold ratCoeffToIntWithDen
  rw [Nat.mul_div_right _ coeff.den_pos]
  have hden_ne : ((coeff.den : Nat) : Rat) ≠ 0 := by
    simp [coeff.den_nz]
  have hcoeff : ((coeff.num : Rat) / (coeff.den : Rat)) = coeff := by
    simpa [Rat.divInt_eq_div] using coeff.num_divInt_den
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

private theorem ratCoeffToIntWithDen_zero (den : Nat) :
    ratCoeffToIntWithDen den 0 = 0 := by
  unfold ratCoeffToIntWithDen
  simp

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

private theorem list_getD_toArray_eq_coeff (f : DensePoly Rat) (n : Nat) :
    f.toArray.toList.getD n 0 = f.coeff n := by
  unfold DensePoly.toArray DensePoly.coeff Array.getD
  by_cases hn : n < f.coeffs.size
  · simp [hn, Array.getElem_toList]
  · simp [hn]
    rfl

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

private def ratPolyPrimitivePartCleared (f : DensePoly Rat) : ZPoly :=
  let den := ratCommonDen f.toArray.toList
  DensePoly.ofCoeffs <|
    f.toArray.toList.map (fun coeff => ratCoeffToIntWithDen den coeff) |>.toArray

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
  rw [DensePoly.coeff_scale (R := Rat) u (toRatPoly p) n (Rat.mul_zero u)]
  rw [toRatPoly_scale_int]
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
def SquareFreeRat (f : ZPoly) : Prop :=
  (DensePoly.gcd (toRatPoly f) (DensePoly.derivative (toRatPoly f))).size ≤ 1

/--
Compute the primitive square-free normalization data needed by the integer
factorization pipeline.
-/
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
def squareFreeCore (f : ZPoly) : ZPoly :=
  (primitiveSquareFreeDecomposition f).squareFreeCore

theorem congr_refl (f : ZPoly) (m : Nat) : congr f f m := by
  intro i
  simp

theorem congr_symm (f g : ZPoly) (m : Nat) (hfg : congr f g m) : congr g f m := by
  intro i
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hfg i) with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  grind

theorem congr_trans (f g h : ZPoly) (m : Nat) (hfg : congr f g m) (hgh : congr g h m) :
    congr f h m := by
  intro i
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hfg i) with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero (hgh i) with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  grind

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

private theorem dvd_mul_sub_mul_of_dvd_sub (m a b c d : Int)
    (hab : m ∣ a - b) (hcd : m ∣ c - d) :
    m ∣ a * c - b * d := by
  rcases hab with ⟨u, hu⟩
  rcases hcd with ⟨v, hv⟩
  refine ⟨u * c + b * v, ?_⟩
  grind

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

private theorem fold_mulCoeffStep_range_of_size_le (p q : ZPoly)
    (n i : Nat) (a : Int) {s : Nat} (hs : q.size ≤ s) :
    (List.range s).foldl (DensePoly.mulCoeffStep p q n i) a =
      (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a := by
  have hs' : q.size + (s - q.size) = s := by omega
  rw [← hs']
  exact fold_mulCoeffStep_range_add_zero_tail p q n i a (s - q.size)

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

private theorem mulCoeffSum_eq_outer_range_of_size_le (p q : ZPoly)
    (n : Nat) {s : Nat} (hs : p.size ≤ s) :
    (List.range s).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 =
      DensePoly.mulCoeffSum p q n := by
  unfold DensePoly.mulCoeffSum
  have hs' : p.size + (s - p.size) = s := by omega
  rw [← hs']
  exact fold_mulCoeffOuter_range_add_zero_tail p q n (s - p.size)

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

theorem content_mul_primitivePart (f : ZPoly) :
    DensePoly.scale (content f) (primitivePart f) = f := by
  simpa [content, primitivePart] using DensePoly.content_mul_primitivePart f

theorem primitivePart_primitive (f : ZPoly) (h : content f ≠ 0) :
    Primitive (primitivePart f) := by
  simpa [Primitive, content, primitivePart] using DensePoly.primitivePart_primitive f h

theorem primitiveSquareFreeDecomposition_primitive (f : ZPoly) :
    (primitiveSquareFreeDecomposition f).primitive = primitivePart f := by
  by_cases hzero : (primitivePart f).isZero = true
  · simp [primitiveSquareFreeDecomposition, hzero]
  · by_cases hderivative : (DensePoly.derivative (toRatPoly (primitivePart f))).isZero = true
    · simp [primitiveSquareFreeDecomposition, hzero, hderivative]
    · simp [primitiveSquareFreeDecomposition, hzero, hderivative]

private theorem normalizePrimitiveSign_zero :
    normalizePrimitiveSign (0 : ZPoly) = 0 := by
  unfold normalizePrimitiveSign
  split
  · exact DensePoly.scale_neg_one_zero
  · rfl

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

theorem ratPolyPrimitivePart_primitive (f : DensePoly Rat)
    (h : content (ratPolyPrimitivePart f) ≠ 0) :
    Primitive (ratPolyPrimitivePart f) := by
  unfold ratPolyPrimitivePart at h ⊢
  exact normalizePrimitiveSign_primitivePart_primitive _ h

theorem ratPolyPrimitivePart_rational_associate (f : DensePoly Rat) :
    ∃ unit : Rat, f = DensePoly.scale unit (toRatPoly (ratPolyPrimitivePart f)) := by
  exact ratPolyPrimitivePart_rational_associate_core f

private theorem rat_scale_zero (p : DensePoly Rat) :
    DensePoly.scale 0 p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) 0 p n (Rat.mul_zero 0)]
  rw [DensePoly.coeff_zero]
  exact Rat.zero_mul (p.coeff n)

private theorem rat_scale_one (p : DensePoly Rat) :
    DensePoly.scale 1 p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) 1 p n (Rat.mul_zero 1)]
  exact Rat.one_mul (p.coeff n)

private theorem rat_list_getD_map_range (size n : Nat) (f : Nat → Rat) :
    ((List.range size).map f).getD n 0 =
      if n < size then f n else 0 := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

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

private theorem rat_derivative_scale (u : Rat) (p : DensePoly Rat) :
    DensePoly.derivative (DensePoly.scale u p) =
      DensePoly.scale u (DensePoly.derivative p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [rat_coeff_derivative]
  rw [DensePoly.coeff_scale (R := Rat) u (DensePoly.derivative p) n (Rat.mul_zero u)]
  rw [rat_coeff_derivative]
  rw [DensePoly.coeff_scale (R := Rat) u p (n + 1) (Rat.mul_zero u)]
  grind [Rat.mul_assoc, Rat.mul_comm]

private theorem rat_derivative_mul (p q : DensePoly Rat) :
    DensePoly.derivative (p * q) =
      DensePoly.derivative p * q + p * DensePoly.derivative q := by
  apply DensePoly.ext_coeff
  intro n
  rw [rat_coeff_derivative]
  rw [DensePoly.coeff_mul p q (n + 1)]
  rw [DensePoly.coeff_add (DensePoly.derivative p * q) (p * DensePoly.derivative q) n
    (by exact Rat.zero_add (0 : Rat))]
  rw [DensePoly.coeff_mul (DensePoly.derivative p) q n]
  rw [DensePoly.coeff_mul p (DensePoly.derivative q) n]
  exact DensePoly.rat_mulCoeffSum_derivative_product_rule p q n

private theorem rat_dvd_mul_left {d p : DensePoly Rat} (q : DensePoly Rat) :
    d ∣ p → d ∣ q * p := by
  intro h
  rcases h with ⟨a, ha⟩
  refine ⟨q * a, ?_⟩
  rw [ha, ← DensePoly.mul_assoc_poly q d a, DensePoly.mul_comm_poly q d,
    DensePoly.mul_assoc_poly d q a]

private theorem rat_dvd_mul_right {d p : DensePoly Rat} (q : DensePoly Rat) :
    d ∣ p → d ∣ p * q := by
  intro h
  rw [DensePoly.mul_comm_poly p q]
  exact rat_dvd_mul_left q h

private theorem rat_dvd_add {d p q : DensePoly Rat} :
    d ∣ p → d ∣ q → d ∣ p + q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb, DensePoly.mul_add_right_poly]

private theorem rat_dvd_sub {d p q : DensePoly Rat} :
    d ∣ p → d ∣ q → d ∣ p - q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + (0 - b), ?_⟩
  rw [DensePoly.sub_eq_add_neg_poly, ha, hb, DensePoly.mul_add_right_poly,
    DensePoly.mul_sub_zero_comm, DensePoly.mul_comm_poly b d]

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

private theorem rat_list_foldl_ignore {α : Type _} (xs : List Nat) (init : α) :
    xs.foldl (fun acc _ => acc) init = init := by
  induction xs generalizing init with
  | nil =>
      rfl
  | cons _ xs ih =>
      simpa using ih init

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

private theorem rat_scale_mulCoeffStep (u v : Rat) (p q : DensePoly Rat)
    (n i : Nat) (a : Rat) (j : Nat) :
    DensePoly.mulCoeffStep (DensePoly.scale u p) (DensePoly.scale v q) n i
        ((u * v) * a) j =
      (u * v) * DensePoly.mulCoeffStep p q n i a j := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · rw [if_pos hij, if_pos hij]
    rw [DensePoly.coeff_scale (R := Rat) u p i (Rat.mul_zero u)]
    rw [DensePoly.coeff_scale (R := Rat) v q j (Rat.mul_zero v)]
    grind
  · rw [if_neg hij, if_neg hij]

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

private theorem rat_scale_mulCoeffSum_of_ne_zero {u v : Rat} (hu : u ≠ 0) (hv : v ≠ 0)
    (p q : DensePoly Rat) (n : Nat) :
    DensePoly.mulCoeffSum (DensePoly.scale u p) (DensePoly.scale v q) n =
      (u * v) * DensePoly.mulCoeffSum p q n := by
  unfold DensePoly.mulCoeffSum
  rw [rat_scale_size_of_ne_zero hu p]
  rw [rat_scale_size_of_ne_zero hv q]
  simpa using rat_scale_mulCoeffOuter_fold u v p q n (List.range p.size) 0

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
      simpa using rat_list_foldl_ignore (List.range (DensePoly.scale u p).size) (0 : Rat)
    · apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_mul]
      rw [rat_scale_mulCoeffSum_of_ne_zero hu hv]
      rw [DensePoly.coeff_scale (R := Rat) (u * v) (p * q) n (Rat.mul_zero (u * v))]
      rw [DensePoly.coeff_mul]

private theorem rat_leadingCoeff_ne_zero_of_pos_size (p : DensePoly Rat) (hpos : 0 < p.size) :
    p.leadingCoeff ≠ 0 := by
  have hidx : p.coeffs.size - 1 < p.coeffs.size := by
    simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
  have hlead_eq : p.leadingCoeff = p.coeff (p.size - 1) := by
    unfold DensePoly.leadingCoeff DensePoly.coeff
    change p.coeffs.back?.getD (0 : Rat) =
      p.coeffs.getD (p.coeffs.size - 1) (Zero.zero : Rat)
    rw [Array.back?_eq_getElem?]
    rw [Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem hidx]
    rfl
  rw [hlead_eq]
  exact DensePoly.coeff_last_ne_zero_of_pos_size p hpos

private theorem rat_div_mul_cancel_of_ne (a b : Rat) (hb : b ≠ 0) :
    a - (a / b) * b = 0 := by
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

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

private theorem rat_divMod_spec_core (p q : DensePoly Rat) :
    let qr := DensePoly.divMod p q
    qr.1 * q + qr.2 = p := by
  by_cases hq : q.size = 0
  · have hrem := DensePoly.divMod_remainder_eq_self_of_size_zero_core p q hq
    have hqzero : q = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_eq_zero_of_size_le q (by omega)]
      rw [DensePoly.coeff_zero]
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

private theorem rat_mod_remainder_degree_lt_core (p q : DensePoly Rat)
    (hdegree : 0 < q.degree?.getD 0) :
    (p % q).degree?.getD 0 < q.degree?.getD 0 := by
  simpa [DensePoly.mod] using rat_divMod_remainder_degree_lt_core p q hdegree

private theorem rat_mod_zero_right_of_size_zero (p m : DensePoly Rat)
    (hm : m.size = 0) :
    p % m = p := by
  simpa [DensePoly.mod] using
    DensePoly.divMod_remainder_eq_self_of_size_zero_core p m hm

private theorem rat_mod_sub_self_eq_mul_neg_div_of_not_isZero (p m : DensePoly Rat)
    (hmzero : ¬ m.isZero) :
    p % m - p = m * (0 - p / m) := by
  have hdiv : (p / m) * m + (p % m) = p := by
    simpa [DensePoly.div, DensePoly.mod] using rat_divMod_spec_core_of_not_isZero p m hmzero
  calc
    p % m - p = 0 - (p / m) * m := by
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun x : DensePoly Rat => x.coeff n) hdiv
      have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
      have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
      change (((p / m) * m + (p % m)).coeff n = p.coeff n) at hcoeff
      rw [DensePoly.coeff_add ((p / m) * m) (p % m) n hzero_add] at hcoeff
      rw [DensePoly.coeff_sub (p % m) p n hzero_sub]
      rw [DensePoly.coeff_sub 0 ((p / m) * m) n hzero_sub]
      rw [DensePoly.coeff_zero]
      grind
    _ = m * (0 - (p / m)) := by
      exact (DensePoly.mul_sub_zero_comm m (p / m)).symm

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
    rw [DensePoly.coeff_sub p p i hzero_sub]
    rw [DensePoly.zero_mul, DensePoly.coeff_zero]
    grind
  · exact ⟨0 - (p / m), rat_mod_sub_self_eq_mul_neg_div_of_not_isZero p m hmzero⟩

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

private theorem rat_add_sub_add_right (a b c d : DensePoly Rat) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) (c + d) n hzero_sub]
  rw [DensePoly.coeff_add a b n hzero_add]
  rw [DensePoly.coeff_add c d n hzero_add]
  rw [DensePoly.coeff_add (a - c) (b - d) n hzero_add]
  rw [DensePoly.coeff_sub a c n hzero_sub]
  rw [DensePoly.coeff_sub b d n hzero_sub]
  grind

private theorem rat_sub_zero_right (p : DensePoly Rat) :
    p - 0 = p := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  rw [DensePoly.coeff_sub p 0 n hzero_sub, DensePoly.coeff_zero]
  grind

private theorem rat_zero_mod_eq_zero (m : DensePoly Rat) :
    (0 : DensePoly Rat) % m = 0 := by
  by_cases hm_zero : m.size = 0
  · exact rat_mod_zero_right_of_size_zero 0 m hm_zero
  · by_cases hdegree : 0 < m.degree?.getD 0
    · have hzero_degree : (0 : DensePoly Rat).degree?.getD 0 = 0 := by
        rfl
      have hlt : (0 : DensePoly Rat).degree?.getD 0 < m.degree?.getD 0 := by
        rw [hzero_degree]
        exact hdegree
      have hdiv := DensePoly.divMod_eq_zero_self_of_degree_lt (0 : DensePoly Rat) m hlt
      simpa [DensePoly.mod] using congrArg Prod.snd hdiv
    · have hm_size : m.size = 1 := by
        have hm_pos : 0 < m.size := Nat.pos_of_ne_zero hm_zero
        have hdeg : m.degree?.getD 0 = m.size - 1 := by
          simp [DensePoly.degree?, hm_zero]
        rw [hdeg] at hdegree
        omega
      have hlead_ne : m.leadingCoeff ≠ (Zero.zero : Rat) := by
        exact rat_leadingCoeff_ne_zero_of_pos_size m (by omega)
      simpa [DensePoly.mod] using
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core (0 : DensePoly Rat) m
          hm_size (fun a => rat_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)

private theorem rat_sub_self_right_add (a b : DensePoly Rat) :
    (a + b) - a = b := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : Rat) - (0 : Rat) = 0 := by grind
  have hzero_add : (0 : Rat) + (0 : Rat) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) a n hzero_sub]
  rw [DensePoly.coeff_add a b n hzero_add]
  grind

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

private theorem rat_size_le_one_of_mul_dvd_self
    (d r : DensePoly Rat) (hr : r.size ≠ 0) :
    d * r ∣ r → d.size ≤ 1 := by
  intro hdiv
  rcases hdiv with ⟨k, hk⟩
  by_cases hd_zero : d.size = 0
  · omega
  have hd_pos : 0 < d.size := Nat.pos_of_ne_zero hd_zero
  have hr_pos : 0 < r.size := Nat.pos_of_ne_zero hr
  by_cases hk_zero : k.size = 0
  · have hk_eq : k = 0 := rat_eq_zero_of_size_zero k hk_zero
    have hr_eq_zero : r = 0 := by
      rw [hk_eq, rat_mul_zero_right] at hk
      exact hk
    have hr_size_zero : r.size = 0 := by
      rw [hr_eq_zero]
      exact DensePoly.size_zero
    contradiction
  · have hk_pos : 0 < k.size := Nat.pos_of_ne_zero hk_zero
    by_cases hd_le : d.size ≤ 1
    · exact hd_le
    · have hdr_top_lt : d.size - 1 + (r.size - 1) < (d * r).size :=
        rat_product_size_gt_top d r hd_pos hr_pos
      have hdr_pos : 0 < (d * r).size := by omega
      have htop_lt : (d * r).size - 1 + (k.size - 1) < ((d * r) * k).size :=
        rat_product_size_gt_top (d * r) k hdr_pos hk_pos
      have hsize_eq : ((d * r) * k).size = r.size := by
        rw [← hk]
      rw [hsize_eq] at htop_lt
      have hdr_lower : r.size ≤ (d * r).size - 1 := by omega
      have hcontr : r.size ≤ (d * r).size - 1 + (k.size - 1) := by omega
      omega

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

private theorem rat_mod_eq_mod_of_congr_pos_degree (p q m : DensePoly Rat)
    (hdegree : 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr p q m) :
    p % m = q % m := by
  apply rat_canonical_remainder_unique_of_pos_degree
  · exact rat_mod_remainder_degree_lt_core p m hdegree
  · exact rat_mod_remainder_degree_lt_core q m hdegree
  · exact rat_mod_remainders_congr_of_congr p q m hcongr

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
      simpa [DensePoly.mod] using
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core p m hm_size
          (fun a => rat_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    have hqmod :
        q % m = 0 := by
      simpa [DensePoly.mod] using
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core q m hm_size
          (fun a => rat_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    rw [hpmod, hqmod]

private theorem rat_mod_eq_mod_of_congr_core (p q m : DensePoly Rat)
    (hcongr : DensePoly.Congr p q m) :
    p % m = q % m := by
  by_cases hdegree : 0 < m.degree?.getD 0
  · exact rat_mod_eq_mod_of_congr_pos_degree p q m hdegree hcongr
  · exact rat_mod_eq_mod_of_congr_not_pos_degree p q m hdegree hcongr

private theorem rat_mod_eq_zero_of_dvd_core (p q : DensePoly Rat)
    (hdiv : q ∣ p) :
    p % q = 0 := by
  rcases hdiv with ⟨r, hr⟩
  rw [← rat_zero_mod_eq_zero q]
  apply rat_mod_eq_mod_of_congr_core
  exact ⟨r, by
    rw [rat_sub_zero_right, hr]⟩

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

private instance ratGcdLaws : DensePoly.GcdLaws Rat where
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

private theorem rat_quotient_derivative_gcd_dvd_repeated
    (ratPrimitive : DensePoly Rat) :
    let derivative := DensePoly.derivative ratPrimitive
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    DensePoly.gcd quotientRat (DensePoly.derivative quotientRat) ∣ repeatedRat := by
  intro derivative repeatedRat quotientRat
  exact
    rat_common_divisor_quotient_derivative_dvd_repeated ratPrimitive
      (DensePoly.gcd quotientRat (DensePoly.derivative quotientRat))
      (by simpa [quotientRat] using
        DensePoly.gcd_dvd_left quotientRat (DensePoly.derivative quotientRat))
      (by simpa [quotientRat] using
        DensePoly.gcd_dvd_right quotientRat (DensePoly.derivative quotientRat))

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
    have hzero_add : (0 : Rat) + 0 = 0 := by grind
    have hzero_sub : (0 : Rat) - 0 = 0 := by grind
    rw [DensePoly.coeff_sub _ _ n hzero_sub]
    rw [DensePoly.coeff_add _ _ n hzero_add]
    grind
  rw [heq] at hsub
  rw [DensePoly.mul_comm_poly]
  exact hsub

/-- Iterated polynomial power for `DensePoly Rat`. We avoid relying on a generic
`Monoid` instance and define this directly by recursion. -/
private def ratPolyPow (d : DensePoly Rat) : Nat → DensePoly Rat
  | 0 => 1
  | n + 1 => d * ratPolyPow d n

@[simp] private theorem ratPolyPow_zero (d : DensePoly Rat) :
    ratPolyPow d 0 = 1 := rfl

@[simp] private theorem ratPolyPow_succ (d : DensePoly Rat) (n : Nat) :
    ratPolyPow d (n + 1) = d * ratPolyPow d n := rfl

private theorem ratPolyPow_one (d : DensePoly Rat) :
    ratPolyPow d 1 = d := by
  show d * ratPolyPow d 0 = d
  show d * (1 : DensePoly Rat) = d
  exact DensePoly.mul_one_right_poly d

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
    rw [rat_derivative_mul]
    rw [DensePoly.mul_add_right_poly]
    apply rat_dvd_add
    · rcases h with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← DensePoly.mul_assoc_poly]
      rw [hc]
      rw [DensePoly.mul_assoc_poly d c (ratPolyPow d (k + 1))]
      rw [DensePoly.mul_comm_poly c (ratPolyPow d (k + 1))]
      rw [← DensePoly.mul_assoc_poly]
    · rcases ih with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← DensePoly.mul_assoc_poly]
      rw [DensePoly.mul_comm_poly a d]
      rw [DensePoly.mul_assoc_poly]
      rw [hc]
      rw [← DensePoly.mul_assoc_poly]

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
      rw [h1, ha, hQ]
      rw [DensePoly.mul_assoc_poly d a (ratPolyPow d (k + 1) * Q)]
      rw [← DensePoly.mul_assoc_poly a (ratPolyPow d (k + 1)) Q]
      rw [DensePoly.mul_comm_poly a (ratPolyPow d (k + 1))]
      rw [DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) a Q]
      rw [← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1)) (a * Q)]
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
        rw [ha', hQ]
        rw [DensePoly.mul_assoc_poly d a' (ratPolyPow d (k + 1) * Q)]
        rw [← DensePoly.mul_assoc_poly a' (ratPolyPow d (k + 1)) Q]
        rw [DensePoly.mul_comm_poly a' (ratPolyPow d (k + 1))]
        rw [DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) a' Q]
        rw [← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1)) (a' * Q)]
      · rw [ha, hQ]
        rw [rat_derivative_mul]
        rw [DensePoly.mul_add_right_poly]
        apply rat_dvd_add
        · have haux := ratPolyPow_succ_dvd_a_mul_derivative hcofactor k
          rcases haux with ⟨c, hc⟩
          refine ⟨c * Q, ?_⟩
          rw [DensePoly.mul_assoc_poly d a
            (DensePoly.derivative (ratPolyPow d (k + 1)) * Q)]
          rw [← DensePoly.mul_assoc_poly a
            (DensePoly.derivative (ratPolyPow d (k + 1))) Q]
          rw [hc]
          rw [DensePoly.mul_assoc_poly (ratPolyPow d (k + 1)) c Q]
          rw [← DensePoly.mul_assoc_poly d (ratPolyPow d (k + 1)) (c * Q)]
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

/-- Polynomial-power size lower bound. If `2 ≤ d.size`, then
`(ratPolyPow d n).size ≥ n + 1`. -/
private theorem rat_pow_size_lower_bound
    (d : DensePoly Rat) (hd : 2 ≤ d.size) (n : Nat) :
    n + 1 ≤ (ratPolyPow d n).size := by
  induction n with
  | zero =>
    rw [ratPolyPow_zero]
    show 1 ≤ (DensePoly.C (1 : Rat)).size
    unfold DensePoly.size
    rw [DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Rat) ≠ 0)]
    decide
  | succ k ih =>
    rw [ratPolyPow_succ]
    have hd_pos : 0 < d.size := by omega
    have hk_pos : 0 < (ratPolyPow d k).size := by omega
    have hgt := rat_product_size_gt_top d (ratPolyPow d k) hd_pos hk_pos
    omega

/-- If `b ≠ 0` and `a ∣ b`, then `a.size ≤ b.size`. -/
private theorem rat_size_le_of_dvd
    (a b : DensePoly Rat) (hb : b.size ≠ 0) (hab : a ∣ b) :
    a.size ≤ b.size := by
  by_cases ha_zero : a.size = 0
  · omega
  have ha_pos : 0 < a.size := Nat.pos_of_ne_zero ha_zero
  rcases hab with ⟨k, hk⟩
  by_cases hk_zero : k.size = 0
  · have hk_eq : k = 0 := rat_eq_zero_of_size_zero k hk_zero
    have hb_eq : b = 0 := by
      rw [hk, hk_eq, rat_mul_zero_right]
    have hb_size_zero : b.size = 0 := by
      rw [hb_eq, DensePoly.size_zero]
    contradiction
  · have hk_pos : 0 < k.size := Nat.pos_of_ne_zero hk_zero
    have hgt := rat_product_size_gt_top a k ha_pos hk_pos
    have hsize_eq : b.size = (a * k).size := by rw [hk]
    omega

/-- Common-divisor size bound: divisors of both `quotientRat` and its derivative
have size at most one. -/
private theorem rat_quotient_common_divisor_size_le_one
    (ratPrimitive d : DensePoly Rat)
    (hrep : DensePoly.gcd ratPrimitive (DensePoly.derivative ratPrimitive) ≠ 0) :
    let derivative := DensePoly.derivative ratPrimitive
    let repeatedRat := DensePoly.gcd ratPrimitive derivative
    let quotientRat := ratPrimitive / repeatedRat
    d ∣ quotientRat →
    d ∣ DensePoly.derivative quotientRat →
    d.size ≤ 1 := by
  intro derivative repeatedRat quotientRat hdq hdq'
  rcases Nat.lt_or_ge 1 d.size with hgt | hle
  · exfalso
    have hd_two : 2 ≤ d.size := hgt
    have hrep_size : repeatedRat.size ≠ 0 := by
      intro hsize
      exact hrep (rat_eq_zero_of_size_zero repeatedRat hsize)
    have hdvd_repeated :
        ratPolyPow d (repeatedRat.size + 1) ∣ repeatedRat :=
      rat_pow_dvd_repeated_of_quotient_common_divisor ratPrimitive d hdq hdq'
        repeatedRat.size
    have hpow_size_lower :
        repeatedRat.size + 1 + 1 ≤ (ratPolyPow d (repeatedRat.size + 1)).size :=
      rat_pow_size_lower_bound d hd_two (repeatedRat.size + 1)
    have hpow_size_upper :
        (ratPolyPow d (repeatedRat.size + 1)).size ≤ repeatedRat.size :=
      rat_size_le_of_dvd (ratPolyPow d (repeatedRat.size + 1)) repeatedRat
        hrep_size hdvd_repeated
    omega
  · exact hle

private theorem densePoly_eq_zero_of_isZero_true {R : Type _} [Zero R] [DecidableEq R]
    (p : DensePoly R) (h : p.isZero = true) :
    p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : p.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using h
  rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]
  rw [DensePoly.coeff_zero]
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

private theorem content_C_int (c : Int) :
    content (DensePoly.C c) = Int.ofNat c.natAbs := by
  simpa [content] using DensePoly.content_C c

private theorem int_eq_one_or_neg_one_of_natAbs_eq_one {c : Int}
    (habs : c.natAbs = 1) :
    c = 1 ∨ c = -1 := by
  cases c with
  | ofNat n =>
      left
      simp at habs
      subst n
      rfl
  | negSucc n =>
      right
      simp at habs
      have hn : n = 0 := by omega
      subst n
      rfl

private theorem normalizePrimitiveSign_C_one :
    normalizePrimitiveSign (DensePoly.C (1 : Int)) = 1 := by
  unfold normalizePrimitiveSign
  have hlead : ¬ DensePoly.leadingCoeff (DensePoly.C (1 : Int)) < 0 := by
    simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Int) ≠ 0)]
  rw [if_neg hlead]
  rfl

private theorem normalizePrimitiveSign_C_neg_one :
    normalizePrimitiveSign (DensePoly.C (-1 : Int)) = 1 := by
  unfold normalizePrimitiveSign
  have hlead : DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) < 0 := by
    simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
  rw [if_pos hlead]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) (-1 : Int) (DensePoly.C (-1 : Int)) n
    (Int.mul_zero (-1 : Int))]
  change -1 * (DensePoly.C (-1 : Int)).coeff n = (DensePoly.C (1 : Int)).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    change - (0 : Int) = (0 : Int)
    rfl

private theorem normalizePrimitiveSign_eq_one_of_primitive_size_le_one
    (p : ZPoly) (hprimitive : Primitive p) (hsize : p.size ≤ 1) :
    normalizePrimitiveSign p = 1 := by
  have hpC := densePoly_eq_C_coeff_zero_of_size_le_one p hsize
  have hcontent :
      content (DensePoly.C (p.coeff 0)) = 1 := by
    have hprimitive_eq : content p = 1 := hprimitive
    rw [hpC] at hprimitive_eq
    exact hprimitive_eq
  have habs : (p.coeff 0).natAbs = 1 := by
    have hcast : ((p.coeff 0).natAbs : Int) = 1 := by
      simpa [content_C_int] using hcontent
    exact_mod_cast hcast
  rcases int_eq_one_or_neg_one_of_natAbs_eq_one habs with hcoeff | hcoeff
  · rw [hpC, hcoeff]
    exact normalizePrimitiveSign_C_one
  · rw [hpC, hcoeff]
    exact normalizePrimitiveSign_C_neg_one

private theorem squareFreeRat_one :
    SquareFreeRat 1 := by
  unfold SquareFreeRat
  rw [toRatPoly_one]
  exact DensePoly.size_C_le_one (1 : Rat)

theorem primitiveSquareFreeDecomposition_reassembly_over_rat (f : ZPoly) :
    let d := primitiveSquareFreeDecomposition f
    ∃ unit : Rat,
      toRatPoly d.primitive =
        DensePoly.scale unit (toRatPoly d.squareFreeCore * toRatPoly d.repeatedPart) := by
  unfold primitiveSquareFreeDecomposition
  by_cases hzero : (primitivePart f).isZero = true
  · refine ⟨0, ?_⟩
    rw [if_pos hzero]
    have hprimitive_zero : primitivePart f = 0 :=
      densePoly_eq_zero_of_isZero_true (primitivePart f) hzero
    rw [hprimitive_zero, toRatPoly_zero]
    rw [rat_scale_zero]
  · rw [if_neg hzero]
    let ratPrimitive := toRatPoly (primitivePart f)
    let derivative := DensePoly.derivative ratPrimitive
    by_cases hderivative : derivative.isZero = true
    · rcases toRatPoly_normalizePrimitiveSign_rational_associate (primitivePart f) with
        ⟨unit, hunit⟩
      refine ⟨unit, ?_⟩
      rw [if_pos hderivative]
      rw [toRatPoly_one, DensePoly.mul_one_right_poly]
      simpa [ratPrimitive] using hunit
    · rw [if_neg hderivative]
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      let quotientRat := ratPrimitive / repeatedRat
      rcases ratPolyPrimitivePart_rational_associate quotientRat with
        ⟨coreUnit, hcore⟩
      rcases ratPolyPrimitivePart_rational_associate repeatedRat with
        ⟨repeatedUnit, hrepeated⟩
      refine ⟨coreUnit * repeatedUnit, ?_⟩
      have htarget :
          ratPrimitive =
            DensePoly.scale (coreUnit * repeatedUnit)
              (toRatPoly (ratPolyPrimitivePart quotientRat) *
                toRatPoly (ratPolyPrimitivePart repeatedRat)) := by
        have hrec : quotientRat * repeatedRat = ratPrimitive := by
          simpa [quotientRat, repeatedRat] using rat_div_gcd_mul_reconstruct ratPrimitive derivative
        rw [← hrec]
        calc
          quotientRat * repeatedRat =
              DensePoly.scale coreUnit (toRatPoly (ratPolyPrimitivePart quotientRat)) *
                repeatedRat := by
            exact congrArg (fun x => x * repeatedRat) hcore
          _ =
              DensePoly.scale coreUnit (toRatPoly (ratPolyPrimitivePart quotientRat)) *
                DensePoly.scale repeatedUnit (toRatPoly (ratPolyPrimitivePart repeatedRat)) := by
            exact congrArg
              (fun x => DensePoly.scale coreUnit (toRatPoly (ratPolyPrimitivePart quotientRat)) * x)
              hrepeated
          _ =
              DensePoly.scale (coreUnit * repeatedUnit)
                (toRatPoly (ratPolyPrimitivePart quotientRat) *
                  toRatPoly (ratPolyPrimitivePart repeatedRat)) := by
            rw [rat_scale_mul_scale]
      simpa [ratPrimitive, derivative, repeatedRat, quotientRat] using htarget

theorem primitiveSquareFreeDecomposition_squareFreeCore
    (f : ZPoly)
    (hcore : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0) :
    SquareFreeRat (primitiveSquareFreeDecomposition f).squareFreeCore := by
  unfold primitiveSquareFreeDecomposition at hcore ⊢
  by_cases hzero : (primitivePart f).isZero = true
  · simp [hzero] at hcore
  · simp [hzero]
    let p := primitivePart f
    let ratPrimitive := toRatPoly p
    let derivative := DensePoly.derivative ratPrimitive
    by_cases hderivative : derivative.isZero = true
    · have hderivative_eq : derivative = 0 :=
        densePoly_eq_zero_of_isZero_true derivative hderivative
      have hcontent_ne : content f ≠ 0 := by
        intro hcontent
        have hpart_zero : primitivePart f = 0 := by
          simpa [primitivePart] using
            DensePoly.primitivePart_eq_zero_of_content_eq_zero f
              (by simpa [content] using hcontent)
        have hisZero : (primitivePart f).isZero = true := by
          rw [hpart_zero]
          rfl
        rw [hisZero] at hzero
        contradiction
      have hprimitive : Primitive p := by
        simpa [p] using primitivePart_primitive f hcontent_ne
      have hsize : p.size ≤ 1 := by
        exact size_le_one_of_toRatPoly_derivative_zero p (by
          simpa [derivative, ratPrimitive] using hderivative_eq)
      have hcore_eq : normalizePrimitiveSign p = 1 :=
        normalizePrimitiveSign_eq_one_of_primitive_size_le_one p hprimitive hsize
      rw [if_pos hderivative]
      change SquareFreeRat (normalizePrimitiveSign p)
      rw [hcore_eq]
      exact squareFreeRat_one
    · rw [if_neg hderivative]
      sorry

theorem coprimeModP_of_bezout
    (f g s t : ZPoly) (p : Nat)
    (hbez : congr (s * f + t * g) 1 p) :
    coprimeModP f g p := by
  exact ⟨s, t, hbez⟩

end ZPoly
end Hex
