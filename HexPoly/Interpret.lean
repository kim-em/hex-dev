/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.Euclid.DivGcd
public import HexPoly.Lcm
public import HexPoly.Instances
import all Init.Data.Zero
import all HexPoly.Dense

public section

/-!
Noninjective interpretation of executable dense polynomial operations.

Zero reflection preserves stored length and degree. Preservation of scalar
operations then transports arithmetic, Horner evaluation, differentiation,
division, gcd and extended gcd in their actual execution order, including
size-derived bounds. Neither carrier needs ring laws or an injective map.

The coefficient map uses a list map for ordinary-kernel reduction. Mathlib
polynomial correspondence is composed with these lemmas in the companion.
-/
namespace Hex.DensePoly
namespace Interpret

universe u v w

variable {E : Type u} {F : Type v} [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
variable (f : E → F) (hz : ∀ x, f x = (Zero.zero : F) ↔ x = (Zero.zero : E))

include hz

omit [DecidableEq E] [DecidableEq F] in
theorem map_zero : f (Zero.zero : E) = (Zero.zero : F) := (hz _).mpr rfl

/-- Map each stored coefficient, retaining normalization by zero reflection. -/
@[expose] def map (p : DensePoly E) : DensePoly F where
  coeffs := (p.toArray.toList.map f).toArray
  normalized := by
    change DensePolyNormalized (p.toArray.toList.map f).toArray
    rw [← Array.toList_map, Array.toArray_toList]
    rcases p.normalized with h | h
    · exact Or.inl (by simpa [toArray] using h)
    · right
      rw [Array.back?_map]
      intro he
      cases hb : p.toArray.back? with
      | none => simp [hb] at he
      | some a =>
        simp [hb] at he
        exact h (by simpa [toArray, (hz a).mp he] using hb)

@[simp] theorem map_size (p : DensePoly E) : (map f hz p).size = p.size := by
  simp [map, size, toArray]
@[simp] theorem map_array (p : DensePoly E) :
    (map f hz p).toArray = p.toArray.map f := by
  simp [map, toArray, ← Array.toList_map]

omit [DecidableEq E] [DecidableEq F] in
private theorem get_map (a : Array E) (n : Nat) :
    (a.map f).getD n (Zero.zero : F) = f (a.getD n (Zero.zero : E)) := by
  by_cases h : n < a.size <;> simp [Array.getD, h, map_zero f hz]

private theorem trim_map (a : List E) :
    trimTrailingZerosList (a.map f) = (trimTrailingZerosList a).map f := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, trimTrailingZerosList, ih]
    by_cases h : trimTrailingZerosList as = [] ∧ a = (Zero.zero : E)
    · simp [h.1, h.2, map_zero f hz]
    · have hh : ¬ ((trimTrailingZerosList as).map f = [] ∧ f a = (Zero.zero : F)) := by
        simpa [hz] using h
      simp [h, hz]

theorem map_ofCoeffs (a : Array E) :
    map f hz (ofCoeffs a) = ofCoeffs (a.map f) := by
  apply DensePoly.ext_coeff
  intro i
  simp [coeff, map, ofCoeffs, toArray, trimTrailingZeros, trim_map f hz]

@[simp] theorem map_zero_poly : map f hz (0 : DensePoly E) = (0 : DensePoly F) := by
  have h := map_ofCoeffs f hz (#[] : Array E)
  simpa only [ofCoeffs_empty, Array.map_empty] using h

private theorem degree_map (a : Array E) (n : Nat) :
    arrayDegreeAux (a.map f) n = arrayDegreeAux a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [arrayDegreeAux, get_map f hz, hz, ih]

@[simp] theorem map_coeff (p : DensePoly E) (i : Nat) :
    (map f hz p).coeff i = f (p.coeff i) := by
  change (map f hz p).toArray.getD i (Zero.zero : F) = _
  rw [map_array]
  exact get_map f hz p.toArray i

@[simp] theorem map_list (p : DensePoly E) :
    (map f hz p).toList = p.toList.map f := by
  simp [toList, toArray, map]

/-- Interpretation preserves the zero polynomial and reflects it. -/
theorem map_eq_zero (p : DensePoly E) : map f hz p = 0 ↔ p = 0 := by
  rw [← size_eq_zero_iff, map_size, size_eq_zero_iff]

/-- Addition transfers using only preservation of scalar addition. -/
theorem map_add [Add E] [Add F]
    (ha : ∀ a b, f (a + b) = f a + f b) (p q : DensePoly E) :
    map f hz (p + q) = map f hz p + map f hz q := by
  change map f hz (add p q) = add _ _
  simp only [add_eq_addImpl, addImpl, map_ofCoeffs]
  congr 1
  apply Array.ext
  · simp
  · intro i hi hi'
    simp only [Array.getElem_map, Array.getElem_ofFn, map_coeff, ha]

/-- Subtraction transfers without structural ring laws on either carrier. -/
theorem map_sub [Sub E] [Sub F]
    (hs : ∀ a b, f (a - b) = f a - f b) (p q : DensePoly E) :
    map f hz (p - q) = map f hz p - map f hz q := by
  change map f hz (sub p q) = sub _ _
  simp only [sub_eq_subImpl, subImpl, map_ofCoeffs]
  congr 1
  apply Array.ext
  · simp
  · intro i hi hi'
    simp only [Array.getElem_map, Array.getElem_ofFn, map_coeff, hs]

/-- Scaling transfers even when nonzero representations are not canonical. -/
theorem map_scale [Mul E] [Mul F]
    (hm : ∀ a b, f (a * b) = f a * f b) (c : E) (p : DensePoly E) :
    map f hz (scale c p) = scale (f c) (map f hz p) := by
  simp only [scale_eq_scaleImpl, scaleImpl, map_ofCoeffs, map_array, Array.map_map]
  congr 2
  funext a
  exact hm c a

omit [Zero E] [Zero F] [DecidableEq E] [DecidableEq F] hz in
private theorem fold_map {A : Type w} (xs : List A) (g : E → A → E)
    (g' : F → A → F) (h : ∀ x a, f (g x a) = g' (f x) a) (z : E) :
    f (xs.foldl g z) = xs.foldl g' (f z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons, h] using ih (g z a)

/-- Schoolbook multiplication transfers in its actual accumulation order. -/
theorem map_mul [Add E] [Mul E] [Add F] [Mul F]
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b) (p q : DensePoly E) :
    map f hz (p * q) = map f hz p * map f hz q := by
  apply ext_coeff
  intro n
  simp only [map_coeff, coeff_mul, mulCoeffSum, map_size]
  rw [fold_map f _ _ _ (fun acc i => ?_) (Zero.zero : E), map_zero f hz]
  apply fold_map f
  intro acc j
  simp only [mulCoeffStep, map_coeff]
  split
  · simp only [ha, hm]
  · rfl

/-- Horner evaluation commutes with interpretation, including the zero case. -/
theorem map_eval [Add E] [Mul E] [Add F] [Mul F]
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b) (p : DensePoly E) (x : E) :
    f (eval p x) = eval (map f hz p) (f x) := by
  simp only [eval, map_list]
  generalize p.toList = cs
  induction cs with
  | nil => exact map_zero f hz
  | cons a cs ih => simp only [evalCoeffList, List.map_cons, ha, hm, ih]

/-- Natural-cast preservation is required for the actual derivative. -/
theorem map_derivative [NatCast E] [Mul E] [NatCast F] [Mul F]
    (hn : ∀ n : Nat, f (n : E) = (n : F))
    (hm : ∀ a b, f (a * b) = f a * f b) (p : DensePoly E) :
    map f hz (derivative p) = derivative (map f hz p) := by
  simp only [derivative_eq_derivativeImpl, derivativeImpl, map_ofCoeffs]
  congr 1
  apply Array.ext
  · simp
  · intro i hi hi'
    simp only [Array.getElem_map, Array.getElem_ofFn, map_coeff, hn, hm]

variable [Sub E] [Mul E] [Sub F] [Mul F]
variable (hs : ∀ a b, f (a - b) = f a - f b) (hm : ∀ a b, f (a * b) = f a * f b)
include hs hm

omit [DecidableEq E] [DecidableEq F] in
private theorem step_map (q a : Array E) (shift j : Nat) (c : E) :
    (subtractScaledShiftStep q shift c a j).map f =
      subtractScaledShiftStep (q.map f) shift (f c) (a.map f) j := by
  simp only [subtractScaledShiftStep, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds, get_map f hz, hs, hm]

omit [DecidableEq E] [DecidableEq F] in
private theorem subtract_map (a q : Array E) (shift : Nat) (c : E) :
    (subtractScaledShift a q shift c).map f =
      subtractScaledShift (a.map f) (q.map f) shift (f c) := by
  simp only [subtractScaledShift, Array.size_map]
  exact (List.foldl_hom (fun a : Array E => a.map f)
    (fun a j => (step_map f hz hs hm q a shift j c).symm)).symm

private theorem loop_map (q : Array E) (degree fuel : Nat) (lead : E → E) (lead' : F → F)
    (hl : ∀ a, f (lead a) = lead' (f a)) (quot rem : Array E) :
    let r := divModArrayAux q degree lead fuel quot rem
    (r.1.map f, r.2.map f) =
      divModArrayAux (q.map f) degree lead' fuel (quot.map f) (rem.map f) := by
  induction fuel generalizing quot rem with
  | zero => simp [divModArrayAux]
  | succ n ih =>
    simp only [divModArrayAux, arrayDegree?, Array.size_map, degree_map f hz]
    cases hd : arrayDegreeAux rem rem.size with
    | none => rfl
    | some rd =>
      by_cases h : rd < degree
      · simp [h]
      · simp only [h, ↓reduceDIte]
        simpa only [Array.set!_eq_setIfInBounds, Array.map_setIfInBounds,
          subtract_map f hz hs hm, get_map f hz, hl] using
          ih (quot.set! (rd - degree) (lead (rem.getD rd (Zero.zero : E))))
            (subtractScaledShift rem q (rd - degree) (lead (rem.getD rd (Zero.zero : E))))

omit hs hm [Sub E] [Mul E] [Sub F] [Mul F] in
@[simp] theorem map_isZero (p : DensePoly E) :
    (map f hz p).isZero = p.isZero := by
  simp [map, isZero, toArray, Array.isEmpty]

omit hs hm [Sub E] [Mul E] [Sub F] [Mul F] in
@[simp] theorem map_degree (p : DensePoly E) :
    (map f hz p).natDegree = p.natDegree := by
  simp [natDegree, degree?]

omit hs hm [Sub E] [Mul E] [Sub F] [Mul F] in
theorem map_leading (p : DensePoly E) :
    (map f hz p).leadingCoeff = f p.leadingCoeff := by
  change ((map f hz p).toArray.back?).getD (Zero.zero : F) = _
  rw [map_array, Array.back?_map]
  simp only [leadingCoeff]
  cases h : p.toArray.back? with
  | none =>
    simp only [toArray] at h
    simpa [h] using (map_zero f hz).symm
  | some a => simp only [toArray] at h; simp [h]

private theorem array_division (p q : DensePoly E) (lead : E → E) (lead' : F → F)
    (hl : ∀ a, f (lead a) = lead' (f a)) :
    let r := divModArray p q lead
    (map f hz r.1, map f hz r.2) =
      divModArray (map f hz p) (map f hz q) lead' := by
  simp only [divModArray, map_isZero, map_size]
  split
  · simp [map_zero_poly]
  · simp only [map_array]
    have h := loop_map f hz hs hm q.toArray (q.size - 1) p.size lead lead' hl
      (Array.replicate (p.size - (q.size - 1)) (Zero.zero : E)) p.toArray
    simp only [Array.map_replicate, map_zero f hz] at h
    simpa only [map_ofCoeffs] using
      congrArg (fun r : Array F × Array F => (ofCoeffs r.1, ofCoeffs r.2)) h

variable [One E] [Add E] [Div E] [One F] [Add F] [Div F]
variable (hd : ∀ a b, f (a / b) = f a / f b)
include hd

/-- The actual existing division algorithm commutes with a zero-reflecting
interpretation. The map is not required to be injective. -/
theorem map_divMod (p q : DensePoly E) :
    let r := divMod p q
    (map f hz r.1, map f hz r.2) =
      divMod (map f hz p) (map f hz q) := by
  simp only [divMod, map_degree]
  split
  · simp [map_zero_poly]
  · apply array_division f hz hs hm
    intro a
    rw [hd, map_leading]


/-- Transfer of every iteration of the existing Euclidean loop. -/
private theorem gcd_loop (p q : DensePoly E) (fuel : Nat) :
    map f hz (gcdAux p q fuel) =
      gcdAux (map f hz p) (map f hz q) fuel := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [gcdAux, map_isZero]
    split
    · rfl
    · have hr := congrArg Prod.snd (map_divMod f hz hs hm hd p q)
      change map f hz (divMod p q).2 =
        (divMod (map f hz p) (map f hz q)).2 at hr
      simpa only [hr] using ih q (divMod p q).2

/-- Transfer of the actual gcd, including its structural fuel. -/
theorem map_gcd (p q : DensePoly E) :
    map f hz (gcd p q) = gcd (map f hz p) (map f hz q) := by
  simp only [gcd, map_size]
  exact gcd_loop f hz hs hm hd p q _


omit hs hm hd [Sub E] [Mul E] [Sub F] [Mul F] [Add E] [Div E] [Add F] [Div F] in
/-- The literal scalar one is preserved when the scalar map preserves one. -/
theorem map_one (h1 : f (1 : E) = (1 : F)) :
    map f hz (1 : DensePoly E) = (1 : DensePoly F) := by
  change map f hz (ofCoeffs #[1]) = ofCoeffs #[1]
  rw [map_ofCoeffs]
  simp only [Array.map_singleton, h1]

variable (ha : ∀ a b, f (a + b) = f a + f b)
include ha

/-- The extended Euclidean loop transports all three outputs and accumulators. -/
theorem map_xgcdAux (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly E) (fuel : Nat) :
    let r := xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel
    ({ gcd := map f hz r.gcd, left := map f hz r.left,
       right := map f hz r.right } : XGCDResult F) =
      xgcdAux (map f hz r₀) (map f hz s₀) (map f hz t₀)
        (map f hz r₁) (map f hz s₁) (map f hz t₁) fuel := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero => rfl
  | succ fuel ih =>
    simp only [xgcdAux, map_isZero]
    split
    · rfl
    · have hq := congrArg Prod.fst (map_divMod f hz hs hm hd r₀ r₁)
      have hr := congrArg Prod.snd (map_divMod f hz hs hm hd r₀ r₁)
      rw [← hq, ← hr, ← map_mul f hz ha hm, ← map_sub f hz hs,
        ← map_mul f hz ha hm, ← map_sub f hz hs]
      exact ih _ _ _ _ _ _

/-- Interpretation of the actual extended gcd, with its size-derived bound. -/
theorem map_xgcd (h1 : f (1 : E) = (1 : F)) (p q : DensePoly E) :
    let r := xgcd p q
    ({ gcd := map f hz r.gcd, left := map f hz r.left,
       right := map f hz r.right } : XGCDResult F) =
      xgcd (map f hz p) (map f hz q) := by
  simpa only [xgcd, map_size, map_one f hz h1, map_zero_poly] using
    map_xgcdAux f hz hs hm hd ha p 1 0 q 0 1 (p.size + q.size + 1)

/-- One-sided extended gcd transports the accumulator used by inverse clients. -/
theorem map_xgcdLeftAux (r₀ s₀ r₁ s₁ : DensePoly E) (fuel : Nat) :
    let r := xgcdLeftAux r₀ s₀ r₁ s₁ fuel
    ({ gcd := map f hz r.gcd, left := map f hz r.left } : XGCDLeftResult F) =
      xgcdLeftAux (map f hz r₀) (map f hz s₀)
        (map f hz r₁) (map f hz s₁) fuel := by
  induction fuel generalizing r₀ s₀ r₁ s₁ with
  | zero => rfl
  | succ fuel ih =>
    simp only [xgcdLeftAux, map_isZero]
    split
    · rfl
    · have hq := congrArg Prod.fst (map_divMod f hz hs hm hd r₀ r₁)
      have hr := congrArg Prod.snd (map_divMod f hz hs hm hd r₀ r₁)
      rw [← hq, ← hr, ← map_mul f hz ha hm, ← map_sub f hz hs]
      exact ih _ _ _ _

/-- One-sided extended gcd uses the same interpreted size-derived bound. -/
theorem map_xgcdLeft (h1 : f (1 : E) = (1 : F)) (p q : DensePoly E) :
    let r := xgcdLeft p q
    ({ gcd := map f hz r.gcd, left := map f hz r.left } : XGCDLeftResult F) =
      xgcdLeft (map f hz p) (map f hz q) := by
  simpa only [xgcdLeft, map_size, map_one f hz h1, map_zero_poly] using
    map_xgcdLeftAux f hz hs hm hd ha p 1 q 0 (p.size + q.size + 1)

omit hs hd [Sub E] [Sub F] [Div E] [Div F] in
/-- Binary polynomial exponentiation transfers without ring laws on the carrier. -/
theorem map_natPow (h1 : f (1 : E) = (1 : F)) (p : DensePoly E) (n : Nat) :
    map f hz (natPow p n) = natPow (map f hz p) n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    conv => lhs; rw [natPow]
    conv => rhs; rw [natPow]
    split
    · exact map_one f hz h1
    · rw [← map_mul f hz ha hm]
      have hlt : n / 2 < n := by omega
      split
      · exact ih (n / 2) hlt _
      · rw [map_mul f hz ha hm, ih (n / 2) hlt]

end Interpret

namespace Interpret

variable {E : Type u} {F : Type v}
variable [Zero E] [DecidableEq E] [Inv E] [Mul E]
variable [Zero F] [DecidableEq F] [Inv F] [Mul F]

/-- Monicization transfers semantically; the leading representative need not be literal one. -/
theorem map_monicize (f : E → F) (hz : ∀ x, f x = 0 ↔ x = 0)
    (hm : ∀ a b, f (a * b) = f a * f b) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
    (p : DensePoly E) : map f hz (monicize p) = monicize (map f hz p) := by
  simp only [monicize, map_isZero]
  split
  · exact map_zero_poly f hz
  · rw [map_scale f hz hm, hi, map_leading]

end Interpret
end Hex.DensePoly
