/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexPoly.Euclid.DivGcd
import all Init.Data.Zero
import all HexPoly.Dense
public section

/-! Noninjective interpretation of the actual DensePoly division algorithm.
Only zero reflection and preservation of the operations used by division are
assumed. No field laws, injectivity, or structural arithmetic laws on E. -/
namespace Transfer
open Hex DensePoly
variable {E F : Type} [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
variable (f : E → F) (hz : ∀ x, f x = (Zero.zero : F) ↔ x = (Zero.zero : E))

include hz

omit [DecidableEq E] [DecidableEq F] in
theorem map_zero : f (Zero.zero : E) = (Zero.zero : F) := (hz _).mpr rfl

@[expose] def mapPoly (hz : ∀ x, f x = (Zero.zero : F) ↔ x = (Zero.zero : E)) (p : DensePoly E) : DensePoly F where
  coeffs := p.toArray.map f
  normalized := by
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

@[simp] theorem map_size (p : DensePoly E) : (mapPoly f hz p).size = p.size := by
  simp [mapPoly, size, toArray]
@[simp] theorem map_array (p : DensePoly E) :
    (mapPoly f hz p).toArray = p.toArray.map f := rfl

omit [DecidableEq E] [DecidableEq F] in
theorem get_map (a : Array E) (n : Nat) :
    (a.map f).getD n (Zero.zero : F) = f (a.getD n (Zero.zero : E)) := by
  by_cases h : n < a.size <;> simp [Array.getD, h, map_zero f hz]

theorem trim_map (a : List E) :
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
    mapPoly f hz (ofCoeffs a) = ofCoeffs (a.map f) := by
  apply DensePoly.ext_coeff
  intro i
  simp [coeff, mapPoly, ofCoeffs, toArray, trimTrailingZeros, trim_map f hz]

@[simp] theorem map_zero_poly : mapPoly f hz (0 : DensePoly E) = (0 : DensePoly F) := by
  have h := map_ofCoeffs f hz (#[] : Array E)
  simpa only [ofCoeffs_empty, Array.map_empty] using h

theorem degree_map (a : Array E) (n : Nat) :
    arrayDegreeAux (a.map f) n = arrayDegreeAux a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [arrayDegreeAux, get_map f hz, hz, ih]

variable [Sub E] [Mul E] [Sub F] [Mul F]
variable (hs : ∀ a b, f (a-b) = f a-f b) (hm : ∀ a b, f (a*b) = f a*f b)
include hs hm

omit [DecidableEq E] [DecidableEq F] in
theorem step_map (q a : Array E) (shift j : Nat) (c : E) :
    (subtractScaledShiftStep q shift c a j).map f =
      subtractScaledShiftStep (q.map f) shift (f c) (a.map f) j := by
  simp only [subtractScaledShiftStep, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds, get_map f hz, hs, hm]

omit [DecidableEq E] [DecidableEq F] in
theorem subtract_map (a q : Array E) (shift : Nat) (c : E) :
    (subtractScaledShift a q shift c).map f =
      subtractScaledShift (a.map f) (q.map f) shift (f c) := by
  simp only [subtractScaledShift, Array.size_map]
  exact (List.foldl_hom (fun a : Array E => a.map f)
    (fun a j => (step_map f hz hs hm q a shift j c).symm)).symm

theorem loop_map (q : Array E) (degree fuel : Nat) (lead : E → E) (lead' : F → F)
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
          ih (quot.set! (rd-degree) (lead (rem.getD rd (Zero.zero : E))))
            (subtractScaledShift rem q (rd-degree) (lead (rem.getD rd (Zero.zero : E))))

omit hs hm [Sub E] [Mul E] [Sub F] [Mul F] in
@[simp] theorem map_isZero (p : DensePoly E) :
    (mapPoly f hz p).isZero = p.isZero := by
  simp [mapPoly, isZero, toArray, Array.isEmpty]

omit hs hm [Sub E] [Mul E] [Sub F] [Mul F] in
@[simp] theorem map_degree (p : DensePoly E) :
    (mapPoly f hz p).natDegree = p.natDegree := by
  simp [natDegree, degree?]

omit hs hm [Sub E] [Mul E] [Sub F] [Mul F] in
theorem map_leading (p : DensePoly E) :
    (mapPoly f hz p).leadingCoeff = f p.leadingCoeff := by
  simp only [leadingCoeff, mapPoly, Array.back?_map]
  cases h : p.toArray.back? with
  | none =>
    simp only [toArray] at h
    simpa [h] using (map_zero f hz).symm
  | some a => simp only [toArray] at h; simp [h]

theorem array_division (p q : DensePoly E) (lead : E → E) (lead' : F → F)
    (hl : ∀ a, f (lead a) = lead' (f a)) :
    let r := divModArray p q lead
    (mapPoly f hz r.1, mapPoly f hz r.2) =
      divModArray (mapPoly f hz p) (mapPoly f hz q) lead' := by
  simp only [divModArray, map_isZero, map_size]
  split
  · simp [map_zero_poly]
  · simp only [map_array]
    have h := loop_map f hz hs hm q.toArray (q.size-1) p.size lead lead' hl
      (Array.replicate (p.size-(q.size-1)) (Zero.zero : E)) p.toArray
    simp only [Array.map_replicate, map_zero f hz] at h
    simpa only [map_ofCoeffs] using
      congrArg (fun r : Array F × Array F => (ofCoeffs r.1, ofCoeffs r.2)) h

variable [One E] [Add E] [Div E] [One F] [Add F] [Div F]
variable (hd : ∀ a b, f (a/b) = f a/f b)
include hd

/-- The actual existing division algorithm commutes with a zero-reflecting
interpretation. The map is not required to be injective. -/
theorem division (p q : DensePoly E) :
    let r := divMod p q
    (mapPoly f hz r.1, mapPoly f hz r.2) =
      divMod (mapPoly f hz p) (mapPoly f hz q) := by
  simp only [divMod, map_degree]
  split
  · simp [map_zero_poly]
  · apply array_division f hz hs hm
    intro a
    rw [hd, map_leading]

/-- info: 'Transfer.division' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms division

/-- Transfer of every iteration of the existing Euclidean loop. -/
theorem gcd_loop (p q : DensePoly E) (fuel : Nat) :
    mapPoly f hz (gcdAux p q fuel) =
      gcdAux (mapPoly f hz p) (mapPoly f hz q) fuel := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [gcdAux, map_isZero]
    split
    · rfl
    · have hr := congrArg Prod.snd (division f hz hs hm hd p q)
      change mapPoly f hz (divMod p q).2 =
        (divMod (mapPoly f hz p) (mapPoly f hz q)).2 at hr
      simpa only [hr] using ih q (divMod p q).2

/-- Transfer of the actual gcd, including its structural fuel. -/
theorem gcd_map (p q : DensePoly E) :
    mapPoly f hz (gcd p q) = gcd (mapPoly f hz p) (mapPoly f hz q) := by
  simp only [gcd, map_size]
  exact gcd_loop f hz hs hm hd p q _

/-- info: 'Transfer.gcd_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gcd_map

end Transfer
