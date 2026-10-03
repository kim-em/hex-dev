/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRationalFn.Map
public import HexOrderedFn.Infinitesimal

public section

namespace Hex.RealClosure.BaseContext

variable {K L M : Type}
variable [Lean.Grind.Field K] [DecidableEq K]
variable [Lean.Grind.Field L] [DecidableEq L]
variable [Lean.Grind.Field M] [DecidableEq M]

/-- A native coefficient-field embedding. The factories derive the erased
arithmetic laws from identity, constant inclusion and coefficient transport. -/
structure FieldEmbedding (K L : Type) [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field L] [DecidableEq L] where
  private mk ::
  value : K → L
  zero : ∀ a, value a = 0 ↔ a = 0
  one : value 1 = 1
  sub : ∀ a b, value (a - b) = value a - value b
  mul : ∀ a b, value (a * b) = value a * value b
  inv : ∀ a, value a⁻¹ = (value a)⁻¹

namespace FieldEmbedding

/-- Addition follows from subtraction in the actual field dictionaries. -/
theorem add (map : FieldEmbedding K L) (a b : K) :
    map.value (a + b) = map.value a + map.value b := by
  have subtract := map.sub (a + b) b
  have cancel : a + b - b = a := by grind
  rw [cancel] at subtract
  grind

/-- Division follows from multiplication and totalized inversion. -/
theorem div (map : FieldEmbedding K L) (a b : K) :
    map.value (a / b) = map.value a / map.value b := by
  simp only [Lean.Grind.Field.div_eq_mul_inv, map.mul, map.inv]

/-- Retain the actual coefficient field. -/
def identity (K : Type) [Lean.Grind.Field K] [DecidableEq K] : FieldEmbedding K K :=
  ⟨id, fun _ => Iff.rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- Compose two native embeddings without changing their cached functions. -/
def comp (first : FieldEmbedding K L) (next : FieldEmbedding L M) : FieldEmbedding K M :=
  ⟨fun a => next.value (first.value a),
    fun a => (next.zero _).trans (first.zero a),
    by rw [first.one, next.one],
    fun a b => by rw [first.sub, next.sub],
    fun a b => by rw [first.mul, next.mul],
    fun a => by rw [first.inv, next.inv]⟩

/-- Include a field as the constants of its next rational-function field. -/
def constants (K : Type) [Lean.Grind.Field K] [DecidableEq K] :
    FieldEmbedding K (Hex.RationalFn K) :=
  ⟨Hex.RationalFn.C, Hex.RationalFn.C_eq_zero_iff, Hex.RationalFn.C_one,
    Hex.RationalFn.C_sub, Hex.RationalFn.C_mul, Hex.RationalFn.C_inv⟩

/-- Preserve one formal variable while embedding its coefficient field.
Canonical numerator and denominator transport performs no polynomial gcd. -/
def rationalFunctions (map : FieldEmbedding K L) :
    FieldEmbedding (Hex.RationalFn K) (Hex.RationalFn L) :=
  ⟨Hex.RationalFn.mapCoeffs map.value map.zero map.one map.sub map.mul map.div map.inv,
    Hex.RationalFn.mapCoeffs_eq_zero _ _ _ _ _ _ _,
    Hex.RationalFn.mapCoeffs_one _ _ _ _ _ _ _,
    Hex.RationalFn.mapCoeffs_sub _ _ _ _ _ _ _,
    Hex.RationalFn.mapCoeffs_mul _ _ _ _ _ _ _,
    Hex.RationalFn.mapCoeffs_inv _ _ _ _ _ _ _⟩

private theorem identity_value_proof (a : K) : (identity K).value a = a := rfl

private theorem comp_value_proof (first : FieldEmbedding K L) (next : FieldEmbedding L M) (a : K) :
    (first.comp next).value a = next.value (first.value a) := rfl

private theorem constants_value_proof (a : K) : (constants K).value a = Hex.RationalFn.C a := rfl

private theorem rationalFunctions_value_proof (map : FieldEmbedding K L) (a : Hex.RationalFn K) :
    map.rationalFunctions.value a =
      Hex.RationalFn.mapCoeffs map.value map.zero map.one map.sub map.mul map.div map.inv a := rfl

theorem identity_value (a : K) : (identity K).value a = a := identity_value_proof a

theorem comp_value (first : FieldEmbedding K L) (next : FieldEmbedding L M) (a : K) :
    (first.comp next).value a = next.value (first.value a) := comp_value_proof first next a

theorem constants_value (a : K) : (constants K).value a = Hex.RationalFn.C a :=
  constants_value_proof a

theorem rationalFunctions_value (map : FieldEmbedding K L) (a : Hex.RationalFn K) :
    map.rationalFunctions.value a =
      Hex.RationalFn.mapCoeffs map.value map.zero map.one map.sub map.mul map.div map.inv a :=
  rationalFunctions_value_proof map a

private theorem lowestIndex_map (map : FieldEmbedding K L) (p : Hex.DensePoly K) :
    Hex.OrderedFn.Infinitesimal.lowestIndex
      (Hex.DensePoly.Interpret.map map.value map.zero p) =
        Hex.OrderedFn.Infinitesimal.lowestIndex p := by
  unfold Hex.OrderedFn.Infinitesimal.lowestIndex
  change (Hex.DensePoly.Interpret.map map.value map.zero p).toArray.findIdx
      (fun c => c != 0) = p.toArray.findIdx (fun c => c != 0)
  rw [Hex.DensePoly.Interpret.map_array]
  have predicate : (fun c : L => c != 0) ∘ map.value = (fun c : K => c != 0) := by
    funext c
    simp only [Function.comp_apply, Lean.Grind.bne_eq_decide_not_eq, map.zero]
  unfold Array.findIdx
  rw [Array.findIdx?_map, predicate, Array.size_map]

private theorem lowestCoeff_map (map : FieldEmbedding K L) (p : Hex.DensePoly K) :
    Hex.OrderedFn.Infinitesimal.lowestCoeff
      (Hex.DensePoly.Interpret.map map.value map.zero p) =
        map.value (Hex.OrderedFn.Infinitesimal.lowestCoeff p) := by
  simp only [Hex.OrderedFn.Infinitesimal.lowestCoeff, lowestIndex_map,
    Hex.DensePoly.Interpret.map_coeff]

/-- Retaining a formal infinitesimal preserves its native sign whenever the
actual coefficient embedding preserves the predecessor signs. -/
theorem rationalFunctions_sign (map : FieldEmbedding K L)
    (sourceSign : K → Int) (targetSign : L → Int)
    (preserved : ∀ a, targetSign (map.value a) = sourceSign a)
    (a : Hex.RationalFn K) :
    Hex.OrderedFn.Infinitesimal.sign targetSign (map.rationalFunctions.value a) =
      Hex.OrderedFn.Infinitesimal.sign sourceSign a := by
  rw [rationalFunctions_value]
  unfold Hex.OrderedFn.Infinitesimal.sign
  simp only [Hex.RationalFn.mapCoeffs_num, Hex.RationalFn.mapCoeffs_den,
    Hex.DensePoly.Interpret.map_eq_zero, lowestCoeff_map, preserved]

private theorem lowestCoeff_C (a : K) :
    Hex.OrderedFn.Infinitesimal.lowestCoeff (Hex.DensePoly.C a) = a := by
  by_cases zero : a = 0
  · subst a
    have empty : Hex.DensePoly.C (0 : K) = (0 : Hex.DensePoly K) :=
      congrArg Hex.RationalFn.num (Hex.RationalFn.C_zero (K := K))
    rw [empty]
    simp only [Hex.OrderedFn.Infinitesimal.lowestCoeff]
    exact Hex.DensePoly.coeff_zero _
  · have index : Hex.OrderedFn.Infinitesimal.lowestIndex (Hex.DensePoly.C a) = 0 := by
      simp [Hex.OrderedFn.Infinitesimal.lowestIndex, Hex.DensePoly.coeffs_C_of_ne_zero zero,
        Array.findIdx, zero]
    simp only [Hex.OrderedFn.Infinitesimal.lowestCoeff, index, Hex.DensePoly.coeff_C,
      ↓reduceIte]

/-- Constant inclusion into a new infinitesimal retains each predecessor sign. -/
theorem constants_sign (baseSign : K → Int) (zero : baseSign 0 = 0)
    (one : baseSign 1 = 1) (a : K) :
    Hex.OrderedFn.Infinitesimal.sign baseSign ((constants K).value a) = baseSign a := by
  rw [constants_value]
  unfold Hex.OrderedFn.Infinitesimal.sign
  change (if Hex.DensePoly.C a = 0 then 0 else
    baseSign (Hex.OrderedFn.Infinitesimal.lowestCoeff (Hex.DensePoly.C a)) *
      baseSign (Hex.OrderedFn.Infinitesimal.lowestCoeff (1 : Hex.DensePoly K))) = baseSign a
  have unit : (1 : Hex.DensePoly K) = Hex.DensePoly.C (1 : K) := rfl
  rw [lowestCoeff_C, unit, lowestCoeff_C, one, Int.mul_one]
  by_cases empty : a = 0
  · subst a
    simp only [zero, ite_self]
  · have nonzero : Hex.DensePoly.C a ≠ 0 := by
      intro h
      apply empty
      have coefficients := congrArg (fun p : Hex.DensePoly K => p.coeff 0) h
      simpa only [Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_zero, ↓reduceIte] using coefficients
    simp only [nonzero, ↓reduceIte]

end FieldEmbedding
end Hex.RealClosure.BaseContext
