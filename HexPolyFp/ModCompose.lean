import HexPolyFp.Basic

/-!
Modular composition in `F_p[x]`.

This module evaluates one executable dense polynomial at another while reducing
modulo a monic modulus after each Horner step. Downstream finite-field
algorithms use this API as the executable quotient-ring composition primitive.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

private theorem mod_horner_step_eq
    [ZMod64.PrimeModulus p]
    (acc g modulus : FpPoly p) (c : ZMod64 p) :
    ((acc % modulus) * g + C c) % modulus = (acc * g + C c) % modulus := by
  rw [DensePoly.DivModLaws.mod_add_mod ((acc % modulus) * g) (C c) modulus]
  rw [DensePoly.DivModLaws.mod_add_mod (acc * g) (C c) modulus]
  rw [DensePoly.DivModLaws.mod_mul_mod (acc % modulus) g modulus]
  rw [DensePoly.DivModLaws.mod_mul_mod acc g modulus]
  rw [DensePoly.mod_mod]

private theorem modByMonic_horner_step_eq
    [ZMod64.PrimeModulus p]
    (acc g modulus : FpPoly p) (c : ZMod64 p) (hmonic : DensePoly.Monic modulus) :
    modByMonic modulus (modByMonic modulus acc hmonic * g + C c) hmonic =
      modByMonic modulus (acc * g + C c) hmonic := by
  simp [modByMonic, DensePoly.modByMonic_eq_mod, mod_horner_step_eq]

private theorem composeModMonic_fold_eq_mod
    [ZMod64.PrimeModulus p]
    (coeffs : List (ZMod64 p)) (init g modulus : FpPoly p)
    (hmonic : DensePoly.Monic modulus) :
    coeffs.foldl
        (fun acc coeff => modByMonic modulus (acc * g + C coeff) hmonic)
        (modByMonic modulus init hmonic) =
      modByMonic modulus
        (coeffs.foldl (fun acc coeff => acc * g + C coeff) init) hmonic := by
  induction coeffs generalizing init with
  | nil =>
      rfl
  | cons coeff coeffs ih =>
      simp only [List.foldl_cons]
      rw [modByMonic_horner_step_eq]
      exact ih (init * g + C coeff)

/--
Horner-style modular composition in the quotient `F_p[x] / (modulus)`.

The reduction after each multiplication keeps the intermediate polynomials
bounded by the modulus degree while preserving the same result as composing
first and reducing once at the end.
-/
def composeModMonic (f g modulus : FpPoly p)
    (hmonic : DensePoly.Monic modulus) : FpPoly p :=
  f.toArray.toList.reverse.foldl
    (fun acc coeff => modByMonic modulus (acc * g + C coeff) hmonic)
    0

@[simp] theorem composeModMonic_zero
    (g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic 0 g modulus hmonic = 0 := by
  rfl

@[simp] theorem composeModMonic_C
    (c : ZMod64 p) (g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic (C c) g modulus hmonic = modByMonic modulus (C c) hmonic := by
  by_cases hc : c = 0
  · subst c
    change Array.foldr (fun x y => modByMonic modulus (y * g + C x) hmonic) 0
        (DensePoly.C (0 : ZMod64 p)).coeffs =
      modByMonic modulus (DensePoly.C (0 : ZMod64 p)) hmonic
    rw [show (DensePoly.C (0 : ZMod64 p) : FpPoly p).coeffs = #[] by
      exact DensePoly.coeffs_C_zero]
    change 0 = modByMonic modulus (0 : FpPoly p) hmonic
    change 0 = DensePoly.modByMonic (0 : FpPoly p) modulus hmonic
    rw [DensePoly.modByMonic_zero]
  · simp [composeModMonic, C, DensePoly.toArray, DensePoly.coeffs_C_of_ne_zero hc, zero_add]

/--
Executable modular composition agrees with ordinary dense-polynomial
composition followed by one reduction modulo the monic modulus.
-/
theorem composeModMonic_eq_modByMonic_compose
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic =
      modByMonic modulus (DensePoly.compose f g) hmonic := by
  rw [composeModMonic, DensePoly.compose]
  have hfold :=
    composeModMonic_fold_eq_mod
      (f.toArray.toList.reverse) (0 : FpPoly p) g modulus hmonic
  have hzero : modByMonic modulus (0 : FpPoly p) hmonic = 0 :=
    DensePoly.modByMonic_zero modulus hmonic
  rw [hzero] at hfold
  exact hfold

/--
Executable modular composition agrees with `DensePoly.compose f g % modulus`,
the quotient-ring spelling preferred by downstream callers that reason with
`%` rather than `modByMonic`.
-/
theorem composeModMonic_eq_mod
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic = DensePoly.compose f g % modulus := by
  rw [composeModMonic_eq_modByMonic_compose]
  exact DensePoly.modByMonic_eq_mod (DensePoly.compose f g) modulus hmonic

/-- The result of `composeModMonic` is already reduced modulo the monic modulus. -/
@[simp] theorem composeModMonic_mod_eq_self
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic % modulus =
      composeModMonic f g modulus hmonic := by
  rw [composeModMonic_eq_mod, DensePoly.mod_mod]

/--
The `modByMonic` spelling of `composeModMonic_mod_eq_self`, useful for
callers that state reduction via `modByMonic` rather than `%`.
-/
@[simp] theorem modByMonic_composeModMonic_eq_self
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    modByMonic modulus (composeModMonic f g modulus hmonic) hmonic =
      composeModMonic f g modulus hmonic := by
  simp [modByMonic, DensePoly.modByMonic_eq_mod, composeModMonic_mod_eq_self]

end FpPoly
end Hex
