/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Degree

public section

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
  rw [DensePoly.DivModLaws.mod_add_mod ((acc % modulus) * g) (C c) modulus,
    DensePoly.DivModLaws.mod_add_mod (acc * g) (C c) modulus,
    DensePoly.DivModLaws.mod_mul_mod (acc % modulus) g modulus,
    DensePoly.DivModLaws.mod_mul_mod acc g modulus, DensePoly.mod_mod]

private theorem modByMonic_horner_step_eq
    [ZMod64.PrimeModulus p]
    (acc g modulus : FpPoly p) (c : ZMod64 p) (hmonic : DensePoly.Monic modulus) :
    modByMonic modulus (modByMonic modulus acc hmonic * g + C c) hmonic =
      modByMonic modulus (acc * g + C c) hmonic := by
  simp [modByMonic, DensePoly.modByMonic_eq_mod, mod_horner_step_eq]

/-- List-level Horner form of modular composition, reading coefficients from
low to high degree and preserving the `acc * g + C c` step orientation. The
body of the `composeModMonic` specification. -/
@[expose]
def composeModMonicList (g modulus : FpPoly p)
    (hmonic : DensePoly.Monic modulus) : List (ZMod64 p) → FpPoly p
  | [] => 0
  | c :: cs =>
      modByMonic modulus (composeModMonicList g modulus hmonic cs * g + C c) hmonic

/--
Horner-style modular composition in the quotient `F_p[x] / (modulus)`.

The reduction after each multiplication keeps the intermediate polynomials
bounded by the modulus degree while preserving the same result as composing
first and reducing once at the end.

Kernel-facing specification: one cons walk of the coefficient list. Compiled
code runs the downward `Array.foldr` loop `composeModMonicImpl` via the
`@[csimp]` proof `composeModMonic_eq_impl`. -/
@[expose]
noncomputable def composeModMonic (f g modulus : FpPoly p)
    (hmonic : DensePoly.Monic modulus) : FpPoly p :=
  composeModMonicList g modulus hmonic f.toList

/-- Runtime implementation of `composeModMonic`: a downward `Array.foldr`
Horner loop (value-equal to `composeModMonic` by `composeModMonic_eq_impl`,
registered `@[csimp]`). -/
@[expose]
def composeModMonicImpl (f g modulus : FpPoly p)
    (hmonic : DensePoly.Monic modulus) : FpPoly p :=
  f.toArray.foldr
    (fun coeff acc => modByMonic modulus (acc * g + C coeff) hmonic)
    0

/-- `composeModMonicList` is the `List.foldr` of the modular Horner step. -/
private theorem composeModMonicList_eq_foldr
    (g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus)
    (coeffs : List (ZMod64 p)) :
    composeModMonicList g modulus hmonic coeffs =
      coeffs.foldr
        (fun coeff acc => modByMonic modulus (acc * g + C coeff) hmonic)
        0 := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      simp only [composeModMonicList, List.foldr_cons]
      rw [ih]

/-- The spec `composeModMonic` and the `Array.foldr` runtime loop compute the
same polynomial. -/
theorem composeModMonic_eq_composeModMonicImpl
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic = composeModMonicImpl f g modulus hmonic := by
  unfold composeModMonic composeModMonicImpl
  rw [← Array.foldr_toList, ← composeModMonicList_eq_foldr]
  rfl

/-- Register the `Array.foldr` loop as the compiled implementation of
`composeModMonic`. -/
@[csimp]
theorem composeModMonic_eq_impl : @composeModMonic = @composeModMonicImpl := by
  funext p _ f g modulus hmonic
  exact composeModMonic_eq_composeModMonicImpl f g modulus hmonic

/-- Modular composition of the zero polynomial is `0`. -/
@[simp, grind =] theorem composeModMonic_zero
    (g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic 0 g modulus hmonic = 0 := by
  rfl

/-- Modular composition of a constant `C c` reduces `C c` modulo the monic
modulus. -/
@[simp, grind =] theorem composeModMonic_C
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
  · unfold composeModMonic
    show composeModMonicList g modulus hmonic (DensePoly.C c : FpPoly p).toList =
      modByMonic modulus (DensePoly.C c) hmonic
    rw [show (DensePoly.C c : FpPoly p).toList = [c] by
      show (DensePoly.C c : FpPoly p).coeffs.toList = [c]
      rw [DensePoly.coeffs_C_of_ne_zero hc]]
    show modByMonic modulus ((0 : FpPoly p) * g + DensePoly.C c) hmonic =
      modByMonic modulus (DensePoly.C c) hmonic
    rw [show (0 : FpPoly p) * g = 0 from rfl, zero_add]

/--
Executable modular composition agrees with ordinary dense-polynomial
composition followed by one reduction modulo the monic modulus.
-/
theorem composeModMonic_eq_modByMonic_compose
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic =
      modByMonic modulus (DensePoly.compose f g) hmonic := by
  unfold composeModMonic DensePoly.compose
  induction f.toList with
  | nil =>
      symm
      exact DensePoly.modByMonic_zero modulus hmonic
  | cons c cs ih =>
      show modByMonic modulus (composeModMonicList g modulus hmonic cs * g + C c) hmonic =
        modByMonic modulus (DensePoly.composeCoeffList cs g * g + DensePoly.C c) hmonic
      rw [ih, modByMonic_horner_step_eq]
      rfl

/--
The converse rewrite direction for `composeModMonic_eq_modByMonic_compose`.
This is useful when a proof has already produced the reduced ordinary
composition and needs to recover the executable modular-composition spelling.
-/
theorem modByMonic_compose_eq_composeModMonic
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    modByMonic modulus (DensePoly.compose f g) hmonic =
      composeModMonic f g modulus hmonic :=
  (composeModMonic_eq_modByMonic_compose f g modulus hmonic).symm

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
@[simp, grind =] theorem composeModMonic_mod_eq_self
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    composeModMonic f g modulus hmonic % modulus =
      composeModMonic f g modulus hmonic := by
  rw [composeModMonic_eq_mod, DensePoly.mod_mod]

/--
The `modByMonic` spelling of `composeModMonic_mod_eq_self`, useful for
callers that state reduction via `modByMonic` rather than `%`.
-/
@[simp, grind =] theorem modByMonic_composeModMonic_eq_self
    [ZMod64.PrimeModulus p]
    (f g modulus : FpPoly p) (hmonic : DensePoly.Monic modulus) :
    modByMonic modulus (composeModMonic f g modulus hmonic) hmonic =
      composeModMonic f g modulus hmonic := by
  simp [modByMonic, DensePoly.modByMonic_eq_mod, composeModMonic_mod_eq_self]

end FpPoly
end Hex
