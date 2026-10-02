/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Int.Cast.Lemmas

public section

/-!
Carrier translations for Mathlib rings.

A Mathlib `CommRing R` carries the Grind `Lean.Grind.CommRing R` instance
from `Mathlib.Algebra.Ring.GrindInstances`, so `Lean.Meta.Sym.Arith`
classifies it and the universal integer coefficient provider applies. This
module records the coefficient interpretation as a Mathlib ring homomorphism
and translates Mathlib characteristic evidence into the Grind form used by
characteristic-aware normalization.

Importing this module does not open the `HexMvPolyMathlib` scope globally. A
frontend re-synthesizes and canonicalizes its requested structures in its
actual scope; open- and closed-scope instances are distinct exact instance
identities.
-/

namespace HexReflectMathlib

open Hex.Reflect

universe u

variable {R : Type u} [CommRing R]

/-- A Mathlib ring homomorphism from a coefficient ring that agrees with the
integer cast on reflected coefficients satisfies the coefficient laws. -/
theorem coeffLaws_ofRingHom {C : Type} [Ring C] (f : C →+* R) (ofInt : Int → C)
    (h : ∀ k : Int, f (ofInt k) = (k : R)) :
    CoeffLaws (C := C) (α := R) ofInt f where
  interp_ofInt k := h k
  interp_zero := map_zero f
  interp_add a b := map_add f a b

/-- The integer cast ring homomorphism is the coefficient interpretation of
the universal integer provider on a Mathlib ring. -/
theorem coeffLaws_intCastRingHom :
    CoeffLaws (C := Int) (α := R) id (Int.castRingHom R) :=
  coeffLaws_ofRingHom (Int.castRingHom R) id fun _ => rfl

/-- The universal integer provider's interpretation is the integer cast ring
homomorphism, as a function. -/
theorem intCast_eq_intCastRingHom :
    (Int.cast : Int → R) = ⇑(Int.castRingHom R) :=
  rfl

/-- Mathlib characteristic evidence gives the Grind form used by
`Expr.toPolyC`. This helper is a theorem, not a global instance. Importing
`Mathlib.Algebra.CharP.Basic` separately supplies a global bridge for
cancellative semirings, so frontends may already obtain characteristic
evidence through instance search. This theorem also permits supplying the
Mathlib ring's exact characteristic instance explicitly. -/
theorem isCharP_of_charP (p : Nat) [CharP R p] : Lean.Grind.IsCharP R p where
  ofNat_ext_iff {x y} := by
    rw [Lean.Grind.Semiring.ofNat_eq_natCast, Lean.Grind.Semiring.ofNat_eq_natCast]
    exact CharP.cast_eq_iff_mod_eq R p

end HexReflectMathlib
