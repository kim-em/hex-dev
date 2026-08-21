/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Degree

public section

/-!
Quotient representatives for executable `F_p[x] / (f)`.

This module introduces the canonical reduction function together with the
quotient-element wrapper that stores reduced representatives modulo a fixed
nonconstant polynomial.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- The degree of a polynomial, defaulting to `0` for the zero polynomial. -/
@[expose]
def degree (f : FpPoly p) : Nat :=
  f.degree?.getD 0

/-- Constant polynomials have {name}`FpPoly.degree` equal to `0`. -/
@[simp, grind =] theorem degree_C (c : ZMod64 p) : degree (C c) = 0 := by
  simp [degree, C]

end FpPoly

namespace GFqRing

variable {p : Nat} [ZMod64.Bounds p]

/-- Canonical remainder reduction modulo `f`, using the existing division surface. -/
@[expose]
def reduceMod (f : FpPoly p) : FpPoly p → FpPoly p :=
  fun g => (Hex.DensePoly.divMod g f).2

/-- A polynomial of degree strictly below the modulus is already its own canonical
representative. -/
theorem reduceMod_eq_self_of_degree_lt (f g : FpPoly p) :
    FpPoly.degree g < FpPoly.degree f → reduceMod f g = g := by
  intro hdeg
  have hdiv := DensePoly.divMod_eq_zero_self_of_degree_lt g f hdeg
  simpa [reduceMod] using congrArg Prod.snd hdiv

/-- The zero polynomial is already canonical modulo any nonconstant modulus. -/
@[simp, grind =] theorem reduceMod_zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    reduceMod f 0 = 0 := by
  exact reduceMod_eq_self_of_degree_lt f 0 hf

/-- The one polynomial is already canonical modulo any nonconstant modulus. -/
@[simp, grind =] theorem reduceMod_one (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    reduceMod f 1 = 1 := by
  have hone : FpPoly.degree (1 : FpPoly p) = 0 := by
    change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 = 0
    simp
  exact reduceMod_eq_self_of_degree_lt f 1 (by simpa [hone] using hf)

/-- Polynomials already known to be canonical representatives modulo `f`. -/
@[expose]
def IsReduced (f : FpPoly p) (g : FpPoly p) : Prop :=
  ∃ h : FpPoly p, g = reduceMod f h

/-- Executable quotient elements, carrying the reducedness invariant in the type.

A value of this type is a polynomial *together with* a proof that it lies in the
image of `reduceMod f`, so a raw `FpPoly p` cannot be supplied where one of these
is expected.

The modulus is required to be prime, which guarantees the representative is
canonical for every nonconstant `f`: `reduceMod` is a genuine remainder only
when the leading coefficient it divides by is a unit, and over a prime modulus
every nonzero coefficient is. Drop the hypothesis and canonicality can fail. At
`p = 4` with `f = 2X` the division step subtracts zero and leaves the remainder
untouched, so `f` and `0` are congruent yet both reduced and distinct.
`isReduced_iff_degree_lt` states the contract this hypothesis buys.

Primality is sufficient, not necessary: a monic `f` needs no coefficient
inversion and would be canonical over any modulus. The uniform prime hypothesis
is the deliberate choice here, since every modulus this library serves is over a
prime field anyway.

`reduceMod` itself, and its degree-short-circuit lemmas above, stay general; it
is the quotient *type* that is restricted, because that is what carries the
canonicality claim. -/
abbrev PolyQuotient [ZMod64.PrimeModulus p] (f : FpPoly p) (_hf : 0 < FpPoly.degree f) :=
  { g : FpPoly p // IsReduced f g }

variable [ZMod64.PrimeModulus p]

/-- Inject a polynomial into the quotient by reducing it modulo `f`. -/
@[expose]
def ofPoly (f : FpPoly p) (hf : 0 < FpPoly.degree f) (g : FpPoly p) :
    PolyQuotient f hf :=
  ⟨reduceMod f g, ⟨g, rfl⟩⟩

/-- Project a quotient element to its canonical polynomial representative. -/
@[expose]
def repr {f : FpPoly p} {hf : 0 < FpPoly.degree f} (x : PolyQuotient f hf) : FpPoly p :=
  x.1

/-- Quotient elements have decidable equality by comparing their canonical representatives. -/
instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : DecidableEq (PolyQuotient f hf) := by
  intro x y
  match decEq x.1 y.1 with
  | isTrue h => exact isTrue (Subtype.ext h)
  | isFalse h => exact isFalse (fun hxy => h (congrArg Subtype.val hxy))

/-- The canonical representative of `ofPoly f hf g` is `reduceMod f g`. -/
@[simp, grind =] theorem repr_ofPoly (f : FpPoly p) (hf : 0 < FpPoly.degree f) (g : FpPoly p) :
    repr (ofPoly f hf g) = reduceMod f g :=
  rfl

/-- Two quotient elements are equal whenever their canonical representatives agree. -/
@[ext] theorem ext
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    {x y : PolyQuotient f hf} (h : repr x = repr y) :
    x = y :=
  Subtype.ext h

/-- A quotient element equals the canonical zero iff its representative reduces to zero. -/
@[simp] theorem eq_zero_iff_repr_eq_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    x = ofPoly f hf 0 ↔ repr x = reduceMod f 0 := by
  constructor
  · intro hx
    simp [hx]
  · intro hx
    apply ext
    simpa using hx

/-- A quotient element differs from the canonical zero iff its representative reduces nonzero. -/
@[simp] theorem ne_zero_iff_repr_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    x ≠ ofPoly f hf 0 ↔ repr x ≠ reduceMod f 0 := by
  constructor
  · intro hx hrepr
    exact hx ((eq_zero_iff_repr_eq_zero x).2 hrepr)
  · intro hx hzero
    exact hx ((eq_zero_iff_repr_eq_zero x).1 hzero)

/-- Canonical representatives have degree strictly below the modulus. -/
@[simp] theorem degree_repr_lt_degree {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    FpPoly.degree (repr x) < FpPoly.degree f := by
  rcases x.2 with ⟨g, hx⟩
  simpa [repr, hx, IsReduced, reduceMod, FpPoly.degree, DensePoly.mod_eq_divMod]
    using DensePoly.mod_degree_lt_of_pos_degree g f hf

/-- Reducedness is exactly a degree bound, so the representative a
{name}`PolyQuotient` stores is the unique one of its residue class.

This is the theorem behind the "equality is equality of canonical
representatives" contract, and it is where primality is load-bearing. The
forward direction is the one that needs it: a reduced polynomial is only known
to sit below the modulus because the remainder-degree law holds over a field,
and that law is what fails when the leading coefficient of `f` is not a unit.
The converse is `reduceMod_eq_self_of_degree_lt`, which holds generally. -/
theorem isReduced_iff_degree_lt {f : FpPoly p} (hf : 0 < FpPoly.degree f)
    (g : FpPoly p) :
    IsReduced f g ↔ FpPoly.degree g < FpPoly.degree f := by
  constructor
  · rintro ⟨h, rfl⟩
    simpa [IsReduced, reduceMod, FpPoly.degree, DensePoly.mod_eq_divMod]
      using DensePoly.mod_degree_lt_of_pos_degree h f hf
  · intro hdeg
    exact ⟨g, (reduceMod_eq_self_of_degree_lt f g hdeg).symm⟩

/-- Applying {name}`reduceMod` to a reduced representative is a no-op. -/
@[simp, grind =] theorem reduceMod_idem (f : FpPoly p) (g : FpPoly p) :
    reduceMod f (reduceMod f g) = reduceMod f g := by
  simpa [reduceMod, DensePoly.mod_eq_divMod] using (DensePoly.mod_mod g f)

/-- The modulus itself reduces to the zero representative modulo itself. -/
@[simp, grind =] theorem reduceMod_self (f : FpPoly p) :
    reduceMod f f = 0 := by
  change (DensePoly.divMod f f).2 = 0
  simpa [DensePoly.mod_eq_divMod] using
    (DensePoly.DivModLaws.mod_self_eq_zero f)

/-- Reducing both summands before quotient reduction preserves the canonical representative. -/
theorem reduceMod_add_reduceMod_congr (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a + b) = reduceMod f (reduceMod f a + reduceMod f b) := by
  simpa [reduceMod, DensePoly.mod_eq_divMod] using
    (DensePoly.DivModLaws.mod_add_mod a b f)

/-- Reducing the left summand before quotient reduction preserves the representative. -/
@[simp, grind =] theorem reduceMod_add_left_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (reduceMod f a + b) = reduceMod f (a + b) := by
  calc
    reduceMod f (reduceMod f a + b)
        = reduceMod f (reduceMod f (reduceMod f a) + reduceMod f b) := by
          exact reduceMod_add_reduceMod_congr f (reduceMod f a) b
    _ = reduceMod f (reduceMod f a + reduceMod f b) := by
          simp [reduceMod_idem]
    _ = reduceMod f (a + b) := by
          exact (reduceMod_add_reduceMod_congr f a b).symm

/-- Reducing the right summand before quotient reduction preserves the representative. -/
@[simp, grind =] theorem reduceMod_add_right_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a + reduceMod f b) = reduceMod f (a + b) := by
  calc
    reduceMod f (a + reduceMod f b)
        = reduceMod f (reduceMod f a + reduceMod f (reduceMod f b)) := by
          exact reduceMod_add_reduceMod_congr f a (reduceMod f b)
    _ = reduceMod f (reduceMod f a + reduceMod f b) := by
          simp [reduceMod_idem]
    _ = reduceMod f (a + b) := by
          exact (reduceMod_add_reduceMod_congr f a b).symm

/-- Reducing both factors before quotient reduction preserves the canonical representative. -/
theorem reduceMod_mul_reduceMod_congr (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a * b) = reduceMod f (reduceMod f a * reduceMod f b) := by
  simpa [reduceMod, DensePoly.mod_eq_divMod] using
    (DensePoly.DivModLaws.mod_mul_mod a b f)

/-- Reducing the left factor before quotient reduction preserves the representative. -/
@[simp, grind =] theorem reduceMod_mul_left_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (reduceMod f a * b) = reduceMod f (a * b) := by
  calc
    reduceMod f (reduceMod f a * b)
        = reduceMod f (reduceMod f (reduceMod f a) * reduceMod f b) := by
          exact reduceMod_mul_reduceMod_congr f (reduceMod f a) b
    _ = reduceMod f (reduceMod f a * reduceMod f b) := by
          simp [reduceMod_idem]
    _ = reduceMod f (a * b) := by
          exact (reduceMod_mul_reduceMod_congr f a b).symm

/-- Reducing the right factor before quotient reduction preserves the representative. -/
@[simp, grind =] theorem reduceMod_mul_right_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a * reduceMod f b) = reduceMod f (a * b) := by
  calc
    reduceMod f (a * reduceMod f b)
        = reduceMod f (reduceMod f a * reduceMod f (reduceMod f b)) := by
          exact reduceMod_mul_reduceMod_congr f a (reduceMod f b)
    _ = reduceMod f (reduceMod f a * reduceMod f b) := by
          simp [reduceMod_idem]
    _ = reduceMod f (a * b) := by
          exact (reduceMod_mul_reduceMod_congr f a b).symm

/-- Adding a right multiple of the modulus does not change the canonical representative. -/
theorem reduceMod_add_mul_self_right (f : FpPoly p) (hf : 0 < FpPoly.degree f)
    (q r : FpPoly p) :
    reduceMod f (q + r * f) = reduceMod f q := by
  calc
    reduceMod f (q + r * f)
        = reduceMod f (q + reduceMod f (r * f)) := by
          exact (reduceMod_add_right_reduceMod f q (r * f)).symm
    _ = reduceMod f (q + reduceMod f (f * r)) := by
          rw [FpPoly.mul_comm r f]
    _ = reduceMod f (q + reduceMod f (reduceMod f f * r)) := by
          rw [reduceMod_mul_left_reduceMod]
    _ = reduceMod f (q + reduceMod f (0 * r)) := by
          rw [reduceMod_self]
    _ = reduceMod f (q + reduceMod f 0) := by
          rw [FpPoly.zero_mul]
    _ = reduceMod f q := by
          simp [reduceMod_zero f hf, FpPoly.add_zero]

/-- Reducing the argument before applying {name}`ofPoly` does not change the resulting quotient
element. -/
@[simp, grind =] theorem ofPoly_reduceMod (f : FpPoly p) (hf : 0 < FpPoly.degree f) (g : FpPoly p) :
    ofPoly f hf (reduceMod f g) = ofPoly f hf g := by
  apply Subtype.ext
  simp [ofPoly, reduceMod_idem]

end GFqRing
end Hex
