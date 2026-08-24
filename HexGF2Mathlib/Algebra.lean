/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2Mathlib.Field
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.Algebra.Field.MinimalAxioms

public section

/-!
Mathlib algebraic structure on the packed `hex-gf2` types.

`SPEC/design-principles.md` principle 2 puts Mathlib typeclass instances on an
executable type in the `*-mathlib` companion. The instances here are built from
the laws `hex-gf2` already proves, through Mathlib's minimal-axioms
constructors, so the ring and field operations stay the executable ones: `*` on
a `CommRing Hex.GF2Poly` is still packed carry-less multiplication, not a
transported copy of it. Building them by transport along
{name}`HexGF2Mathlib.GF2Poly.equiv` instead would give the right laws attached
to the wrong operations.
-/

namespace HexGF2Mathlib

open Hex

/-- The packed `F₂[x]` representation is a Mathlib commutative ring, with the
executable packed operations. -/
instance commRing : CommRing Hex.GF2Poly :=
  CommRing.ofMinimalAxioms
    Hex.GF2Poly.add_assoc
    Hex.GF2Poly.zero_add
    Hex.GF2Poly.neg_add_cancel
    Hex.GF2Poly.mul_assoc
    Hex.GF2Poly.mul_comm
    Hex.GF2Poly.one_mul
    -- `Hex.GF2Poly.left_distrib` is in fact the right-distributive law
    -- `(p + r) * q = p * q + r * q`; commutativity turns it into the one
    -- Mathlib asks for here.
    (fun a b c => by
      rw [Hex.GF2Poly.mul_comm a (b + c), Hex.GF2Poly.left_distrib,
        Hex.GF2Poly.mul_comm b a, Hex.GF2Poly.mul_comm c a])

namespace GF2nPoly

variable {f : Hex.GF2Poly} {hirr : Hex.GF2Poly.Irreducible f}

/-- The packed quotient is a Mathlib field once the modulus is nonconstant.

The degree hypothesis is not redundant. `Hex.GF2Poly.Irreducible` asks that `f`
be nonzero with no factorization into two positive-degree parts, which the
constant `1` satisfies, and `Hex.GF2nPoly 1 _` is the trivial ring where
`0 = 1`. Carried as a `Fact` so that instance synthesis can find it: a caller
with a genuine modulus supplies it once, and the committed packed entries in
`hex-gfq` carry `degree_pos` to build it from. -/
noncomputable instance field [hdeg : Fact (0 < f.degree)] :
    Field (Hex.GF2nPoly f hirr) :=
  Field.ofMinimalAxioms (Hex.GF2nPoly f hirr)
    Hex.GF2nPoly.add_assoc
    Hex.GF2nPoly.zero_add
    (fun a => by
      show a + a = 0
      exact Hex.GF2nPoly.add_self a)
    Hex.GF2nPoly.mul_assoc
    Hex.GF2nPoly.mul_comm
    Hex.GF2nPoly.one_mul
    Hex.GF2nPoly.mul_inv_cancel
    Hex.GF2nPoly.inv_zero
    Hex.GF2nPoly.left_distrib
    ⟨1, 0, Hex.GF2nPoly.one_ne_zero hdeg.out⟩

/-! # The instances are usable, and keep the executable operations -/

section Checks

open Hex

/-- The `CommRing` reaches Mathlib's general ring lemmas. -/
example (p q : Hex.GF2Poly) : (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by
  ring

/-- Multiplication under the `CommRing` is still the executable packed product,
not a transported copy: this closes by `rfl`. -/
example (p q : Hex.GF2Poly) : p * q = Hex.GF2Poly.mul p q := rfl

/-- Addition likewise. -/
example (p q : Hex.GF2Poly) : p + q = Hex.GF2Poly.add p q := rfl

/-- The field instance is found by synthesis given the degree fact, and its
inverse is still the executable one. -/
example {f : Hex.GF2Poly} {hirr : Hex.GF2Poly.Irreducible f}
    [Fact (0 < f.degree)] (a : Hex.GF2nPoly f hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha

end Checks

end GF2nPoly

end HexGF2Mathlib
