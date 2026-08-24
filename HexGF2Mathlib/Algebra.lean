/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2Mathlib.Field
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.RingTheory.EuclideanDomain

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

namespace GF2Poly

/-- The Euclidean rank of a packed polynomial. Zero has rank zero and a
nonzero polynomial has rank one greater than its degree. -/
def euclideanRank (p : Hex.GF2Poly) : Nat :=
  if p = 0 then 0 else p.degree + 1

@[simp] theorem euclideanRank_zero : euclideanRank 0 = 0 := by
  simp [euclideanRank]

@[simp] theorem euclideanRank_of_ne_zero {p : Hex.GF2Poly} (hp : p ≠ 0) :
    euclideanRank p = p.degree + 1 := by
  simp [euclideanRank, hp]

/-- The packed `F₂[x]` representation is a Euclidean domain whose quotient and
remainder are the executable long-division operations from `hex-gf2`. -/
instance euclideanDomain : EuclideanDomain Hex.GF2Poly where
  toCommRing := commRing
  toNontrivial := ⟨0, 1, fun h => Hex.GF2Poly.one_ne_zero h.symm⟩
  quotient := Hex.GF2Poly.div
  quotient_zero := Hex.GF2Poly.div_zero_right
  remainder := Hex.GF2Poly.mod
  quotient_mul_add_remainder_eq := fun p q => by
    rw [mul_comm]
    exact Hex.GF2Poly.div_mul_add_mod p q
  r := fun p q => euclideanRank p < euclideanRank q
  r_wellFounded := (measure euclideanRank).wf
  remainder_lt := fun p q hq => by
    rw [euclideanRank_of_ne_zero hq]
    rcases Hex.GF2Poly.mod_degree_lt p q hq with hzero | hdegree
    · change (Hex.GF2Poly.mod p q).isZero = true at hzero
      rw [(Hex.GF2Poly.isZero_iff_eq_zero _).mp hzero, euclideanRank_zero]
      omega
    · change (Hex.GF2Poly.mod p q).degree < q.degree at hdegree
      by_cases hrem : Hex.GF2Poly.mod p q = 0
      · rw [hrem, euclideanRank_zero]
        omega
      · rw [euclideanRank_of_ne_zero hrem]
        omega
  mul_left_not_lt := fun p q hq => by
    by_cases hp : p = 0
    · simp [hp]
    · rw [euclideanRank_of_ne_zero hp]
      have hpzero : p.isZero = false :=
        (Hex.GF2Poly.isZero_eq_false_iff_ne_zero p).mpr hp
      have hqzero : q.isZero = false :=
        (Hex.GF2Poly.isZero_eq_false_iff_ne_zero q).mpr hq
      obtain ⟨dp, hdp⟩ :=
        Hex.GF2Poly.degree?_isSome_of_isZero_false hpzero
      obtain ⟨dq, hdq⟩ :=
        Hex.GF2Poly.degree?_isSome_of_isZero_false hqzero
      have hpqdeg : (p * q).degree? = some (dp + dq) :=
        Hex.GF2Poly.degree?_mul_of_degree?_eq_some hdp hdq
      have hpq : p * q ≠ 0 := by
        intro hpq
        rw [hpq] at hpqdeg
        simp [Hex.GF2Poly.degree?] at hpqdeg
      rw [euclideanRank_of_ne_zero hpq,
        Hex.GF2Poly.degree_eq_of_degree?_eq_some hdp,
        Hex.GF2Poly.degree_eq_of_degree?_eq_some hpqdeg]
      omega

/-- The gcd-domain interface uses the packed executable gcd, not Mathlib's
separate recursive Euclidean-domain implementation. -/
noncomputable instance gcdMonoid : GCDMonoid Hex.GF2Poly :=
  gcdMonoidOfGCD Hex.GF2Poly.gcd
    Hex.GF2Poly.gcd_dvd_left
    Hex.GF2Poly.gcd_dvd_right
    (fun hdleft hdright => Hex.GF2Poly.dvd_gcd _ _ _ hdleft hdright)

/-- Mathlib's gcd operation on packed polynomials is definitionally the
executable `hex-gf2` gcd. -/
theorem gcd_eq_packed (p q : Hex.GF2Poly) :
    GCDMonoid.gcd p q = Hex.GF2Poly.gcd p q :=
  rfl

/-- Mathlib's recursive Euclidean gcd agrees with the executable packed gcd.
Over `F₂[x]`, mutual divisibility determines equality because `1` is the only
unit. -/
theorem euclidean_gcd_eq_packed (p q : Hex.GF2Poly) :
    EuclideanDomain.gcd p q = Hex.GF2Poly.gcd p q := by
  apply Hex.GF2Poly.dvd_antisymm
  · exact Hex.GF2Poly.dvd_gcd _ _ _
      (EuclideanDomain.gcd_dvd_left p q)
      (EuclideanDomain.gcd_dvd_right p q)
  · exact EuclideanDomain.dvd_gcd
      (Hex.GF2Poly.gcd_dvd_left p q)
      (Hex.GF2Poly.gcd_dvd_right p q)

end GF2Poly

namespace GF2n

variable {n : Nat} {irr : UInt64}
variable {hn : 0 < n} {hn64 : n < 64}
variable {hirr : Hex.GF2Poly.Irreducible (Hex.GF2Poly.ofUInt64Monic irr n)}

/-- The packed single-word quotient is a Mathlib field, with its executable
core operations retained. Its positive extension degree is part of the type,
so unlike `GF2nPoly` it needs no extra nontriviality hypothesis. -/
noncomputable instance field : Field (Hex.GF2n n irr hn hn64 hirr) :=
  Field.ofMinimalAxioms (Hex.GF2n n irr hn hn64 hirr)
    Hex.GF2n.add_assoc
    Hex.GF2n.zero_add
    Hex.GF2n.neg_add_cancel
    Hex.GF2n.mul_assoc
    Hex.GF2n.mul_comm
    Hex.GF2n.one_mul
    Hex.GF2n.mul_inv_cancel
    Hex.GF2n.inv_zero
    Hex.GF2n.left_distrib
    ⟨1, 0, Hex.GF2n.one_ne_zero⟩

/-! # The instance is usable, and keeps the executable core operations -/

section Checks

/-- The single-word field instance keeps the executable operations named by
the computational API. -/
example (a b : Hex.GF2n n irr hn hn64 hirr) :
    a * b = Hex.GF2n.mul a b ∧ -a = Hex.GF2n.neg a ∧
      a - b = Hex.GF2n.sub a b ∧ a⁻¹ = Hex.GF2n.inv a ∧
      a / b = Hex.GF2n.div a b := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The single-word instance reaches Mathlib's field lemmas directly. -/
example (a : Hex.GF2n n irr hn hn64 hirr) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha

end Checks

end GF2n

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

/-! # The instances are usable -/

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

/-- Euclidean division and remainder remain the executable packed operations. -/
example (p q : Hex.GF2Poly) :
    p / q = Hex.GF2Poly.div p q ∧ p % q = Hex.GF2Poly.mod p q :=
  ⟨rfl, rfl⟩

/-- The packed gcd is also the operation exposed through Mathlib's gcd-domain
interface. -/
example (p q : Hex.GF2Poly) :
    GCDMonoid.gcd p q = Hex.GF2Poly.gcd p q :=
  GF2Poly.gcd_eq_packed p q

/-- Mathlib's recursive Euclidean gcd is the packed gcd as well. -/
example (p q : Hex.GF2Poly) :
    EuclideanDomain.gcd p q = Hex.GF2Poly.gcd p q :=
  GF2Poly.euclidean_gcd_eq_packed p q

/-- The Euclidean-domain instance reaches Mathlib's unique-factorization
interface. -/
example : UniqueFactorizationMonoid Hex.GF2Poly := inferInstance

/-- Principal-ideal and Bezout interfaces are also synthesized from the
Euclidean-domain instance. -/
example : IsPrincipalIdealRing Hex.GF2Poly := inferInstance
example : IsBezout Hex.GF2Poly := inferInstance

/-- The field instance is found by synthesis given the degree fact, and its
inverse is still the executable one. -/
example {f : Hex.GF2Poly} {hirr : Hex.GF2Poly.Irreducible f}
    [Fact (0 < f.degree)] (a : Hex.GF2nPoly f hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha

end Checks

end GF2nPoly

end HexGF2Mathlib
