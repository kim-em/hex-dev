/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Basic
public import HexPolyFpMathlib.Basic
public import HexModArithMathlib.ZMod64Equiv
public import HexConway.Compatibility
public import Mathlib.Algebra.Polynomial.Eval.Defs

public section

/-!
Ring homomorphisms into the executable finite field, and the canonical subfield
embedding they build.

`hex-conway` proves that the norm of the generator of `F_p[x] / (C(p, n))` down
to the degree-`m` subfield is a root of `C(p, m)`. This file turns that fact
into the map it is evidence for: a ring homomorphism `GFq p m →+* GFq p n` for
`m ∣ n`.

The multiplicative content is Mathlib's, not ours. `Polynomial.eval₂RingHom` is
a ring homomorphism by construction, so substituting the norm element into a
polynomial is automatically multiplicative. What the Hex side has to supply is
only that the executable substitution agrees with it, and that is additive and
monomial data.
-/

namespace HexGFqMathlib

open Hex

variable {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]

/-- Reduction into the executable finite field is a ring homomorphism.

The component facts live on the quotient-ring layer; this bundles them so that
Mathlib constructions needing a `RingHom` can be pointed at the executable
field. -/
@[expose]
def ofPolyHom (f : Hex.FpPoly p) (hf : 0 < Hex.FpPoly.degree f)
    (hp : Hex.Nat.Prime p) (hirr : Hex.FpPoly.Irreducible f) :
    Hex.FpPoly p →+* Hex.GFqField.FiniteField f hf hp hirr where
  toFun := Hex.GFqField.ofPoly f hf hp hirr
  map_one' := by
    apply Hex.GFqField.ext
    apply Hex.GFqRing.ext
    show Hex.GFqField.repr (Hex.GFqField.ofPoly f hf hp hirr 1) =
      Hex.GFqField.repr (1 : Hex.GFqField.FiniteField f hf hp hirr)
    rw [Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_one]
  map_zero' := by
    apply Hex.GFqField.ext
    apply Hex.GFqRing.ext
    show Hex.GFqField.repr (Hex.GFqField.ofPoly f hf hp hirr 0) =
      Hex.GFqField.repr (0 : Hex.GFqField.FiniteField f hf hp hirr)
    rw [Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_zero]
  map_add' a b := by
    apply Hex.GFqField.ext
    apply Hex.GFqRing.ext
    show Hex.GFqField.repr (Hex.GFqField.ofPoly f hf hp hirr (a + b)) =
      Hex.GFqField.repr
        (Hex.GFqField.ofPoly f hf hp hirr a + Hex.GFqField.ofPoly f hf hp hirr b)
    rw [Hex.GFqField.repr_add, Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_ofPoly,
      Hex.GFqField.repr_ofPoly]
    exact Hex.GFqRing.reduceMod_add_reduceMod_congr f a b
  map_mul' a b := by
    apply Hex.GFqField.ext
    apply Hex.GFqRing.ext
    show Hex.GFqField.repr (Hex.GFqField.ofPoly f hf hp hirr (a * b)) =
      Hex.GFqField.repr
        (Hex.GFqField.ofPoly f hf hp hirr a * Hex.GFqField.ofPoly f hf hp hirr b)
    rw [Hex.GFqField.repr_mul, Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_ofPoly,
      Hex.GFqField.repr_ofPoly]
    exact Hex.GFqRing.reduceMod_mul_reduceMod_congr f a b

@[simp] theorem ofPolyHom_apply
    {f : Hex.FpPoly p} {hf : 0 < Hex.FpPoly.degree f}
    {hp : Hex.Nat.Prime p} {hirr : Hex.FpPoly.Irreducible f} (g : Hex.FpPoly p) :
    ofPolyHom f hf hp hirr g = Hex.GFqField.ofPoly f hf hp hirr g :=
  rfl

open HexModArithMathlib.ZMod64 in
omit [Hex.ZMod64.PrimeModulus p] in
/-- `toZMod` is injective, since `ofZMod` inverts it. -/
private theorem toZMod_injective {a b : Hex.ZMod64 p} (h : toZMod a = toZMod b) :
    a = b := by
  rw [← ofZMod_toZMod a, ← ofZMod_toZMod b, h]

open HexModArithMathlib.ZMod64 in
omit [Hex.ZMod64.PrimeModulus p] in
/-- The inverse coefficient map is additive. Derived from `toZMod_add`; the
`≃+*` bundling cannot be used directly here because `Hex.ZMod64 p` has no
Mathlib `NonAssocSemiring`, so the hom classes do not apply to it. -/
private theorem ofZMod_add (a b : ZMod p) :
    ofZMod (p := p) (a + b) = ofZMod a + ofZMod b := by
  apply toZMod_injective
  rw [toZMod_add, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

open HexModArithMathlib.ZMod64 in
omit [Hex.ZMod64.PrimeModulus p] in
/-- The inverse coefficient map is multiplicative. -/
private theorem ofZMod_mul (a b : ZMod p) :
    ofZMod (p := p) (a * b) = ofZMod a * ofZMod b := by
  apply toZMod_injective
  rw [toZMod_mul, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

open HexModArithMathlib.ZMod64 in
/-- The constant embedding `ZMod p →+* FpPoly p`, routing Mathlib's coefficient
ring through the executable `ZMod64 p`. -/
def constPolyHom : ZMod p →+* Hex.FpPoly p where
  toFun c := Hex.DensePoly.C (ofZMod (p := p) c)
  map_one' := by
    show (Hex.DensePoly.C (ofZMod (p := p) (1 : ZMod p)) : Hex.FpPoly p) = 1
    rw [ofZMod_one]
    rfl
  map_zero' := by
    show (Hex.DensePoly.C (ofZMod (p := p) (0 : ZMod p)) : Hex.FpPoly p) = 0
    rw [ofZMod_zero]
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_zero]
    split <;> rfl
  map_add' a b := by
    show (Hex.DensePoly.C (ofZMod (p := p) (a + b)) : Hex.FpPoly p) = _
    rw [ofZMod_add]
    exact Hex.FpPoly.C_add_eq _ _
  map_mul' a b := by
    show (Hex.DensePoly.C (ofZMod (p := p) (a * b)) : Hex.FpPoly p) = _
    rw [ofZMod_mul]
    exact Hex.FpPoly.C_mul_C_eq _ _

/-- Constants of the executable finite field, as a ring homomorphism from
Mathlib's coefficient ring. This is what instantiates
`Polynomial.eval₂RingHom`. -/
noncomputable def constHom (f : Hex.FpPoly p) (hf : 0 < Hex.FpPoly.degree f)
    (hp : Hex.Nat.Prime p) (hirr : Hex.FpPoly.Irreducible f) :
    ZMod p →+* Hex.GFqField.FiniteField f hf hp hirr :=
  (ofPolyHom f hf hp hirr).comp constPolyHom

/-! # Executable substitution is Mathlib's evaluation

`Polynomial.eval₂RingHom` is a ring homomorphism by construction. Identifying
it with the executable `DensePoly.compose` is what lets that multiplicativity
be used on Hex's side, and by `Polynomial.induction_on'` the identification
needs only the additive and monomial cases.
-/

variable {f : Hex.FpPoly p} {hf : 0 < Hex.FpPoly.degree f}
variable {hp : Hex.Nat.Prime p} {hirr : Hex.FpPoly.Irreducible f}

/-- Substituting `b` and reducing agrees with evaluating at the reduction of
`b`, for every polynomial. -/
theorem ofPolyHom_compose_eq_eval₂ (b : Hex.FpPoly p) (g : Hex.FpPoly p) :
    ofPolyHom f hf hp hirr (Hex.DensePoly.compose g b) =
      Polynomial.eval₂ (constHom f hf hp hirr) (ofPolyHom f hf hp hirr b)
        (HexPolyFpMathlib.fpPolyEquiv g) := by
  have key : ∀ P : Polynomial (ZMod p),
      ofPolyHom f hf hp hirr
          (Hex.DensePoly.compose (HexPolyFpMathlib.fpPolyEquiv.symm P) b) =
        Polynomial.eval₂ (constHom f hf hp hirr) (ofPolyHom f hf hp hirr b) P := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        rw [map_add, Hex.FpPoly.compose_add, map_add, hP, hQ, Polynomial.eval₂_add]
    | monomial k c =>
        rw [Polynomial.eval₂_monomial]
        rw [HexPolyFpMathlib.fpPolyEquiv_symm_apply,
          HexPolyFpMathlib.polynomialToFpPoly_monomial,
          Hex.FpPoly.compose_monomial, HexPolyFpMathlib.linearPow_eq_pow,
          map_mul, map_pow]
        rfl
  have := key (HexPolyFpMathlib.fpPolyEquiv g)
  rwa [RingEquiv.symm_apply_apply] at this

/-! # The canonical subfield embedding

Substituting the norm element is a ring homomorphism out of the polynomials,
because `Polynomial.eval₂RingHom` is. It descends to the degree-`m` field
because that homomorphism kills `C(p, m)`, which is exactly Tier 2
compatibility.
-/

/-- Substitution into the executable field, as a ring homomorphism out of the
executable polynomials: `g ↦ g(b)` in `F_p[x] / (f)`. -/
noncomputable def substHom (f : Hex.FpPoly p) (hf : 0 < Hex.FpPoly.degree f)
    (hp : Hex.Nat.Prime p) (hirr : Hex.FpPoly.Irreducible f) (b : Hex.FpPoly p) :
    Hex.FpPoly p →+* Hex.GFqField.FiniteField f hf hp hirr :=
  (Polynomial.eval₂RingHom (constHom f hf hp hirr)
      (ofPolyHom f hf hp hirr b)).comp
    (HexPolyFpMathlib.fpPolyEquiv : Hex.FpPoly p ≃+* Polynomial (ZMod p)).toRingHom

theorem substHom_apply (b g : Hex.FpPoly p) :
    substHom f hf hp hirr b g =
      ofPolyHom f hf hp hirr (Hex.DensePoly.compose g b) :=
  (ofPolyHom_compose_eq_eval₂ b g).symm

/-- Substitution is insensitive to reduction modulo a polynomial it kills.

This is the descent step: two representatives of the same residue differ by a
multiple of the modulus, so if the modulus is sent to zero they have the same
image. -/
theorem substHom_reduceMod (b : Hex.FpPoly p) (fm : Hex.FpPoly p)
    (hzero : substHom f hf hp hirr b fm = 0) (g : Hex.FpPoly p) :
    substHom f hf hp hirr b (Hex.GFqRing.reduceMod fm g) =
      substHom f hf hp hirr b g := by
  letI : Hex.DensePoly.DivModLaws (Hex.ZMod64 p) :=
    Hex.ZMod64.instDivModLawsZMod64Fp p
  have hspec := Hex.DensePoly.DivModLaws.divMod_spec (R := Hex.ZMod64 p) g fm
  have hg : (Hex.DensePoly.divMod g fm).1 * fm + Hex.GFqRing.reduceMod fm g = g := hspec
  have hmul : substHom f hf hp hirr b ((Hex.DensePoly.divMod g fm).1 * fm) = 0 := by
    rw [map_mul, hzero]
    exact mul_zero _
  have hcongr := congrArg (substHom f hf hp hirr b) hg
  rw [map_add, hmul] at hcongr
  rw [← hcongr]
  exact (zero_add (M := Hex.GFqField.FiniteField f hf hp hirr) _).symm

/-! # The Conway subfield embedding

Everything above is generic in the modulus. Specialising to two committed
Conway entries whose degrees divide, and taking the substitution point to be
the norm element, gives the map the Tier 2 compatibility fact is evidence for.
-/

section Conway

variable {m n : Nat}

/-- The class of `X` in the Conway presentation of `GFq p n`. -/
noncomputable def conwayX (p n : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p] (hn : Hex.Conway.SupportedEntry p n) :
    Hex.GFq p n hn :=
  ofPolyHom _ _ _ _ Hex.FpPoly.X

/-- The norm element of `GFq p n`, as a field element rather than a
representative: where the generator of the degree-`m` subfield goes. -/
noncomputable def conwayGen (p m n : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p] (hn : Hex.Conway.SupportedEntry p n) :
    Hex.GFq p n hn :=
  ofPolyHom _ _ _ _
    (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
      (Hex.Conway.conwayPoly_monic p n hn) m (n / m))

/-- The computed Conway subfield generator is the field norm of the ambient
generator. -/
theorem conwayGen_eq_norm (p : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p] (hn : Hex.Conway.SupportedEntry p n)
    (hm_pos : 0 < m) (hmn : m ∣ n) :
    conwayGen p m n hn =
      (conwayX p n hn) ^ ((p ^ n - 1) / (p ^ m - 1)) := by
  unfold conwayGen conwayX
  rw [← map_pow, ← HexPolyFpMathlib.linearPow_eq_pow]
  apply (Hex.GFq.ofPoly_eq_ofPoly_iff_reduceMod_eq hn _ _).2
  have hnorm := Hex.Conway.subfieldGen_eq_norm hn hm_pos hmn
  unfold Hex.Conway.subfieldGen at hnorm
  have hpow := Hex.FpPoly.Quotient.reduce_linearPow_eq_pow
    (g := Hex.Conway.conwayPoly p n hn)
    (hmonic := Hex.Conway.conwayPoly_monic p n hn)
    (hg_pos := Hex.Conway.conwayPoly_degree_pos p n hn)
    Hex.FpPoly.X ((p ^ n - 1) / (p ^ m - 1))
  have hval := congrArg Hex.FpPoly.Quotient.val (hnorm.trans hpow.symm)
  simp only [Hex.FpPoly.Quotient.reduce_val] at hval
  have hred (g : Hex.FpPoly p) :
      Hex.GFqRing.reduceMod (Hex.Conway.conwayPoly p n hn) g =
        Hex.FpPoly.modByMonic (Hex.Conway.conwayPoly p n hn) g
          (Hex.Conway.conwayPoly_monic p n hn) := by
    rw [Hex.FpPoly.modByMonic, Hex.DensePoly.modByMonic_eq_mod]
    rfl
  rw [hred, hred]
  exact hval

/-- Substituting the norm element kills the smaller Conway polynomial.

This is Tier 2 compatibility, carried from the executable `Bool` check to the
statement a descent needs. -/
theorem substHom_conwayPoly_eq_zero (p : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (hm : Hex.Conway.SupportedEntry p m) (hn : Hex.Conway.SupportedEntry p n)
    (hcompat : Hex.Conway.Compatible p m n hm hn) :
    substHom (Hex.Conway.conwayPoly p n hn) (Hex.Conway.conwayPoly_nonconstant p n hn)
        hn.prime (Hex.Conway.conwayPoly_irreducible p n hn)
        (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
          (Hex.Conway.conwayPoly_monic p n hn) m (n / m))
        (Hex.Conway.conwayPoly p m hm) = 0 := by
  rw [substHom_apply]
  have hzero : Hex.FpPoly.composeModMonicImpl (Hex.Conway.conwayPoly p m hm)
      (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
        (Hex.Conway.conwayPoly_monic p n hn) m (n / m))
      (Hex.Conway.conwayPoly p n hn) (Hex.Conway.conwayPoly_monic p n hn) = 0 :=
    beq_iff_eq.mp hcompat
  have hcompose := Hex.FpPoly.composeModMonic_eq_composeModMonicImpl
    (Hex.Conway.conwayPoly p m hm)
    (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
      (Hex.Conway.conwayPoly_monic p n hn) m (n / m))
    (Hex.Conway.conwayPoly p n hn) (Hex.Conway.conwayPoly_monic p n hn)
  rw [Hex.FpPoly.composeModMonic_eq_modByMonic_compose] at hcompose
  have hmod : Hex.FpPoly.modByMonic (Hex.Conway.conwayPoly p n hn)
      (Hex.DensePoly.compose (Hex.Conway.conwayPoly p m hm)
        (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
          (Hex.Conway.conwayPoly_monic p n hn) m (n / m)))
      (Hex.Conway.conwayPoly_monic p n hn) = 0 := by
    rw [hcompose, hzero]
  apply Hex.GFqField.ext
  apply Hex.GFqRing.ext
  show Hex.GFqField.repr (Hex.GFqField.ofPoly _ _ _ _ _) =
    Hex.GFqField.repr (0 : Hex.GFq p n hn)
  rw [Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_zero,
    Hex.GFqRing.reduceMod_zero _ (Hex.Conway.conwayPoly_nonconstant p n hn)]
  show Hex.GFqRing.reduceMod (Hex.Conway.conwayPoly p n hn) _ = 0
  have hred : Hex.GFqRing.reduceMod (Hex.Conway.conwayPoly p n hn)
      (Hex.DensePoly.compose (Hex.Conway.conwayPoly p m hm)
        (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
          (Hex.Conway.conwayPoly_monic p n hn) m (n / m))) =
      Hex.FpPoly.modByMonic (Hex.Conway.conwayPoly p n hn)
        (Hex.DensePoly.compose (Hex.Conway.conwayPoly p m hm)
          (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
            (Hex.Conway.conwayPoly_monic p n hn) m (n / m)))
        (Hex.Conway.conwayPoly_monic p n hn) := by
    rw [Hex.FpPoly.modByMonic, Hex.DensePoly.modByMonic_eq_mod]
    rfl
  rw [hred, hmod]

/--
The canonical embedding of the degree-`m` Conway field into the degree-`n` one.

Given `m ∣ n` and compatibility of the two committed entries, this is a genuine
ring homomorphism `GFq p m →+* GFq p n`: substitute the norm element for the
generator. It is canonical because the target is the Conway norm rather than an
arbitrary root of `C(p, m)`, so two callers embedding `GF(p^m)` into `GF(p^n)`
land on the same copy. That is the property the Conway table exists to provide,
and Tier 2 compatibility is what makes the substitution well defined.
-/
noncomputable def conwayEmbed (p m n : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (hm : Hex.Conway.SupportedEntry p m) (hn : Hex.Conway.SupportedEntry p n)
    (hcompat : Hex.Conway.Compatible p m n hm hn) :
    Hex.GFq p m hm →+* Hex.GFq p n hn where
  toFun a :=
    substHom _ _ _ _
      (Hex.Conway.normX (Hex.Conway.conwayPoly p n hn)
        (Hex.Conway.conwayPoly_monic p n hn) m (n / m))
      (Hex.GFqField.repr a)
  map_one' := by
    show substHom _ _ _ _ _ (Hex.GFqField.repr (1 : Hex.GFq p m hm)) = 1
    rw [Hex.GFqField.repr_one, substHom_reduceMod _ _
      (substHom_conwayPoly_eq_zero p hm hn hcompat), map_one]
    rfl
  map_zero' := by
    show substHom _ _ _ _ _ (Hex.GFqField.repr (0 : Hex.GFq p m hm)) = 0
    rw [Hex.GFqField.repr_zero, substHom_reduceMod _ _
      (substHom_conwayPoly_eq_zero p hm hn hcompat), map_zero]
    rfl
  map_add' a b := by
    show substHom _ _ _ _ _ (Hex.GFqField.repr (a + b)) = _
    rw [Hex.GFqField.repr_add, substHom_reduceMod _ _
      (substHom_conwayPoly_eq_zero p hm hn hcompat), map_add]
  map_mul' a b := by
    show substHom _ _ _ _ _ (Hex.GFqField.repr (a * b)) = _
    rw [Hex.GFqField.repr_mul, substHom_reduceMod _ _
      (substHom_conwayPoly_eq_zero p hm hn hcompat), map_mul]

/-- The Conway embedding sends the source generator to the computed subfield
generator. Together with {name}`conwayGen_eq_norm`, this identifies its image
with the field norm in the target. -/
theorem conwayEmbed_X (p : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (hm : Hex.Conway.SupportedEntry p m) (hn : Hex.Conway.SupportedEntry p n)
    (hcompat : Hex.Conway.Compatible p m n hm hn) :
    conwayEmbed p m n hm hn hcompat (conwayX p m hm) = conwayGen p m n hn := by
  unfold conwayEmbed conwayX conwayGen
  change substHom _ _ _ _ _ (Hex.GFqField.repr (ofPolyHom _ _ _ _ Hex.FpPoly.X)) =
    ofPolyHom _ _ _ _ _
  rw [ofPolyHom_apply, Hex.GFqField.repr_ofPoly, substHom_reduceMod _ _
    (substHom_conwayPoly_eq_zero p hm hn hcompat), substHom_apply,
    Hex.FpPoly.compose_X]

/-! # The embedding on committed entries

`GF(2^2)` sits inside `GF(2^6)`, `GF(2^3)` inside `GF(2^6)`, and `GF(13)`
inside `GF(13^6)`. Each is a ring homomorphism, and each is canonical: the
image of the generator is the Conway norm, not an arbitrary root. -/

/-- `GF(2^2) →+* GF(2^6)`, the canonical Conway embedding. -/
noncomputable example :
    Hex.GFq 2 2 Hex.Conway.supportedEntry_2_2 →+*
      Hex.GFq 2 6 Hex.Conway.supportedEntry_2_6 :=
  conwayEmbed 2 2 6 _ _ Hex.Conway.compat_2_2_6

/-- `GF(2^3) →+* GF(2^6)`. -/
noncomputable example :
    Hex.GFq 2 3 Hex.Conway.supportedEntry_2_3 →+*
      Hex.GFq 2 6 Hex.Conway.supportedEntry_2_6 :=
  conwayEmbed 2 3 6 _ _ Hex.Conway.compat_2_3_6

/-- `GF(13) →+* GF(13^6)`, the largest committed case. -/
noncomputable example :
    Hex.GFq 13 1 Hex.Conway.supportedEntry_13_1 →+*
      Hex.GFq 13 6 Hex.Conway.supportedEntry_13_6 :=
  conwayEmbed 13 1 6 _ _ Hex.Conway.compat_13_1_6

/-- `GF(2^4) →+* GF(2^8)`, so the AES-sized Conway field receives its subfield. -/
noncomputable example :
    Hex.GFq 2 4 Hex.Conway.supportedEntry_2_4 →+*
      Hex.GFq 2 8 Hex.Conway.supportedEntry_2_8 :=
  conwayEmbed 2 4 8 _ _ Hex.Conway.compat_2_4_8

end Conway

end HexGFqMathlib
