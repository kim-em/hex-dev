/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway
import HexGF2
import HexGFqField

/-!
User-facing canonical finite-field constructors.

This module packages committed Conway-table entries as generic quotient-field
types.  The generic `GFq` constructor always uses the `HexGFqField` quotient
representation; optimized packed characteristic-two constructors are kept to
separate declarations so the representation choice remains explicit.
-/
namespace Hex

namespace Conway

/-- A committed Conway-table entry available through instance synthesis.

This keeps the proof-oriented explicit `SupportedEntry` API available while
supporting a short user-facing field spelling for committed entries. -/
class CommittedEntry (p n : Nat) [ZMod64.Bounds p] where
  entry : SupportedEntry p n

/-- The committed table supports generic `GFq` construction for `C(2, 1)`. -/
instance committedEntry_2_1 : CommittedEntry 2 1 where
  entry := supportedEntry_2_1

/-- The committed table supports generic `GFq` construction for `C(2, 2)`. -/
instance committedEntry_2_2 : CommittedEntry 2 2 where
  entry := supportedEntry_2_2

/-- The committed table supports generic `GFq` construction for `C(2, 3)`. -/
instance committedEntry_2_3 : CommittedEntry 2 3 where
  entry := supportedEntry_2_3

/-- The committed table supports generic `GFq` construction for `C(2, 4)`. -/
instance committedEntry_2_4 : CommittedEntry 2 4 where
  entry := supportedEntry_2_4

/-- The committed table supports generic `GFq` construction for `C(2, 5)`. -/
instance committedEntry_2_5 : CommittedEntry 2 5 where
  entry := supportedEntry_2_5

/-- The committed table supports generic `GFq` construction for `C(2, 6)`. -/
instance committedEntry_2_6 : CommittedEntry 2 6 where
  entry := supportedEntry_2_6

/-- The committed table supports generic `GFq` construction for `C(3, 1)`. -/
instance committedEntry_3_1 : CommittedEntry 3 1 where
  entry := supportedEntry_3_1

/-- The committed table supports generic `GFq` construction for `C(3, 2)`. -/
instance committedEntry_3_2 : CommittedEntry 3 2 where
  entry := supportedEntry_3_2

/-- The committed table supports generic `GFq` construction for `C(3, 3)`. -/
instance committedEntry_3_3 : CommittedEntry 3 3 where
  entry := supportedEntry_3_3

/-- The committed table supports generic `GFq` construction for `C(3, 4)`. -/
instance committedEntry_3_4 : CommittedEntry 3 4 where
  entry := supportedEntry_3_4

/-- The committed table supports generic `GFq` construction for `C(3, 5)`. -/
instance committedEntry_3_5 : CommittedEntry 3 5 where
  entry := supportedEntry_3_5

/-- The committed table supports generic `GFq` construction for `C(3, 6)`. -/
instance committedEntry_3_6 : CommittedEntry 3 6 where
  entry := supportedEntry_3_6

/-- The committed table supports generic `GFq` construction for `C(5, 1)`. -/
instance committedEntry_5_1 : CommittedEntry 5 1 where
  entry := supportedEntry_5_1

/-- The committed table supports generic `GFq` construction for `C(5, 2)`. -/
instance committedEntry_5_2 : CommittedEntry 5 2 where
  entry := supportedEntry_5_2

/-- The committed table supports generic `GFq` construction for `C(5, 3)`. -/
instance committedEntry_5_3 : CommittedEntry 5 3 where
  entry := supportedEntry_5_3

/-- The committed table supports generic `GFq` construction for `C(5, 4)`. -/
instance committedEntry_5_4 : CommittedEntry 5 4 where
  entry := supportedEntry_5_4

/-- The committed table supports generic `GFq` construction for `C(5, 5)`. -/
instance committedEntry_5_5 : CommittedEntry 5 5 where
  entry := supportedEntry_5_5

/-- The committed table supports generic `GFq` construction for `C(5, 6)`. -/
instance committedEntry_5_6 : CommittedEntry 5 6 where
  entry := supportedEntry_5_6

/-- The committed table supports generic `GFq` construction for `C(7, 1)`. -/
instance committedEntry_7_1 : CommittedEntry 7 1 where
  entry := supportedEntry_7_1

/-- The committed table supports generic `GFq` construction for `C(7, 2)`. -/
instance committedEntry_7_2 : CommittedEntry 7 2 where
  entry := supportedEntry_7_2

/-- The committed table supports generic `GFq` construction for `C(7, 3)`. -/
instance committedEntry_7_3 : CommittedEntry 7 3 where
  entry := supportedEntry_7_3

/-- The committed table supports generic `GFq` construction for `C(7, 4)`. -/
instance committedEntry_7_4 : CommittedEntry 7 4 where
  entry := supportedEntry_7_4

/-- The committed table supports generic `GFq` construction for `C(7, 5)`. -/
instance committedEntry_7_5 : CommittedEntry 7 5 where
  entry := supportedEntry_7_5

/-- The committed table supports generic `GFq` construction for `C(7, 6)`. -/
instance committedEntry_7_6 : CommittedEntry 7 6 where
  entry := supportedEntry_7_6

/-- The committed table supports generic `GFq` construction for `C(11, 1)`. -/
instance committedEntry_11_1 : CommittedEntry 11 1 where
  entry := supportedEntry_11_1

/-- The committed table supports generic `GFq` construction for `C(11, 2)`. -/
instance committedEntry_11_2 : CommittedEntry 11 2 where
  entry := supportedEntry_11_2

/-- The committed table supports generic `GFq` construction for `C(11, 3)`. -/
instance committedEntry_11_3 : CommittedEntry 11 3 where
  entry := supportedEntry_11_3

/-- The committed table supports generic `GFq` construction for `C(11, 4)`. -/
instance committedEntry_11_4 : CommittedEntry 11 4 where
  entry := supportedEntry_11_4

/-- The committed table supports generic `GFq` construction for `C(11, 5)`. -/
instance committedEntry_11_5 : CommittedEntry 11 5 where
  entry := supportedEntry_11_5

/-- The committed table supports generic `GFq` construction for `C(11, 6)`. -/
instance committedEntry_11_6 : CommittedEntry 11 6 where
  entry := supportedEntry_11_6

/-- The committed table supports generic `GFq` construction for `C(13, 1)`. -/
instance committedEntry_13_1 : CommittedEntry 13 1 where
  entry := supportedEntry_13_1

/-- The committed table supports generic `GFq` construction for `C(13, 2)`. -/
instance committedEntry_13_2 : CommittedEntry 13 2 where
  entry := supportedEntry_13_2

/-- The committed table supports generic `GFq` construction for `C(13, 3)`. -/
instance committedEntry_13_3 : CommittedEntry 13 3 where
  entry := supportedEntry_13_3

/-- The committed table supports generic `GFq` construction for `C(13, 4)`. -/
instance committedEntry_13_4 : CommittedEntry 13 4 where
  entry := supportedEntry_13_4

/-- The committed table supports generic `GFq` construction for `C(13, 5)`. -/
instance committedEntry_13_5 : CommittedEntry 13 5 where
  entry := supportedEntry_13_5

/-- The committed table supports generic `GFq` construction for `C(13, 6)`. -/
instance committedEntry_13_6 : CommittedEntry 13 6 where
  entry := supportedEntry_13_6

/-- Interpret a packed single-word binary modulus as the corresponding generic
`FpPoly 2` polynomial.  `lower` supplies the coefficients of degrees `< n`;
the leading degree-`n` coefficient is inserted explicitly. -/
def packedGF2FpPoly (lower : UInt64) (n : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs <|
    (((List.range n).map fun i =>
      if (((lower >>> i.toUInt64) &&& 1) = 0) then
        (0 : ZMod64 2)
      else
        (1 : ZMod64 2)).toArray).push 1

/-- A committed Conway-table entry at `p = 2` that is also available as a
single-word packed `GF2n` modulus.  The `lower` field stores the lower
coefficients of the monic degree-`n` modulus; the leading `x^n` coefficient is
implicit in `GF2Poly.ofUInt64Monic lower n`. -/
class PackedGF2Entry (n : Nat) where
  entry : SupportedEntry 2 n
  lower : UInt64
  conway_eq_packed : conwayPoly 2 n entry = packedGF2FpPoly lower n
  degree_pos : 0 < n
  degree_lt_word : n < 64
  packed_irreducible : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n)

/-- A degree-one `GF2Poly` is either the monomial `X` or `X + 1` — the only two
monic degree-one polynomials over `𝔽₂`. Used to enumerate the possible factors
when proving a degree-two packed modulus irreducible. -/
private theorem gf2poly_degree_one_eq_monomial_or_x_plus_one {p : GF2Poly}
    (hp : p.degree = 1) :
    p = GF2Poly.monomial 1 ∨ p = GF2Poly.ofUInt64Monic 1 1 := by
  have hpNonzero : p ≠ 0 := by
    intro hzero
    simp [hzero] at hp
  have hpzeroFalse : p.isZero = false := by
    cases hzero : p.isZero
    · rfl
    · exact False.elim (hpNonzero (GF2Poly.eq_zero_of_isZero hzero))
  obtain ⟨d, hd⟩ := GF2Poly.degree?_isSome_of_isZero_false hpzeroFalse
  have hd1 : d = 1 := by
    simpa [GF2Poly.degree, hd] using hp
  subst d
  by_cases h0 : p.coeff 0 = true
  · right
    apply GF2Poly.ext_coeff
    intro n
    cases n with
    | zero =>
        rw [h0]
        decide
    | succ n =>
        cases n with
        | zero =>
            rw [GF2Poly.coeff_eq_true_of_degree?_eq_some hd]
            decide
        | succ n =>
            rw [GF2Poly.coeff_eq_false_of_degree?_lt hd (by omega)]
            have hxDegree : (GF2Poly.ofUInt64Monic 1 1).degree? = some 1 := by
              decide
            rw [GF2Poly.coeff_eq_false_of_degree?_lt hxDegree (by omega)]
  · left
    apply GF2Poly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hp0 : p.coeff 0 = false := by
          cases h : p.coeff 0
          · rfl
          · exact False.elim (h0 h)
        rw [hp0]
        decide
    | succ n =>
        cases n with
        | zero =>
            rw [GF2Poly.coeff_eq_true_of_degree?_eq_some hd]
            decide
        | succ n =>
            rw [GF2Poly.coeff_eq_false_of_degree?_lt hd (by omega)]
            rw [GF2Poly.coeff_monomial_ne
              (n := 1) (m := Nat.succ (Nat.succ n)) (by omega)]

/-- The packed polynomial `X + 1` (`ofUInt64Monic 1 1`) is nonzero. -/
private theorem gf2poly_x_plus_one_ne_zero :
    GF2Poly.ofUInt64Monic 1 1 ≠ 0 := by
  intro hzero
  have hwords := congrArg GF2Poly.toWords hzero
  have hbad :
      GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1) ≠
        GF2Poly.toWords (0 : GF2Poly) := by
    decide
  exact hbad hwords

/-- The packed modulus corresponding to the committed Conway entry `C(2, 1) =
X + 1`. -/
theorem packedGF2Entry_2_1_irreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 1 1) := by
  constructor
  · exact gf2poly_x_plus_one_ne_zero
  · intro a b hab
    by_cases ha0 : a.degree = 0
    · exact Or.inl ha0
    by_cases hb0 : b.degree = 0
    · exact Or.inr hb0
    exfalso
    have habWords := congrArg GF2Poly.toWords hab
    have haNonzero : a ≠ 0 := by
      intro hzero
      apply ha0
      simp [hzero]
    have hbNonzero : b ≠ 0 := by
      intro hzero
      apply hb0
      simp [hzero]
    have hfNonzero : GF2Poly.ofUInt64Monic 1 1 ≠ 0 :=
      gf2poly_x_plus_one_ne_zero
    have hfDegree : (GF2Poly.ofUInt64Monic 1 1).degree = 1 := by
      decide
    have haDegree : a.degree = 1 := by
      have haDvd : a ∣ GF2Poly.ofUInt64Monic 1 1 := ⟨b, by simp [hab]⟩
      have hle := GF2Poly.degree_le_of_dvd_nonzero
        haNonzero hfNonzero haDvd
      rw [hfDegree] at hle
      omega
    have hbDegree : b.degree = 1 := by
      have hbDvd : b ∣ GF2Poly.ofUInt64Monic 1 1 := ⟨a, by simp [GF2Poly.mul_comm, hab]⟩
      have hle := GF2Poly.degree_le_of_dvd_nonzero
        hbNonzero hfNonzero hbDvd
      rw [hfDegree] at hle
      omega
    rcases gf2poly_degree_one_eq_monomial_or_x_plus_one haDegree with ha | ha <;>
      rcases gf2poly_degree_one_eq_monomial_or_x_plus_one hbDegree with hb | hb
    · subst a
      subst b
      have hbad :
          GF2Poly.toWords (GF2Poly.monomial 1 * GF2Poly.monomial 1) ≠
            GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1) := by
        decide
      exact hbad habWords
    · subst a
      subst b
      have hbad :
          GF2Poly.toWords (GF2Poly.monomial 1 * GF2Poly.ofUInt64Monic 1 1) ≠
            GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1) := by
        decide
      exact hbad habWords
    · subst a
      subst b
      have hbad :
          GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1 * GF2Poly.monomial 1) ≠
            GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1) := by
        decide
      exact hbad habWords
    · subst a
      subst b
      have hbad :
          GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1 * GF2Poly.ofUInt64Monic 1 1) ≠
            GF2Poly.toWords (GF2Poly.ofUInt64Monic 1 1) := by
        decide
      exact hbad habWords

/-- The current committed table supports a packed `GF2n` view of `C(2, 1)`. -/
instance packedGF2Entry_2_1 : PackedGF2Entry 1 where
  entry := supportedEntry_2_1
  lower := 1
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := packedGF2Entry_2_1_irreducible

/-- Build the Rabin-style irreducibility certificate for the packed degree-`n`
modulus `ofUInt64Monic lower n`: the `X^(2^k)`-mod power chain for `k ≤ n`, and,
for each maximal proper divisor `d` of `n`, the Bézout coefficients of the xgcd
of the modulus with `X^(2^d) - X` (witnessing coprimality, hence no proper
subfield root). Consumed by `checkIrreducibilityCertificate_imp_irreducible`. -/
private def packedGF2IrreducibilityCertificate (lower : UInt64) (n : Nat) :
    GF2Poly.IrreducibilityCertificate :=
  let f := GF2Poly.ofUInt64Monic lower n
  { n := n
    powChain := ((List.range (n + 1)).map fun k => GF2Poly.xpow2kMod f k).toArray
    bezout :=
      ((GF2Poly.maximalProperDivisors n).map fun d =>
        let diff := GF2Poly.frobeniusDiffMod f d
        let xg := GF2Poly.xgcd f diff
        { left := xg.left, right := xg.right }).toArray }

set_option maxRecDepth 4096 in
/-- The packed Conway modulus for `C(2, 2)` (`0x3`) is irreducible,
checked from its certificate. -/
private theorem packedGF2Entry_2_2_irreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x3 2) :=
  GF2Poly.checkIrreducibilityCertificate_imp_irreducible
    (GF2Poly.ofUInt64Monic 0x3 2)
    (packedGF2IrreducibilityCertificate 0x3 2)
    (by decide)

set_option maxRecDepth 4096 in
/-- The packed Conway modulus for `C(2, 3)` (`0x3`) is irreducible,
checked from its certificate. -/
private theorem packedGF2Entry_2_3_irreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x3 3) :=
  GF2Poly.checkIrreducibilityCertificate_imp_irreducible
    (GF2Poly.ofUInt64Monic 0x3 3)
    (packedGF2IrreducibilityCertificate 0x3 3)
    (by decide)

set_option maxRecDepth 4096 in
/-- The packed Conway modulus for `C(2, 5)` (`0x5`) is irreducible,
checked from its certificate. -/
private theorem packedGF2Entry_2_5_irreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x5 5) :=
  GF2Poly.checkIrreducibilityCertificate_imp_irreducible
    (GF2Poly.ofUInt64Monic 0x5 5)
    (packedGF2IrreducibilityCertificate 0x5 5)
    (by decide)

set_option maxRecDepth 4096 in
/-- The packed Conway modulus for `C(2, 6)` (`0x1B`) is irreducible,
checked from its certificate. -/
private theorem packedGF2Entry_2_6_irreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 6) :=
  GF2Poly.checkIrreducibilityCertificate_imp_irreducible
    (GF2Poly.ofUInt64Monic 0x1B 6)
    (packedGF2IrreducibilityCertificate 0x1B 6)
    (by decide)

/-- The committed table supports a packed `GF2n` view of `C(2, 2)`. -/
instance packedGF2Entry_2_2 : PackedGF2Entry 2 where
  entry := supportedEntry_2_2
  lower := 0x3
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := packedGF2Entry_2_2_irreducible

/-- The committed table supports a packed `GF2n` view of `C(2, 3)`. -/
instance packedGF2Entry_2_3 : PackedGF2Entry 3 where
  entry := supportedEntry_2_3
  lower := 0x3
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := packedGF2Entry_2_3_irreducible

/-- The committed table supports a packed `GF2n` view of `C(2, 4)`. -/
instance packedGF2Entry_2_4 : PackedGF2Entry 4 where
  entry := supportedEntry_2_4
  lower := 0x3
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := GF2Poly.gf16_modulus_irreducible

/-- The committed table supports a packed `GF2n` view of `C(2, 5)`. -/
instance packedGF2Entry_2_5 : PackedGF2Entry 5 where
  entry := supportedEntry_2_5
  lower := 0x5
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := packedGF2Entry_2_5_irreducible

/-- The committed table supports a packed `GF2n` view of `C(2, 6)`. -/
instance packedGF2Entry_2_6 : PackedGF2Entry 6 where
  entry := supportedEntry_2_6
  lower := 0x1B
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := packedGF2Entry_2_6_irreducible

end Conway

/-- Canonical finite field with `p^n` elements for a committed Conway-table
entry, using the generic quotient-field representation. -/
abbrev GFq (p n : Nat) [ZMod64.Bounds p] (h : Conway.SupportedEntry p n) : Type :=
  GFqField.FiniteField (Conway.conwayPoly p n h)
    (Conway.conwayPoly_nonconstant p n h)
    h.prime
    (Conway.conwayPoly_irreducible p n h)

namespace GFq

variable {p n : Nat} [ZMod64.Bounds p]

/-- The Conway modulus selected for a committed `GFq p n` entry. -/
abbrev modulus (h : Conway.SupportedEntry p n) : FpPoly p :=
  Conway.conwayPoly p n h

/-- `GFq.modulus` is the Conway polynomial selected by the committed entry. -/
@[simp, grind =] theorem modulus_eq_conway (h : Conway.SupportedEntry p n) :
    modulus h = Conway.conwayPoly p n h :=
  rfl

/-- The selected Conway modulus has positive degree. -/
@[simp]
theorem modulus_nonconstant (h : Conway.SupportedEntry p n) :
    0 < FpPoly.degree (modulus h) :=
  Conway.conwayPoly_nonconstant p n h

/-- The selected Conway modulus is irreducible. -/
@[grind =>]
theorem modulus_irreducible (h : Conway.SupportedEntry p n) :
    FpPoly.Irreducible (modulus h) :=
  Conway.conwayPoly_irreducible p n h

grind_pattern modulus_irreducible => Conway.conwayPoly p n h

/-- The selected Conway modulus lives over a prime base field. -/
theorem modulus_prime (h : Conway.SupportedEntry p n) :
    Hex.Nat.Prime p :=
  h.prime

grind_pattern modulus_prime => h.prime

/-- Reduce a polynomial into the canonical field selected by a committed Conway
entry. -/
def ofPoly (h : Conway.SupportedEntry p n) (g : FpPoly p) : GFq p n h :=
  GFqField.ofPoly (modulus h) (modulus_nonconstant h) (modulus_prime h)
    (modulus_irreducible h) g

/-- `GFq.ofPoly` delegates to the generic quotient-field constructor with the
selected Conway modulus. -/
@[simp, grind =] theorem ofPoly_eq_field_ofPoly (h : Conway.SupportedEntry p n)
    (g : FpPoly p) :
    ofPoly h g =
      GFqField.ofPoly (modulus h) (modulus_nonconstant h)
        (modulus_prime h) (modulus_irreducible h) g :=
  rfl

/-- Project a canonical field element to its reduced polynomial representative. -/
def repr {h : Conway.SupportedEntry p n} (x : GFq p n h) : FpPoly p :=
  GFqField.repr x

/-- `GFq.repr` is the generic quotient-field representative projection. -/
@[simp, grind =] theorem repr_eq_field_repr {h : Conway.SupportedEntry p n}
    (x : GFq p n h) :
    repr x = GFqField.repr x :=
  rfl

/-- Two canonical `GFq` elements are equal when their reduced polynomial
representatives agree. -/
@[ext] theorem ext {h : Conway.SupportedEntry p n} {x y : GFq p n h}
    (hxy : repr x = repr y) :
    x = y := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  apply GFqField.ext
  apply GFqRing.ext
  simpa [repr, GFqField.repr] using hxy

/-- The canonical representative of an injected `FpPoly` is that polynomial
reduced modulo the selected Conway polynomial. Lets a caller normalise a
`repr (ofPoly h g)` round-trip to a plain `reduceMod`. -/
@[simp, grind =] theorem repr_ofPoly (h : Conway.SupportedEntry p n) (g : FpPoly p) :
    repr (ofPoly h g) = GFqRing.reduceMod (modulus h) g :=
  rfl

/-- The canonical representative of `0` in `GFq` is reduction of `0` modulo
the selected Conway polynomial. -/
@[simp, grind =] theorem repr_zero (h : Conway.SupportedEntry p n) :
    repr (0 : GFq p n h) = GFqRing.reduceMod (modulus h) 0 :=
  rfl

/-- The canonical representative of `1` in `GFq` is reduction of `1` modulo
the selected Conway polynomial. -/
@[simp, grind =] theorem repr_one (h : Conway.SupportedEntry p n) :
    repr (1 : GFq p n h) = GFqRing.reduceMod (modulus h) 1 :=
  rfl

/-- The canonical representative of a sum in `GFq` reduces from the sum of
representatives modulo the selected Conway polynomial. -/
@[simp, grind =] theorem repr_add {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    repr (x + y) = GFqRing.reduceMod (modulus h) (repr x + repr y) :=
  rfl

/-- The canonical representative of a product in `GFq` reduces from the product
of representatives modulo the selected Conway polynomial. -/
@[simp, grind =] theorem repr_mul {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    repr (x * y) = GFqRing.reduceMod (modulus h) (repr x * repr y) :=
  rfl

/-- The representative of a negation reduces from the negated representative. -/
@[simp, grind =] theorem repr_neg {h : Conway.SupportedEntry p n} (x : GFq p n h) :
    repr (-x) = GFqRing.reduceMod (modulus h) (-(repr x)) :=
  rfl

/-- The representative of a subtraction reduces from the difference of
representatives. -/
@[simp, grind =] theorem repr_sub {h : Conway.SupportedEntry p n} (x y : GFq p n h) :
    repr (x - y) = GFqRing.reduceMod (modulus h) (repr x - repr y) :=
  rfl

/-- The canonical representative of a natural literal in `GFq` is the
reduction modulo the selected Conway polynomial of the constant
polynomial carrying the literal as a `ZMod64` coefficient. -/
@[simp, grind =] theorem repr_natCast (h : Conway.SupportedEntry p n) (k : Nat) :
    repr ((k : GFq p n h)) =
      GFqRing.reduceMod (modulus h) (FpPoly.C (k : ZMod64 p)) :=
  rfl

/-- The canonical representative of a quotient in `GFq` lifts the
quotient-ring product of the dividend's representative with the inverse of
the divisor. -/
@[simp, grind =] theorem repr_div {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    repr (x / y) =
      GFqRing.repr (x.toQuotient * (GFqField.inv y).toQuotient) :=
  rfl

/-- The canonical representative of a natural power in `GFq` lifts the
quotient-ring power of the underlying quotient representative. -/
@[simp, grind =] theorem repr_pow {h : Conway.SupportedEntry p n}
    (x : GFq p n h) (k : Nat) :
    repr (x ^ k) = GFqRing.repr (x.toQuotient ^ k) :=
  rfl

/-- The canonical representative of a nonnegative integer power in `GFq` lifts
the quotient-ring power of the underlying quotient representative. -/
@[simp, grind =] theorem repr_zpow_ofNat {h : Conway.SupportedEntry p n}
    (x : GFq p n h) (k : Nat) :
    repr (x ^ (Int.ofNat k) : GFq p n h) =
      GFqRing.repr (x.toQuotient ^ k) :=
  rfl

/-- The canonical representative of a negative integer power in `GFq` lifts
the inverse of the corresponding quotient-ring positive power. -/
@[simp, grind =] theorem repr_zpow_negSucc {h : Conway.SupportedEntry p n}
    (x : GFq p n h) (k : Nat) :
    repr (x ^ (Int.negSucc k) : GFq p n h) =
      GFqRing.repr ((GFqField.inv (GFqField.pow x (k + 1))).toQuotient) :=
  rfl

/-- The canonical representative of an integer literal in `GFq` lifts the
quotient-ring integer-cast representative. -/
@[simp, grind =] theorem repr_intCast (h : Conway.SupportedEntry p n) (i : Int) :
    repr ((i : GFq p n h)) =
      GFqRing.repr
        ((i : GFqRing.PolyQuotient (modulus h) (modulus_nonconstant h))) :=
  rfl

/-- The representative of a natural scalar action lifts the quotient-ring
action. -/
@[simp, grind =] theorem repr_nsmul {h : Conway.SupportedEntry p n}
    (k : Nat) (x : GFq p n h) :
    repr (k • x : GFq p n h) = GFqRing.repr (k • x.toQuotient) :=
  rfl

/-- The representative of an integer scalar action lifts the quotient-ring
action. -/
@[simp, grind =] theorem repr_zsmul {h : Conway.SupportedEntry p n}
    (k : Int) (x : GFq p n h) :
    repr (k • x : GFq p n h) = GFqRing.repr (k • x.toQuotient) :=
  rfl

/-- The zero inverse in `GFq` follows the field wrapper's junk-value
convention and has zero representative. -/
@[simp, grind =] theorem repr_inv_zero (h : Conway.SupportedEntry p n) :
    repr ((0 : GFq p n h)⁻¹) = GFqRing.reduceMod (modulus h) 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  simp [repr]

/-- The zero inverse in `GFq` follows the field wrapper's junk-value convention. -/
-- `@[simp]`-only: `grind =` keys this on the `(0 : GFq p n h)` literal, whose
-- `GFqField.FiniteField` carrier holds `n`/`h` as erased instance args, so they
-- cannot be instantiated from the pattern (`invalid pattern(s) for inv_zero`).
-- The GF2n sibling `HexGF2.Field.inv_zero` carries `grind =` because there the
-- type indices appear explicitly in the keyed term.
@[simp] theorem inv_zero (h : Conway.SupportedEntry p n) :
    ((0 : GFq p n h)⁻¹ : GFq p n h) = 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  exact GFqField.inv_zero (modulus h) (modulus_nonconstant h)
    (modulus_prime h) (modulus_irreducible h)

/-- Division in `GFq` is multiplication by inverse. -/
@[grind =]
theorem div_eq_mul_inv {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    x / y = x * y⁻¹ := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  exact GFqField.div_eq_mul_inv x y

/-- A nonzero `GFq` element cancels against its inverse on the right. -/
theorem mul_inv_cancel {h : Conway.SupportedEntry p n}
    {x : GFq p n h} (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  exact GFqField.mul_inv_cancel (x := x) hx

/-- A nonzero `GFq` element cancels against its inverse on the left. -/
theorem inv_mul_cancel {h : Conway.SupportedEntry p n}
    {x : GFq p n h} (hx : x ≠ 0) :
    x⁻¹ * x = 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  exact GFqField.inv_mul_cancel (x := x) hx

/-- Two `GFq.ofPoly` constructors produce the same field element exactly when
their inputs have the same reduced representative modulo the selected Conway
polynomial. -/
theorem ofPoly_eq_ofPoly_iff_reduceMod_eq
    (h : Conway.SupportedEntry p n) (f g : FpPoly p) :
    ofPoly h f = ofPoly h g ↔
      GFqRing.reduceMod (modulus h) f = GFqRing.reduceMod (modulus h) g := by
  constructor
  · intro hfg
    have hrepr := congrArg repr hfg
    simpa using hrepr
  · intro hred
    apply ext
    simpa using hred

/-- Injecting an `FpPoly` into `GFq` is invariant under pre-reduction modulo
the selected Conway polynomial: a caller may drop a `reduceMod` already
sitting under `ofPoly`. -/
@[simp, grind =] theorem ofPoly_reduceMod
    (h : Conway.SupportedEntry p n) (f : FpPoly p) :
    ofPoly h (GFqRing.reduceMod (modulus h) f) = ofPoly h f := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  rw [ofPoly_eq_ofPoly_iff_reduceMod_eq]
  exact GFqRing.reduceMod_idem (modulus h) f

/-- The Frobenius endomorphism on the canonical Conway-backed field, computed
as the `p`-th power on the underlying quotient representation. -/
def frob {h : Conway.SupportedEntry p n} (x : GFq p n h) : GFq p n h :=
  GFqField.frob x

/-- `GFq.frob` is the `p`-th power map. -/
theorem frob_eq_pow {h : Conway.SupportedEntry p n} (x : GFq p n h) :
    frob x = x ^ p :=
  rfl

/-- The representative of `GFq.frob` is the quotient-ring `p`-th power
representative. -/
@[simp, grind =] theorem repr_frob {h : Conway.SupportedEntry p n} (x : GFq p n h) :
    repr (frob x) = GFqRing.repr (x.toQuotient ^ p) :=
  rfl

end GFq

/-- Ergonomic generic finite field for a committed Conway-table entry.

Use `GFqC p n` when the committed entry should be inferred from the current
Conway table. Use explicit `GFq p n h` when a proof needs to name the witness. -/
abbrev GFqC (p n : Nat) [ZMod64.Bounds p] [h : Conway.CommittedEntry p n] : Type :=
  GFq p n h.entry

namespace GFqC

variable {p n : Nat} [ZMod64.Bounds p] [h : Conway.CommittedEntry p n]

/-- The committed Conway-table entry selected for `GFqC p n`. -/
abbrev entry : Conway.SupportedEntry p n :=
  h.entry

/-- The Conway modulus selected for the committed `GFqC p n` field. -/
abbrev modulus : FpPoly p :=
  GFq.modulus (entry (p := p) (n := n))

/-- `GFqC.modulus` delegates to the explicit-entry `GFq.modulus`. -/
theorem modulus_eq_gfq :
    modulus (p := p) (n := n) =
      GFq.modulus (entry (p := p) (n := n)) :=
  rfl

/-- Reduce a polynomial into the committed `GFqC p n` field. -/
def ofPoly (g : FpPoly p) : GFqC p n :=
  GFq.ofPoly (entry (p := p) (n := n)) g

/-- `GFqC.ofPoly` delegates to the explicit-entry `GFq.ofPoly`. -/
theorem ofPoly_eq_gfq (g : FpPoly p) :
    ofPoly (p := p) (n := n) g =
      GFq.ofPoly (entry (p := p) (n := n)) g :=
  rfl

/-- Project a committed `GFqC` element to its reduced polynomial representative. -/
def repr (x : GFqC p n) : FpPoly p :=
  GFq.repr x

/-- `GFqC.repr` delegates to the explicit-entry `GFq.repr`. -/
theorem repr_eq_gfq (x : GFqC p n) :
    repr x = GFq.repr x :=
  rfl

/-- The representative of an injected polynomial is reduction modulo the
selected committed Conway polynomial. -/
@[simp, grind =] theorem repr_ofPoly (g : FpPoly p) :
    repr (ofPoly (p := p) (n := n) g) =
      GFqRing.reduceMod (modulus (p := p) (n := n)) g :=
  rfl

/-- The canonical representative of a sum in `GFqC` reduces from the sum of
representatives modulo the selected committed Conway polynomial. -/
@[simp, grind =] theorem repr_add (x y : GFqC p n) :
    repr (x + y) =
      GFqRing.reduceMod (modulus (p := p) (n := n)) (repr x + repr y) :=
  rfl

/-- The canonical representative of a product in `GFqC` reduces from the
product of representatives modulo the selected committed Conway polynomial. -/
@[simp, grind =] theorem repr_mul (x y : GFqC p n) :
    repr (x * y) =
      GFqRing.reduceMod (modulus (p := p) (n := n)) (repr x * repr y) :=
  rfl

/-- The Frobenius endomorphism on the committed `GFqC p n` field. -/
def frob (x : GFqC p n) : GFqC p n :=
  GFq.frob x

/-- `GFqC.frob` delegates to the explicit-entry `GFq.frob`. -/
theorem frob_eq_gfq (x : GFqC p n) :
    frob x = GFq.frob x :=
  rfl

/-- `GFqC.frob` is the `p`-th power map. -/
theorem frob_eq_pow (x : GFqC p n) :
    frob x = x ^ p :=
  rfl

/-- The representative of `GFqC.frob` is the quotient-ring `p`-th power
representative. -/
@[simp, grind =] theorem repr_frob (x : GFqC p n) :
    repr (frob x) = GFqRing.repr (x.toQuotient ^ p) :=
  rfl

end GFqC

/-- Optimized canonical binary field for committed Conway entries that have a
single-word packed modulus. -/
abbrev GF2q (n : Nat) [h : Conway.PackedGF2Entry n] : Type :=
  GF2n n h.lower h.degree_pos h.degree_lt_word h.packed_irreducible

namespace GF2q

variable {n : Nat} [h : Conway.PackedGF2Entry n]

/-- The supported Conway-table entry backing this optimized binary field. -/
def supportedEntry : Conway.SupportedEntry 2 n :=
  h.entry

/-- `GF2q.supportedEntry` is the committed packed Conway entry. -/
@[simp, grind =] theorem supportedEntry_eq :
    supportedEntry (n := n) = h.entry :=
  rfl

/-- The lower-word packed modulus selected for a committed optimized `GF2q`
entry. -/
def lower : UInt64 :=
  h.lower

/-- `GF2q.lower` is the lower-word modulus stored in the packed entry. -/
@[simp, grind =] theorem lower_eq :
    lower (n := n) = h.lower :=
  rfl

/-- The packed modulus polynomial selected for a committed optimized `GF2q`
entry. -/
def modulus : GF2Poly :=
  GF2Poly.ofUInt64Monic h.lower n

/-- `GF2q.modulus` is the packed monic polynomial selected by the entry. -/
@[simp, grind =] theorem modulus_eq_ofUInt64Monic :
    modulus (n := n) = GF2Poly.ofUInt64Monic h.lower n :=
  rfl

/-- The packed modulus, viewed through the generic `FpPoly 2` representation,
is the committed Conway polynomial for this entry. -/
theorem conway_eq_packed :
    Conway.conwayPoly 2 n h.entry = Conway.packedGF2FpPoly h.lower n :=
  h.conway_eq_packed

/-- The generic `GFq` modulus for a packed binary entry agrees with the packed
modulus viewed as an `FpPoly 2`. -/
theorem gfq_modulus_eq_packedFpPoly :
    GFq.modulus h.entry = Conway.packedGF2FpPoly (lower (n := n)) n := by
  simpa [GFq.modulus, lower] using h.conway_eq_packed

/-- The selected packed modulus has positive extension degree. -/
@[simp]
theorem degree_pos : 0 < n :=
  h.degree_pos

/-- The selected packed modulus fits in the single-word `GF2n` representation. -/
@[simp]
theorem degree_lt_word : n < 64 :=
  h.degree_lt_word

/-- The selected packed modulus is irreducible. -/
@[grind =>]
theorem modulus_irreducible : GF2Poly.Irreducible (modulus (n := n)) :=
  h.packed_irreducible

/-- Reduce a machine word into the optimized binary field selected by a
committed packed Conway entry. -/
def ofWord (w : UInt64) : GF2q n :=
  GF2n.reduce (n := n) (irr := h.lower) w

/-- `GF2q.ofWord` delegates to the packed `GF2n` reducer for the selected
Conway modulus. -/
@[simp, grind =] theorem ofWord_eq_reduce (w : UInt64) :
    ofWord (n := n) w = GF2n.reduce (n := n) (irr := h.lower) w :=
  rfl

/-- Project an optimized binary field element to its packed machine-word
representative. -/
def repr (x : GF2q n) : UInt64 :=
  x.val

/-- `GF2q.repr` is the packed-word value stored by `GF2n`. -/
@[simp, grind =] theorem repr_eq_val (x : GF2q n) :
    repr x = x.val :=
  rfl

/-- Interpret the low `n` bits of a packed binary word as an `FpPoly 2`
polynomial. -/
def wordFpPoly (w : UInt64) : FpPoly 2 :=
  FpPoly.ofCoeffs <|
    (((List.range n).map fun i =>
      if (((w >>> i.toUInt64) &&& 1) = 0) then
        (0 : ZMod64 2)
      else
        (1 : ZMod64 2)).toArray)

/-- Interpret the packed representative of an optimized binary-field element
as a generic `FpPoly 2` polynomial. -/
def reprFpPoly (x : GF2q n) : FpPoly 2 :=
  wordFpPoly (n := n) (repr x)

/-- Map an optimized packed canonical binary-field element into the generic
canonical `GFq 2 n` model for the same committed Conway entry. -/
def toGFq (x : GF2q n) : GFq 2 n (supportedEntry (n := n)) :=
  GFq.ofPoly (supportedEntry (n := n)) (reprFpPoly x)

/-- `GF2q.reprFpPoly` is the low-bit `FpPoly 2` view of the packed
representative. -/
@[simp, grind =] theorem reprFpPoly_eq_wordFpPoly (x : GF2q n) :
    reprFpPoly x = wordFpPoly (n := n) (repr x) :=
  rfl

/-- `GF2q.toGFq` injects the packed representative through `GFq.ofPoly`. -/
@[simp, grind =] theorem toGFq_eq_ofPoly (x : GF2q n) :
    toGFq x = GFq.ofPoly (supportedEntry (n := n)) (reprFpPoly x) :=
  rfl

/-- Bridging a packed word into `GFq 2 n` injects the reduced packed
representative as an `FpPoly 2`. -/
@[simp, grind =] theorem toGFq_ofWord (w : UInt64) :
    toGFq (ofWord (n := n) w) =
      GFq.ofPoly (supportedEntry (n := n))
        (wordFpPoly (n := n) (repr (ofWord (n := n) w))) :=
  rfl

/-- The generic representative of `GF2q.toGFq` is the selected Conway-modulus
reduction of the packed representative viewed as an `FpPoly 2`. -/
@[simp, grind =] theorem toGFq_repr (x : GF2q n) :
    GFq.repr (toGFq x) =
      GFqRing.reduceMod (GFq.modulus (supportedEntry (n := n))) (reprFpPoly x) :=
  rfl

/-- Two optimized `GF2q` elements are equal when their packed representatives
agree. -/
@[ext] theorem ext {x y : GF2q n} (hxy : repr x = repr y) :
    x = y := by
  cases x
  cases y
  simp [repr] at hxy
  subst hxy
  rfl

/-- The packed representative of a word injected into `GF2q` is that word
reduced into the field by `GF2n.reduce`, relating the raw `UInt64` word to the
canonical packed `GF2q` representation. -/
@[simp, grind =] theorem repr_ofWord (w : UInt64) :
    repr (ofWord (n := n) w) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) w).val :=
  rfl

/-- The packed representative of `0` in `GF2q` is the zero word. -/
@[simp, grind =] theorem repr_zero :
    repr (0 : GF2q n) = 0 :=
  rfl

/-- The packed representative of `1` in `GF2q` is the one word. -/
@[simp, grind =] theorem repr_one :
    repr (1 : GF2q n) = 1 := by
  show GF2Poly.canonicalWordLT n h.degree_lt_word
      (GF2Poly.packedReduceWord n h.lower (GF2Poly.ofUInt64 1)) = 1
  have hn1 : 1 < 2 ^ n :=
    calc 1 = 2 ^ 0 := by decide
      _ < 2 ^ n := Nat.pow_lt_pow_right (by decide) h.degree_pos
  -- `ofUInt64 1 = (1 : GF2Poly)`, and `1 % modulus = 1` since `1.degree < modulus.degree = n`.
  have hmod : (1 : GF2Poly) % GF2Poly.ofUInt64Monic h.lower n = 1 :=
    GF2Poly.mod_eq_self_of_reduced 1 _ <| Or.inr <| by
      rw [GF2Poly.degree_ofUInt64Monic_of_lt_64 h.lower h.degree_lt_word]
      exact h.degree_pos
  -- Hence `ofUInt64 (packedReduceWord ... (ofUInt64 1)) = 1` as polynomials.
  have hpoly :
      GF2Poly.ofUInt64
          (GF2Poly.packedReduceWord n h.lower (GF2Poly.ofUInt64 1)) = 1 := by
    rw [GF2Poly.ofUInt64_packedReduceWord_eq_of_degree_lt
      h.degree_lt_word (GF2Poly.ofUInt64 1) (Or.inr ?_)]
    · show (1 : GF2Poly) % GF2Poly.ofUInt64Monic h.lower n = 1
      exact hmod
    · show ((1 : GF2Poly) % GF2Poly.ofUInt64Monic h.lower n).degree < n
      rw [hmod]; exact h.degree_pos
  -- Compare the single stored words: both `ofUInt64 _` and `ofUInt64 1` equal `ofWords #[1]`.
  have hword :
      GF2Poly.packedReduceWord n h.lower (GF2Poly.ofUInt64 1) = 1 := by
    by_cases hw0 :
        GF2Poly.packedReduceWord n h.lower (GF2Poly.ofUInt64 1) = 0
    · exfalso
      have hbad : GF2Poly.ofUInt64 0 = (1 : GF2Poly) := hw0 ▸ hpoly
      have : (GF2Poly.ofUInt64 0).words = (1 : GF2Poly).words := congrArg GF2Poly.words hbad
      revert this; decide
    · have hwords :
          (#[GF2Poly.packedReduceWord n h.lower (GF2Poly.ofUInt64 1)] :
            Array UInt64) = #[1] := by
        have hwords' := congrArg GF2Poly.words hpoly
        rw [show GF2Poly.ofUInt64
            (GF2Poly.packedReduceWord n h.lower (GF2Poly.ofUInt64 1)) =
              GF2Poly.ofWords #[GF2Poly.packedReduceWord n h.lower
                (GF2Poly.ofUInt64 1)] from rfl,
          GF2Poly.words_ofWords_single_nonzero hw0] at hwords'
        exact hwords'
      have h0 := congrArg (fun a => a[0]?) hwords
      simpa using h0
  rw [hword]
  -- Finally: `canonicalWordLT n hn64 1 = 1` since `1.toNat < 2 ^ n`.
  apply UInt64.toNat_inj.mp
  simp [GF2Poly.canonicalWordLT, Nat.mod_eq_of_lt hn1]

/-- The packed representative of a natural-number literal is stored by the
packed backend's characteristic-two natural cast. -/
@[simp, grind =] theorem repr_natCast (k : Nat) :
    repr (Nat.cast k : GF2q n) =
      (GF2n.natCast
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) k).val :=
  rfl

/-- The packed representative of an integer literal is stored by the packed
backend's characteristic-two integer cast. -/
@[simp, grind =] theorem repr_intCast (k : Int) :
    repr (Int.cast k : GF2q n) =
      (GF2n.intCast
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) k).val :=
  rfl

/-- In characteristic two, negation preserves the packed representative. -/
@[simp, grind =] theorem repr_neg (x : GF2q n) :
    repr (-x) = repr x :=
  rfl

/-- The packed representative of a subtraction is the reduced XOR of
representatives. -/
@[simp, grind =] theorem repr_sub (x y : GF2q n) :
    repr (x - y) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        (repr x ^^^ repr y)).val :=
  rfl

/-- Natural scalar multiplication in optimized binary fields depends only on
the scalar parity. -/
@[simp, grind =] theorem repr_nsmul (k : Nat) (x : GF2q n) :
    repr (k • x : GF2q n) =
      if k % 2 = 0 then 0 else repr x := by
  change
    (GF2n.nsmul
      (n := n) (irr := h.lower)
      (hn := h.degree_pos) (hn64 := h.degree_lt_word)
      (hirr := h.packed_irreducible) k x).val =
        if k % 2 = 0 then 0 else x.val
  by_cases hk : k % 2 = 0
  · have hzero : (0 : GF2q n).val = 0 := by
      simpa [repr] using (repr_zero (n := n))
    simpa [GF2n.nsmul, hk] using hzero
  · simp [GF2n.nsmul, hk]

/-- Integer scalar multiplication in optimized binary fields depends only on
the absolute-value parity. -/
@[simp, grind =] theorem repr_zsmul (k : Int) (x : GF2q n) :
    repr (k • x : GF2q n) =
      if k.natAbs % 2 = 0 then 0 else repr x := by
  change
    (GF2n.zsmul
      (n := n) (irr := h.lower)
      (hn := h.degree_pos) (hn64 := h.degree_lt_word)
      (hirr := h.packed_irreducible) k x).val =
        if k.natAbs % 2 = 0 then 0 else x.val
  by_cases hk : k.natAbs % 2 = 0
  · have hzero : (0 : GF2q n).val = 0 := by
      simpa [repr] using (repr_zero (n := n))
    simpa [GF2n.zsmul, hk] using hzero
  · simp [GF2n.zsmul, hk]

/-- The packed representative of a sum is the reduced XOR of representatives. -/
@[simp, grind =] theorem repr_add (x y : GF2q n) :
    repr (x + y) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        (repr x ^^^ repr y)).val :=
  rfl

/-- The packed representative of a product is the reduced carry-less product
of representatives. -/
@[simp, grind =] theorem repr_mul (x y : GF2q n) :
    repr (x * y) =
      (let product := Hex.clmul (repr x) (repr y)
       GF2n.reduceWide
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        product.1 product.2).val := by
  rfl

/-- The packed representative of an inverse is the representative stored by
the packed `GF2n` inversion path. -/
@[simp, grind =] theorem repr_inv (x : GF2q n) :
    repr x⁻¹ =
      (GF2n.inv
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x).val := by
  rfl

/-- The packed representative of a quotient is the representative stored by
the packed `GF2n` division path. -/
@[simp, grind =] theorem repr_div (x y : GF2q n) :
    repr (x / y) =
      (GF2n.div
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x y).val :=
  rfl

/-- The packed representative of a natural power is stored by the packed
`GF2n` square-and-multiply power. -/
@[simp, grind =] theorem repr_pow (x : GF2q n) (k : Nat) :
    repr (x ^ k) =
      (GF2n.pow
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x k).val :=
  rfl

/-- The packed representative of a nonnegative integer power is stored by the
packed `GF2n` integer-power operation. -/
@[simp, grind =] theorem repr_zpow_ofNat (x : GF2q n) (k : Nat) :
    repr (x ^ (Int.ofNat k) : GF2q n) =
      (GF2n.zpow
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x (Int.ofNat k)).val :=
  rfl

/-- The packed representative of a negative integer power is stored by the
packed `GF2n` integer-power operation. -/
@[simp, grind =] theorem repr_zpow_negSucc (x : GF2q n) (k : Nat) :
    repr (x ^ (Int.negSucc k) : GF2q n) =
      (GF2n.zpow
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x (Int.negSucc k)).val :=
  rfl

end GF2q

end Hex
