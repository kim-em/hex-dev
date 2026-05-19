import HexConway
import HexGF2
import HexGfqField

/-!
User-facing canonical finite-field constructors.

This module packages committed Conway-table entries as generic quotient-field
types.  The generic `GFq` constructor always uses the `HexGfqField` quotient
representation; optimized packed characteristic-two constructors are kept to
separate declarations so the representation choice remains explicit.
-/
namespace Hex

namespace Conway

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
@[simp] theorem modulus_eq_conway (h : Conway.SupportedEntry p n) :
    modulus h = Conway.conwayPoly p n h :=
  rfl

/-- The selected Conway modulus has positive degree. -/
theorem modulus_nonconstant (h : Conway.SupportedEntry p n) :
    0 < FpPoly.degree (modulus h) :=
  Conway.conwayPoly_nonconstant p n h

/-- The selected Conway modulus is irreducible. -/
theorem modulus_irreducible (h : Conway.SupportedEntry p n) :
    FpPoly.Irreducible (modulus h) :=
  Conway.conwayPoly_irreducible p n h

/-- The selected Conway modulus lives over a prime base field. -/
theorem modulus_prime (h : Conway.SupportedEntry p n) :
    Hex.Nat.Prime p :=
  h.prime

/-- Reduce a polynomial into the canonical field selected by a committed Conway
entry. -/
def ofPoly (h : Conway.SupportedEntry p n) (g : FpPoly p) : GFq p n h :=
  GFqField.ofPoly (modulus h) (modulus_nonconstant h) (modulus_prime h)
    (modulus_irreducible h) g

/-- `GFq.ofPoly` delegates to the generic quotient-field constructor with the
selected Conway modulus. -/
@[simp] theorem ofPoly_eq_field_ofPoly (h : Conway.SupportedEntry p n)
    (g : FpPoly p) :
    ofPoly h g =
      GFqField.ofPoly (modulus h) (modulus_nonconstant h)
        (modulus_prime h) (modulus_irreducible h) g :=
  rfl

/-- Project a canonical field element to its reduced polynomial representative. -/
def repr {h : Conway.SupportedEntry p n} (x : GFq p n h) : FpPoly p :=
  GFqField.repr x

/-- `GFq.repr` is the generic quotient-field representative projection. -/
@[simp] theorem repr_eq_field_repr {h : Conway.SupportedEntry p n}
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

@[simp] theorem repr_ofPoly (h : Conway.SupportedEntry p n) (g : FpPoly p) :
    repr (ofPoly h g) = GFqRing.reduceMod (modulus h) g :=
  rfl

/-- The canonical representative of `0` in `GFq` is reduction of `0` modulo
the selected Conway polynomial. -/
@[simp] theorem repr_zero (h : Conway.SupportedEntry p n) :
    repr (0 : GFq p n h) = GFqRing.reduceMod (modulus h) 0 :=
  rfl

/-- The canonical representative of `1` in `GFq` is reduction of `1` modulo
the selected Conway polynomial. -/
@[simp] theorem repr_one (h : Conway.SupportedEntry p n) :
    repr (1 : GFq p n h) = GFqRing.reduceMod (modulus h) 1 :=
  rfl

/-- The canonical representative of a sum in `GFq` reduces from the sum of
representatives modulo the selected Conway polynomial. -/
@[simp] theorem repr_add {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    repr (x + y) = GFqRing.reduceMod (modulus h) (repr x + repr y) :=
  rfl

/-- The canonical representative of a product in `GFq` reduces from the product
of representatives modulo the selected Conway polynomial. -/
@[simp] theorem repr_mul {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    repr (x * y) = GFqRing.reduceMod (modulus h) (repr x * repr y) :=
  rfl

/-- The representative of a negation reduces from the negated representative. -/
@[simp] theorem repr_neg {h : Conway.SupportedEntry p n} (x : GFq p n h) :
    repr (-x) = GFqRing.reduceMod (modulus h) (-(repr x)) :=
  rfl

/-- The representative of a subtraction reduces from the difference of
representatives. -/
@[simp] theorem repr_sub {h : Conway.SupportedEntry p n} (x y : GFq p n h) :
    repr (x - y) = GFqRing.reduceMod (modulus h) (repr x - repr y) :=
  rfl

/-- The canonical representative of a natural literal in `GFq` is the
reduction modulo the selected Conway polynomial of the constant
polynomial carrying the literal as a `ZMod64` coefficient. -/
@[simp] theorem repr_natCast (h : Conway.SupportedEntry p n) (k : Nat) :
    repr ((k : GFq p n h)) =
      GFqRing.reduceMod (modulus h) (FpPoly.C (k : ZMod64 p)) :=
  rfl

/-- The canonical representative of a quotient in `GFq` lifts the
quotient-ring product of the dividend's representative with the inverse of
the divisor. -/
@[simp] theorem repr_div {h : Conway.SupportedEntry p n}
    (x y : GFq p n h) :
    repr (x / y) =
      GFqRing.repr (x.toQuotient * (GFqField.inv y).toQuotient) :=
  rfl

/-- The canonical representative of a natural power in `GFq` lifts the
quotient-ring power of the underlying quotient representative. -/
@[simp] theorem repr_pow {h : Conway.SupportedEntry p n}
    (x : GFq p n h) (k : Nat) :
    repr (x ^ k) = GFqRing.repr (x.toQuotient ^ k) :=
  rfl

/-- The canonical representative of a nonnegative integer power in `GFq` lifts
the quotient-ring power of the underlying quotient representative. -/
@[simp] theorem repr_zpow_ofNat {h : Conway.SupportedEntry p n}
    (x : GFq p n h) (k : Nat) :
    repr (x ^ (Int.ofNat k) : GFq p n h) =
      GFqRing.repr (x.toQuotient ^ k) :=
  rfl

/-- The canonical representative of a negative integer power in `GFq` lifts
the inverse of the corresponding quotient-ring positive power. -/
@[simp] theorem repr_zpow_negSucc {h : Conway.SupportedEntry p n}
    (x : GFq p n h) (k : Nat) :
    repr (x ^ (Int.negSucc k) : GFq p n h) =
      GFqRing.repr ((GFqField.inv (GFqField.pow x (k + 1))).toQuotient) :=
  rfl

/-- The canonical representative of an integer literal in `GFq` lifts the
quotient-ring integer-cast representative. -/
@[simp] theorem repr_intCast (h : Conway.SupportedEntry p n) (i : Int) :
    repr ((i : GFq p n h)) =
      GFqRing.repr
        ((i : GFqRing.PolyQuotient (modulus h) (modulus_nonconstant h))) :=
  rfl

/-- The representative of a natural scalar action lifts the quotient-ring
action. -/
@[simp] theorem repr_nsmul {h : Conway.SupportedEntry p n}
    (k : Nat) (x : GFq p n h) :
    repr (k • x : GFq p n h) = GFqRing.repr (k • x.toQuotient) :=
  rfl

/-- The representative of an integer scalar action lifts the quotient-ring
action. -/
@[simp] theorem repr_zsmul {h : Conway.SupportedEntry p n}
    (k : Int) (x : GFq p n h) :
    repr (k • x : GFq p n h) = GFqRing.repr (k • x.toQuotient) :=
  rfl

/-- The canonical representative of a nonzero inverse in `GFq` is the inverse
polynomial representative reduced through the selected Conway modulus. -/
@[simp] theorem repr_inv_of_ne_zero {h : Conway.SupportedEntry p n}
    {x : GFq p n h} (hx : x ≠ 0) :
    repr (x⁻¹ : GFq p n h) =
      GFqRing.repr
        (GFqRing.ofPoly (modulus h) (modulus_nonconstant h)
          (GFqField.invPoly x.toQuotient)) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  simpa using
    (GFqField.repr_inv_of_ne_zero
      (f := modulus h) (hf := modulus_nonconstant h)
      (hp := modulus_prime h) (hirr := modulus_irreducible h)
      (x := x) hx)

/-- The zero inverse in `GFq` follows the field wrapper's junk-value
convention and has zero representative. -/
@[simp] theorem repr_inv_zero (h : Conway.SupportedEntry p n) :
    repr ((0 : GFq p n h)⁻¹) = GFqRing.reduceMod (modulus h) 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  simp [repr]

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

@[simp] theorem ofPoly_reduceMod
    (h : Conway.SupportedEntry p n) (f : FpPoly p) :
    ofPoly h (GFqRing.reduceMod (modulus h) f) = ofPoly h f := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime h.prime
  rw [ofPoly_eq_ofPoly_iff_reduceMod_eq]
  exact GFqRing.reduceMod_idem (modulus h) f

end GFq

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
@[simp] theorem supportedEntry_eq :
    supportedEntry (n := n) = h.entry :=
  rfl

/-- The lower-word packed modulus selected for a committed optimized `GF2q`
entry. -/
def lower : UInt64 :=
  h.lower

/-- `GF2q.lower` is the lower-word modulus stored in the packed entry. -/
@[simp] theorem lower_eq :
    lower (n := n) = h.lower :=
  rfl

/-- The packed modulus polynomial selected for a committed optimized `GF2q`
entry. -/
def modulus : GF2Poly :=
  GF2Poly.ofUInt64Monic h.lower n

/-- `GF2q.modulus` is the packed monic polynomial selected by the entry. -/
@[simp] theorem modulus_eq_ofUInt64Monic :
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
theorem degree_pos : 0 < n :=
  h.degree_pos

/-- The selected packed modulus fits in the single-word `GF2n` representation. -/
theorem degree_lt_word : n < 64 :=
  h.degree_lt_word

/-- The selected packed modulus is irreducible. -/
theorem modulus_irreducible : GF2Poly.Irreducible (modulus (n := n)) :=
  h.packed_irreducible

/-- Reduce a machine word into the optimized binary field selected by a
committed packed Conway entry. -/
def ofWord (w : UInt64) : GF2q n :=
  GF2n.reduce (n := n) (irr := h.lower) w

/-- `GF2q.ofWord` delegates to the packed `GF2n` reducer for the selected
Conway modulus. -/
@[simp] theorem ofWord_eq_reduce (w : UInt64) :
    ofWord (n := n) w = GF2n.reduce (n := n) (irr := h.lower) w :=
  rfl

/-- Project an optimized binary field element to its packed machine-word
representative. -/
def repr (x : GF2q n) : UInt64 :=
  x.val

/-- `GF2q.repr` is the packed-word value stored by `GF2n`. -/
@[simp] theorem repr_eq_val (x : GF2q n) :
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
@[simp] theorem reprFpPoly_eq_wordFpPoly (x : GF2q n) :
    reprFpPoly x = wordFpPoly (n := n) (repr x) :=
  rfl

/-- `GF2q.toGFq` injects the packed representative through `GFq.ofPoly`. -/
@[simp] theorem toGFq_eq_ofPoly (x : GF2q n) :
    toGFq x = GFq.ofPoly (supportedEntry (n := n)) (reprFpPoly x) :=
  rfl

/-- Bridging a packed word into `GFq 2 n` injects the reduced packed
representative as an `FpPoly 2`. -/
@[simp] theorem toGFq_ofWord (w : UInt64) :
    toGFq (ofWord (n := n) w) =
      GFq.ofPoly (supportedEntry (n := n))
        (wordFpPoly (n := n) (repr (ofWord (n := n) w))) :=
  rfl

/-- The generic representative of `GF2q.toGFq` is the selected Conway-modulus
reduction of the packed representative viewed as an `FpPoly 2`. -/
@[simp] theorem toGFq_repr (x : GF2q n) :
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

@[simp] theorem repr_ofWord (w : UInt64) :
    repr (ofWord (n := n) w) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) w).val :=
  rfl

/-- The packed representative of `0` in `GF2q` is the zero word. -/
@[simp] theorem repr_zero :
    repr (0 : GF2q n) = 0 :=
  rfl

/-- The packed representative of `1` in `GF2q` is the one word. -/
@[simp] theorem repr_one :
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
@[simp] theorem repr_natCast (k : Nat) :
    repr (Nat.cast k : GF2q n) =
      (GF2n.natCast
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) k).val :=
  rfl

/-- The packed representative of an integer literal is stored by the packed
backend's characteristic-two integer cast. -/
@[simp] theorem repr_intCast (k : Int) :
    repr (Int.cast k : GF2q n) =
      (GF2n.intCast
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) k).val :=
  rfl

/-- In characteristic two, negation preserves the packed representative. -/
@[simp] theorem repr_neg (x : GF2q n) :
    repr (-x) = repr x :=
  rfl

/-- The packed representative of a subtraction is the reduced XOR of
representatives. -/
@[simp] theorem repr_sub (x y : GF2q n) :
    repr (x - y) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        (repr x ^^^ repr y)).val :=
  rfl

/-- Natural scalar multiplication in optimized binary fields depends only on
the scalar parity. -/
@[simp] theorem repr_nsmul (k : Nat) (x : GF2q n) :
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
@[simp] theorem repr_zsmul (k : Int) (x : GF2q n) :
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
@[simp] theorem repr_add (x y : GF2q n) :
    repr (x + y) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        (repr x ^^^ repr y)).val :=
  rfl

/-- The packed representative of a product is the reduced carry-less product
of representatives. -/
@[simp] theorem repr_mul (x y : GF2q n) :
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
@[simp] theorem repr_inv (x : GF2q n) :
    repr x⁻¹ =
      (GF2n.inv
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x).val := by
  rfl

/-- The packed representative of a quotient is the representative stored by
the packed `GF2n` division path. -/
@[simp] theorem repr_div (x y : GF2q n) :
    repr (x / y) =
      (GF2n.div
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x y).val :=
  rfl

/-- The packed representative of a natural power is stored by the packed
`GF2n` square-and-multiply power. -/
@[simp] theorem repr_pow (x : GF2q n) (k : Nat) :
    repr (x ^ k) =
      (GF2n.pow
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x k).val :=
  rfl

/-- The packed representative of a nonnegative integer power is stored by the
packed `GF2n` integer-power operation. -/
@[simp] theorem repr_zpow_ofNat (x : GF2q n) (k : Nat) :
    repr (x ^ (Int.ofNat k) : GF2q n) =
      (GF2n.zpow
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x (Int.ofNat k)).val :=
  rfl

/-- The packed representative of a negative integer power is stored by the
packed `GF2n` integer-power operation. -/
@[simp] theorem repr_zpow_negSucc (x : GF2q n) (k : Nat) :
    repr (x ^ (Int.negSucc k) : GF2q n) =
      (GF2n.zpow
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible)
        x (Int.negSucc k)).val :=
  rfl

end GF2q

end Hex
