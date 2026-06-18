import HexGFq
import HexGF2Mathlib.Field
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Generic Mathlib-side definitions for the executable `GFq` model.

This module exposes the concrete reduced-representative enumeration used to
transport `Fintype` support onto generic `Hex.GFqField.FiniteField` values, and
states the canonical-cardinality equivalence to Mathlib's `GaloisField`.
-/

namespace HexGFqMathlib

open Hex

namespace FpPoly

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret the first `degree` coefficients of an `FpPoly` as a base-`p`
index.

This is the encoder half of the bijection between degree-`< degree`
polynomials and `Fin (p ^ degree)`; `ofIndexBelowDegree` is its inverse on
bounded inputs (`coeffIndex_ofIndexBelowDegree`,
`ofIndexBelowDegree_coeffIndex`), and the value is always below `p ^ degree`
(`coeffIndex_lt`). -/
def coeffIndex (degree : Nat) (f : Hex.FpPoly p) : Nat :=
  (List.range degree).foldl
    (fun acc i => acc + (f.coeff i).toNat * p ^ i)
    0

/-- Decode a base-`p` index into a polynomial with at most `degree`
coefficients.

The decoder half of the `coeffIndex` bijection. Its coefficients are
characterised by `coeff_ofIndexBelowDegree_of_lt` (in range, a `simp` normal
form) and `coeff_ofIndexBelowDegree_of_ge` (beyond the width, zero), and its
`FpPoly.degree` stays below `degree` when the width is positive
(`ofIndexBelowDegree_degree_lt`). -/
def ofIndexBelowDegree (degree index : Nat) : Hex.FpPoly p :=
  Hex.FpPoly.ofCoeffs <|
    ((List.range degree).map fun i =>
      Hex.ZMod64.ofNat p (index / p ^ i)).toArray

/-- Peeling the top position of the base-`p` encoding. -/
theorem coeffIndex_succ (degree : Nat) (f : Hex.FpPoly p) :
    coeffIndex (degree + 1) f
      = coeffIndex degree f + (f.coeff degree).toNat * p ^ degree := by
  unfold coeffIndex
  rw [List.range_succ, List.foldl_append]
  simp

/-- `coeffIndex` is the base-`p` interpretation of the per-position residue
digits, exposing Mathlib's `Nat.ofDigits` API. -/
theorem coeffIndex_eq_ofDigits (degree : Nat) (f : Hex.FpPoly p) :
    coeffIndex degree f
      = Nat.ofDigits p ((List.range degree).map (fun i => (f.coeff i).toNat)) := by
  induction degree with
  | zero => simp [coeffIndex]
  | succ d ih =>
    rw [coeffIndex_succ, ih, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_map,
      List.length_range]
    ring

/-- A base-`p` positional sum of `degree` residue digits stays below `p ^ degree`. -/
theorem coeffIndex_lt (degree : Nat) (f : Hex.FpPoly p) :
    coeffIndex degree f < p ^ degree := by
  induction degree with
  | zero => simp [coeffIndex]
  | succ d ih =>
    rw [coeffIndex_succ, pow_succ]
    have hb : (f.coeff d).toNat < p := Hex.ZMod64.toNat_lt _
    have hq : 0 < p ^ d := pow_pos Hex.ZMod64.Bounds.pPos d
    calc coeffIndex d f + (f.coeff d).toNat * p ^ d
        < p ^ d + (f.coeff d).toNat * p ^ d := by omega
      _ = ((f.coeff d).toNat + 1) * p ^ d := by ring
      _ ≤ p * p ^ d := by exact Nat.mul_le_mul_right _ (by omega)
      _ = p ^ d * p := Nat.mul_comm _ _

omit [Hex.ZMod64.Bounds p] in
/-- Extracting digit `j` of a base-`p` number presented through `Nat.ofDigits`. -/
theorem ofDigits_div_pow_mod (hp : 0 < p) (L : List Nat)
    (hL : ∀ x ∈ L, x < p) (j : Nat) (hj : j < L.length) :
    Nat.ofDigits p L / p ^ j % p = L.getD j 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop j hp L hL,
    List.drop_eq_getElem_cons hj, Nat.ofDigits_cons, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hL _ (List.getElem_mem hj)),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

omit [Hex.ZMod64.Bounds p] in
/-- Reconstructing a number below `p ^ degree` from its fixed-width base-`p`
digits. -/
theorem ofDigits_range_map_div_pow_mod (hp : 0 < p) :
    ∀ (degree n : Nat), n < p ^ degree →
      Nat.ofDigits p ((List.range degree).map (fun i => n / p ^ i % p)) = n := by
  intro degree
  induction degree with
  | zero =>
    intro n hn
    simp only [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    simp
  | succ d ih =>
    intro n hn
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.ofDigits_cons]
    have hfun : ((fun i => n / p ^ i % p) ∘ Nat.succ)
        = (fun i => n / p / p ^ i % p) := by
      funext i
      have hpow : p ^ (i + 1) = p * p ^ i := by rw [pow_succ]; ring
      simp only [Function.comp_apply, hpow, Nat.div_div_eq_div_mul]
    rw [hfun]
    have hdiv : n / p < p ^ d := by
      rw [Nat.div_lt_iff_lt_mul hp]
      calc n < p ^ (d + 1) := hn
        _ = p ^ d * p := by rw [pow_succ]
    rw [ih (n / p) hdiv]
    simp only [pow_zero, Nat.div_one]
    exact Nat.mod_add_div n p

/-- Coefficients below the width read back the encoded base-`p` digit. -/
@[simp]
theorem coeff_ofIndexBelowDegree_of_lt (degree index i : Nat) (hi : i < degree) :
    (ofIndexBelowDegree (p := p) degree index).coeff i
      = Hex.ZMod64.ofNat p (index / p ^ i) := by
  unfold ofIndexBelowDegree Hex.FpPoly.ofCoeffs
  rw [Hex.DensePoly.coeff_ofCoeffs]
  simp [Array.getD_eq_getD_getElem?, List.getElem?_range hi]

/-- Coefficients at or beyond the width vanish. -/
@[simp]
theorem coeff_ofIndexBelowDegree_of_ge (degree index i : Nat) (hi : degree ≤ i) :
    (ofIndexBelowDegree (p := p) degree index).coeff i = 0 := by
  apply Hex.DensePoly.coeff_eq_zero_of_size_le
  unfold ofIndexBelowDegree Hex.FpPoly.ofCoeffs
  calc (Hex.DensePoly.ofCoeffs
          ((List.range degree).map (fun i => Hex.ZMod64.ofNat p (index / p ^ i))).toArray).size
      ≤ _ := Hex.DensePoly.size_ofCoeffs_le _
    _ = degree := by simp
    _ ≤ i := hi

/-- The width-`degree` decoder produces a polynomial of size at most `degree`,
hence degree below `degree` whenever the width is positive. -/
theorem degree_lt_of_size_le (g : Hex.FpPoly p) (d : Nat)
    (hsz : g.size ≤ d) (hd : 0 < d) : Hex.FpPoly.degree g < d := by
  rcases Nat.eq_zero_or_pos g.size with h | h
  · have hzero : Hex.FpPoly.degree g = 0 := by
      unfold Hex.FpPoly.degree
      rw [(Hex.DensePoly.degree?_eq_none_iff g).mpr h]; rfl
    omega
  · have hsome : Hex.FpPoly.degree g = g.size - 1 := by
      unfold Hex.FpPoly.degree
      rw [Hex.DensePoly.degree?_eq_some_of_pos_size g h]; rfl
    omega

/-- A polynomial's stored size is at most one more than its `FpPoly.degree`. -/
theorem size_le_degree_succ (f : Hex.FpPoly p) :
    f.size ≤ Hex.FpPoly.degree f + 1 := by
  rcases Nat.eq_zero_or_pos f.size with h | h
  · omega
  · have hsome : Hex.FpPoly.degree f = f.size - 1 := by
      unfold Hex.FpPoly.degree
      rw [Hex.DensePoly.degree?_eq_some_of_pos_size f h]; rfl
    omega

/-- Bounded reduced polynomials encode to indices below `p ^ degree`. -/
theorem coeffIndex_lt_of_degree_lt {degree : Nat} {f : Hex.FpPoly p}
    (_hdeg : Hex.FpPoly.degree f < degree) :
    coeffIndex degree f < p ^ degree :=
  coeffIndex_lt degree f

/-- Decoded indices are represented by polynomials with degree below the
requested bound. The positivity hypothesis is necessary: at `degree = 0` the
index type `Fin (p ^ 0) = Fin 1` is inhabited but the decoder returns the zero
polynomial, whose `FpPoly.degree` is `0`. -/
theorem ofIndexBelowDegree_degree_lt (degree index : Nat) (hd : 0 < degree) :
    Hex.FpPoly.degree (ofIndexBelowDegree (p := p) degree index) < degree := by
  apply degree_lt_of_size_le _ _ _ hd
  unfold ofIndexBelowDegree Hex.FpPoly.ofCoeffs
  calc (Hex.DensePoly.ofCoeffs
          ((List.range degree).map (fun i => Hex.ZMod64.ofNat p (index / p ^ i))).toArray).size
      ≤ _ := Hex.DensePoly.size_ofCoeffs_le _
    _ = degree := by simp

/-- Encoding after decoding recovers the bounded index. -/
@[simp]
theorem coeffIndex_ofIndexBelowDegree (degree : Nat) (index : Fin (p ^ degree)) :
    coeffIndex degree (ofIndexBelowDegree (p := p) degree index.1) = index.1 := by
  rw [coeffIndex_eq_ofDigits]
  have hmap : ((List.range degree).map
        (fun i => ((ofIndexBelowDegree (p := p) degree index.1).coeff i).toNat))
      = (List.range degree).map (fun i => index.1 / p ^ i % p) := by
    apply List.map_congr_left
    intro i hi
    rw [coeff_ofIndexBelowDegree_of_lt degree index.1 i (List.mem_range.mp hi),
      Hex.ZMod64.toNat_ofNat]
  rw [hmap]
  exact ofDigits_range_map_div_pow_mod Hex.ZMod64.Bounds.pPos degree index.1 index.2

/-- Decoding after encoding recovers a polynomial already below the degree
bound. -/
@[simp]
theorem ofIndexBelowDegree_coeffIndex {degree : Nat} {f : Hex.FpPoly p}
    (hdeg : Hex.FpPoly.degree f < degree) :
    ofIndexBelowDegree (p := p) degree (coeffIndex degree f) = f := by
  apply Hex.DensePoly.ext_coeff
  intro j
  rcases Nat.lt_or_ge j degree with hj | hj
  · rw [coeff_ofIndexBelowDegree_of_lt degree (coeffIndex degree f) j hj,
      Hex.ZMod64.ofNat_eq_iff_toNat_eq, coeffIndex_eq_ofDigits]
    have hL : ∀ x ∈ (List.range degree).map (fun i => (f.coeff i).toNat), x < p := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact Hex.ZMod64.toNat_lt _
    have hlen : j < ((List.range degree).map (fun i => (f.coeff i).toNat)).length := by
      simpa [List.length_map, List.length_range] using hj
    rw [ofDigits_div_pow_mod Hex.ZMod64.Bounds.pPos _ hL j hlen,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    simp [List.getElem_map, List.getElem_range]
  · refine (coeff_ofIndexBelowDegree_of_ge degree (coeffIndex degree f) j hj).trans ?_
    exact (Hex.DensePoly.coeff_eq_zero_of_size_le f
      (by have := size_le_degree_succ f; omega)).symm

end FpPoly

namespace FiniteField

variable {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
variable {f : Hex.FpPoly p}
variable {hf : 0 < Hex.FpPoly.degree f}
variable {hp : Hex.Nat.Prime p}
variable {hirr : Hex.FpPoly.Irreducible f}

/-- The executable finite-field wrapper carries Mathlib's `Field` structure
through the field laws already proved for the implementation-facing
`Lean.Grind.Field` hierarchy. -/
noncomputable instance field :
    Field (Hex.GFqField.FiniteField f hf hp hirr) :=
  Field.ofMinimalAxioms (Hex.GFqField.FiniteField f hf hp hirr)
    (by intro a b c; exact Lean.Grind.Semiring.add_assoc a b c)
    (by
      intro a
      calc
        0 + a = a + 0 := Lean.Grind.Semiring.add_comm 0 a
        _ = a := Lean.Grind.Semiring.add_zero a)
    (by intro a; exact Lean.Grind.Ring.neg_add_cancel a)
    (by intro a b c; exact Lean.Grind.Semiring.mul_assoc a b c)
    (by intro a b; exact Lean.Grind.CommSemiring.mul_comm a b)
    (by intro a; exact Lean.Grind.Semiring.one_mul a)
    (by intro a ha; exact Lean.Grind.Field.mul_inv_cancel ha)
    (Lean.Grind.Field.inv_zero (α := Hex.GFqField.FiniteField f hf hp hirr))
    (by intro a b c; exact Lean.Grind.Semiring.left_distrib a b c)
    ⟨0, 1, Hex.GFqField.zero_ne_one f hf hp hirr⟩

/-- Reduced polynomial representatives for the quotient by `f`. -/
abbrev ReducedRep (f : Hex.FpPoly p) : Type :=
  { g : Hex.FpPoly p // Hex.FpPoly.degree g < Hex.FpPoly.degree f }

/-- The executable finite-field wrapper is equivalent to its canonical reduced
polynomial representatives. -/
def reducedRepEquiv :
    HexGF2Mathlib.TypeEquiv
      (Hex.GFqField.FiniteField f hf hp hirr)
      (ReducedRep f) where
  toFun x := ⟨Hex.GFqField.repr x, Hex.GFqField.degree_repr_lt_degree x⟩
  invFun x := Hex.GFqField.ofPoly f hf hp hirr x.1
  left_inv := by
    intro x
    apply Hex.GFqField.ext
    apply Hex.GFqRing.ext
    simp [Hex.GFqField.ofPoly, Hex.GFqField.repr]
  right_inv := by
    intro x
    apply Subtype.ext
    exact Hex.GFqRing.reduceMod_eq_self_of_degree_lt f x.1 x.2

/-- Reduced representatives are indexed by `Fin (p ^ degree f)`. The
positive-degree hypothesis is needed for the decoder's degree bound (see
`FpPoly.ofIndexBelowDegree_degree_lt`); it is supplied at every call site by the
nonconstant-modulus assumption. -/
def reducedRepFinEquiv (f : Hex.FpPoly p) (hf : 0 < Hex.FpPoly.degree f) :
    HexGF2Mathlib.TypeEquiv
      (ReducedRep f)
      (Fin (p ^ Hex.FpPoly.degree f)) where
  toFun x :=
    ⟨FpPoly.coeffIndex (Hex.FpPoly.degree f) x.1,
      FpPoly.coeffIndex_lt_of_degree_lt x.2⟩
  invFun index :=
    ⟨FpPoly.ofIndexBelowDegree (p := p) (Hex.FpPoly.degree f) index.1,
      FpPoly.ofIndexBelowDegree_degree_lt (p := p) (Hex.FpPoly.degree f) index.1 hf⟩
  left_inv := by
    intro x
    exact Subtype.ext (FpPoly.ofIndexBelowDegree_coeffIndex x.2)
  right_inv := by
    intro index
    exact Fin.ext (FpPoly.coeffIndex_ofIndexBelowDegree (p := p)
      (Hex.FpPoly.degree f) index)

/-- Generic finite-field elements are equivalent to the expected finite index
type. -/
noncomputable def finEquiv :
    Hex.GFqField.FiniteField f hf hp hirr ≃
      Fin (p ^ Hex.FpPoly.degree f) :=
  HexGF2Mathlib.TypeEquiv.toEquiv <|
    HexGF2Mathlib.TypeEquiv.trans reducedRepEquiv (reducedRepFinEquiv f hf)

/-- The generic executable finite-field wrapper is finite. -/
noncomputable instance fintype :
    Fintype (Hex.GFqField.FiniteField f hf hp hirr) :=
  Fintype.ofEquiv (Fin (p ^ Hex.FpPoly.degree f)) finEquiv.symm

/-- The generic executable finite-field wrapper has the expected cardinality. -/
@[simp]
theorem fintype_card :
    Fintype.card (Hex.GFqField.FiniteField f hf hp hirr) =
      p ^ Hex.FpPoly.degree f := by
  simpa using Fintype.card_congr (finEquiv (f := f) (hf := hf)
    (hp := hp) (hirr := hirr))

end FiniteField

namespace GFq

variable {p n : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]

/-- Canonical Conway-backed `GFq` values inherit the generic finite-field
enumeration. -/
noncomputable instance fintype (h : Hex.Conway.SupportedEntry p n) :
    Fintype (Hex.GFq p n h) :=
  FiniteField.fintype

/-- Cardinality of the canonical Conway-backed `GFq` in terms of its selected
modulus degree. -/
theorem fintype_card (h : Hex.Conway.SupportedEntry p n) :
    Fintype.card (Hex.GFq p n h) =
      p ^ Hex.FpPoly.degree (Hex.GFq.modulus h) := by
  simp [Hex.GFq, Hex.GFq.modulus]

omit [Hex.ZMod64.PrimeModulus p] in
/-- The committed Conway modulus has the requested extension degree. -/
theorem modulus_degree (h : Hex.Conway.SupportedEntry p n) :
    Hex.FpPoly.degree (Hex.GFq.modulus h) = n := by
  exact Hex.Conway.luebeckConwayPolynomial?_degree_eq
    (f := Hex.GFq.modulus h) (Hex.Conway.luebeckConwayPolynomial?_conwayPoly h)

omit [Hex.ZMod64.PrimeModulus p] in
/-- The committed Conway polynomial has the requested extension degree. This is
the `Conway.conwayPoly`-phrased twin of `modulus_degree`: it is the form `simp`
needs once the `@[simp]` lemma `modulus_eq_conway` has normalised
`GFq.modulus h` to `Conway.conwayPoly p n h`, and together with
`FiniteField.fintype_card` it drives `Fintype.card (GFq p n h)` to `p ^ n`. -/
@[simp]
theorem conwayPoly_degree (h : Hex.Conway.SupportedEntry p n) :
    Hex.FpPoly.degree (Hex.Conway.conwayPoly p n h) = n :=
  modulus_degree h

/-- Cardinality of canonical `GFq p n` as `p ^ n`. -/
@[simp]
theorem fintype_card_eq_pow (h : Hex.Conway.SupportedEntry p n) :
    Fintype.card (Hex.GFq p n h) = p ^ n := by
  rw [fintype_card h, modulus_degree h]

/-- Canonical `GFq` and Mathlib's `GaloisField` have matching cardinalities. -/
theorem card_eq_galoisField_card [Fact p.Prime]
    (h : Hex.Conway.SupportedEntry p n) (hn : n ≠ 0) :
    Fintype.card (Hex.GFq p n h) = Nat.card (GaloisField p n) := by
  rw [fintype_card_eq_pow h, GaloisField.card p n hn]

/-- Canonical `GFq` values are ring-equivalent to Mathlib's `GaloisField`
with the same characteristic and extension degree. -/
noncomputable def equivGaloisField [Fact p.Prime]
    (h : Hex.Conway.SupportedEntry p n) (hn : n ≠ 0) :
    _root_.RingEquiv (Hex.GFq p n h) (GaloisField p n) := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  refine FiniteField.ringEquivOfCardEq (K := Hex.GFq p n h) (K' := GaloisField p n) ?_
  rw [card_eq_galoisField_card (h := h) hn]
  exact Nat.card_eq_fintype_card (α := GaloisField p n)

end GFq

end HexGFqMathlib
