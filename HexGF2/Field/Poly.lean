/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Field.Word

public section

/-!
The arbitrary-degree `GF(2^n)` wrapper, backed by a full `GF2Poly` residue.

Where `GF2n` fits an element in one machine word, `GF2nPoly` carries a packed
polynomial reduced modulo an irreducible of any degree, which is what the
`n >= 64` cases such as GHASH's `GF(2^128)` need.

This file is the representation and its arithmetic laws. The root-count and
Frobenius development sits in `HexGF2.Field.Roots`, and the bundled
`Lean.Grind` instances in `HexGF2.Field.Grind`.
-/

namespace Hex

namespace GF2nPoly

variable {f : GF2Poly} {hirr : GF2Poly.Irreducible f}

private theorem add_pair_swap (a b c d : GF2Poly) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  apply GF2Poly.ext_coeff
  intro n
  rw [GF2Poly.coeff_add_eq_bne, GF2Poly.coeff_add_eq_bne,
    GF2Poly.coeff_add_eq_bne, GF2Poly.coeff_add_eq_bne,
    GF2Poly.coeff_add_eq_bne, GF2Poly.coeff_add_eq_bne]
  cases a.coeff n <;> cases b.coeff n <;> cases c.coeff n <;>
    cases d.coeff n <;> rfl

/-- Equality of packed polynomial representatives follows from equality of
their stored reduced polynomials. -/
theorem eq_of_val_eq {a b : GF2nPoly f hirr}
    (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

/-- Decidable equality on the quotient field `GF2nPoly f hirr`, decided on
the underlying reduced representative `.val`; representatives with equal
`.val` are promoted to equal field elements via `eq_of_val_eq`. -/
instance instDecidableEq : DecidableEq (GF2nPoly f hirr) := fun a b =>
  match decEq a.val b.val with
  | isTrue h => isTrue (eq_of_val_eq h)
  | isFalse h => isFalse (fun hab => h (congrArg GF2nPoly.val hab))

/-- Finite-index coefficient code for the reduced representative of a packed
quotient-field element. -/
@[expose]
def coeffVector (a : GF2nPoly f hirr) : Fin f.degree → Bool :=
  GF2Poly.reducedCoeffVector f.degree a.val

/-- The coefficient code is injective on packed quotient-field elements. -/
theorem eq_of_coeffVector_eq {a b : GF2nPoly f hirr}
    (hcoeff : coeffVector a = coeffVector b) :
    a = b := by
  apply eq_of_val_eq
  exact GF2Poly.eq_of_reducedCoeffVector_eq a.val_reduced b.val_reduced hcoeff

/-- The defining irreducible modulus polynomial of the packed quotient field. -/
@[expose]
def modulus : GF2Poly :=
  f

/-- Zero is a reduced representative modulo any packed irreducible. -/
theorem zero_reduced : (0 : GF2Poly).IsZero ∨ (0 : GF2Poly).degree < f.degree := by
  exact Or.inl rfl

/-- Reduce a packed polynomial to its canonical residue class modulo `f`. -/
@[expose]
def reducePoly (p : GF2Poly) : GF2nPoly f hirr :=
  let r := p % modulus (f := f)
  if hzero : r.isZero = true then
    ⟨r, Or.inl hzero⟩
  else if hdegree : r.degree < f.degree then
    ⟨r, Or.inr hdegree⟩
  else
    ⟨0, zero_reduced (f := f)⟩

/-- The value stored by canonical quotient reduction is the ordinary remainder
modulo the irreducible modulus. -/
@[simp, grind =] theorem reducePoly_val_eq_mod (p : GF2Poly) :
    (reducePoly (f := f) (hirr := hirr) p).val = p % f := by
  unfold reducePoly modulus
  by_cases hzero : (p % f).isZero = true
  · simp [hzero]
  · by_cases hdegree : (p % f).degree < f.degree
    · simp [hzero, hdegree]
    · have hrem := GF2Poly.mod_degree_lt p f hirr.1
      cases hrem with
      | inl hrem_zero => exact False.elim (hzero hrem_zero)
      | inr hrem_degree => exact False.elim (hdegree hrem_degree)

/-- Two raw polynomials pack to the same quotient representative exactly when
they agree modulo `f`; the reduction map is injective up to `f`-residue. -/
@[grind =] theorem reducePoly_eq_iff_mod_eq {p q : GF2Poly} :
    reducePoly (f := f) (hirr := hirr) p =
      reducePoly (f := f) (hirr := hirr) q ↔
    p % f = q % f := by
  constructor
  · intro h
    have hval := congrArg GF2nPoly.val h
    simpa [reducePoly_val_eq_mod (f := f) (hirr := hirr) p,
      reducePoly_val_eq_mod (f := f) (hirr := hirr) q] using hval
  · intro h
    apply eq_of_val_eq
    simp [reducePoly_val_eq_mod, h]

/-- Reducing an already-computed remainder gives the same quotient class as
reducing the original polynomial. -/
theorem reducePoly_mod_eq (p : GF2Poly) :
    reducePoly (f := f) (hirr := hirr) (p % f) =
      reducePoly (f := f) (hirr := hirr) p := by
  rw [reducePoly_eq_iff_mod_eq]
  exact GF2Poly.mod_eq_self_of_reduced (p % f) f
    (GF2Poly.mod_degree_lt p f hirr.1)

/-- Reduction `% f` commutes with addition: reducing the sum of two remainders
gives the same result as reducing the sum directly. This makes addition on the
quotient `GF2nPoly f hirr` well-defined on reduced representatives. -/
private theorem mod_add_mod_eq_mod_add (p q f : GF2Poly) :
    ((p % f) + (q % f)) % f = (p + q) % f := by
  let qp := (GF2Poly.divMod p f).1
  let rp := (GF2Poly.divMod p f).2
  let qq := (GF2Poly.divMod q f).1
  let rq := (GF2Poly.divMod q f).2
  have hp : p = rp + qp * f := by
    have hspec : qp * f + rp = p := by
      simpa [qp, rp] using GF2Poly.divMod_spec p f
    rw [← hspec, GF2Poly.add_comm]
  have hq : q = rq + qq * f := by
    have hspec : qq * f + rq = q := by
      simpa [qq, rq] using GF2Poly.divMod_spec q f
    rw [← hspec, GF2Poly.add_comm]
  have hsum :
      p + q = (rp + rq) + (qp + qq) * f := by
    rw [hp, hq, GF2Poly.left_distrib]
    exact add_pair_swap rp (qp * f) rq (qq * f)
  calc
    ((p % f) + (q % f)) % f = (rp + rq) % f := by rfl
    _ = ((rp + rq) + (qp + qq) * f) % f := by
          exact (GF2Poly.mod_add_mul_right_eq_mod (rp + rq) (qp + qq) f).symm
    _ = (p + q) % f := by rw [hsum]

/-- Reduction `% f` commutes with multiplication: reducing the product of two
remainders gives the same result as reducing the product directly. This makes
multiplication on the quotient `GF2nPoly f hirr` well-defined on reduced
representatives. -/
theorem mod_mul_mod_eq_mod_mul (p q f : GF2Poly) :
    ((p % f) * (q % f)) % f = (p * q) % f := by
  let qp := (GF2Poly.divMod p f).1
  let rp := (GF2Poly.divMod p f).2
  let qq := (GF2Poly.divMod q f).1
  let rq := (GF2Poly.divMod q f).2
  have hp : p = rp + qp * f := by
    have hspec : qp * f + rp = p := by
      simpa [qp, rp] using GF2Poly.divMod_spec p f
    rw [← hspec, GF2Poly.add_comm]
  have hq : q = rq + qq * f := by
    have hspec : qq * f + rq = q := by
      simpa [qq, rq] using GF2Poly.divMod_spec q f
    rw [← hspec, GF2Poly.add_comm]
  let c := qp * rq + (rp * qq + (qp * qq) * f)
  have hmul :
      p * q = rp * rq + c * f := by
    rw [hp, hq]
    calc
      (rp + qp * f) * (rq + qq * f)
          = (rp * rq + rp * (qq * f)) + ((qp * f) * rq + (qp * f) * (qq * f)) := by
              rw [GF2Poly.right_distrib, GF2Poly.left_distrib, GF2Poly.left_distrib]
              exact add_pair_swap (rp * rq) ((qp * f) * rq) (rp * (qq * f))
                ((qp * f) * (qq * f))
      _ = (rp * rq + (qp * f) * rq) + (rp * (qq * f) + (qp * f) * (qq * f)) := by
          exact add_pair_swap (rp * rq) (rp * (qq * f)) ((qp * f) * rq)
            ((qp * f) * (qq * f))
      _ = (rp * rq + (qp * rq) * f) +
            ((rp * qq) * f + ((qp * qq) * f) * f) := by
          have hqprq : (qp * f) * rq = (qp * rq) * f := by
            rw [GF2Poly.mul_assoc qp f rq, GF2Poly.mul_comm f rq,
              ← GF2Poly.mul_assoc qp rq f]
          have hrpqq : rp * (qq * f) = (rp * qq) * f := by
            rw [GF2Poly.mul_assoc rp qq f]
          have hqpqq : (qp * f) * (qq * f) = ((qp * qq) * f) * f := by
            calc
              (qp * f) * (qq * f) = qp * (f * (qq * f)) := by
                rw [GF2Poly.mul_assoc]
              _ = qp * ((f * qq) * f) := by
                rw [GF2Poly.mul_assoc f qq f]
              _ = qp * ((qq * f) * f) := by
                rw [GF2Poly.mul_comm f qq]
              _ = (qp * (qq * f)) * f := by
                rw [GF2Poly.mul_assoc qp (qq * f) f]
              _ = ((qp * qq) * f) * f := by
                rw [GF2Poly.mul_assoc qp qq f]
          rw [hqprq, hrpqq, hqpqq]
      _ = rp * rq + ((qp * rq + (rp * qq + (qp * qq) * f)) * f) := by
          have htail :
              (qp * rq) * f + ((rp * qq) * f + ((qp * qq) * f) * f) =
                (qp * rq + (rp * qq + (qp * qq) * f)) * f := by
            rw [← GF2Poly.left_distrib (rp * qq) ((qp * qq) * f) f,
              ← GF2Poly.left_distrib (qp * rq) (rp * qq + (qp * qq) * f) f]
          rw [GF2Poly.add_assoc, htail]
  calc
    ((p % f) * (q % f)) % f = (rp * rq) % f := by rfl
    _ = (rp * rq + c * f) % f := by
          exact (GF2Poly.mod_add_mul_right_eq_mod (rp * rq) c f).symm
    _ = (p * q) % f := by rw [hmul]

/-- If `f` divides `p` then `p` reduces to `0` mod `f`: the forward direction of
`p % f = 0 ↔ f ∣ p`, used to show a divisible polynomial collapses to the zero
quotient class. -/
private theorem mod_eq_zero_of_dvd {p f : GF2Poly} (hf : f ≠ 0) (h : f ∣ p) :
    p % f = 0 := by
  rcases h with ⟨c, hc⟩
  have hrem_reduced : (p % f).isZero = true ∨ (p % f).degree < f.degree :=
    GF2Poly.mod_degree_lt p f hf
  have hfdvd_rem : f ∣ p % f := by
    let q := (GF2Poly.divMod p f).1
    let r := (GF2Poly.divMod p f).2
    have hspec : q * f + r = p := by
      simpa [q, r] using GF2Poly.divMod_spec p f
    refine ⟨q + c, ?_⟩
    calc
      p % f = r := rfl
      _ = q * f + (q * f + r) := by
        symm
        rw [← GF2Poly.add_assoc, GF2Poly.add_self, GF2Poly.zero_add]
      _ = q * f + p := by rw [hspec]
      _ = q * f + f * c := by rw [hc]
      _ = f * q + f * c := by rw [GF2Poly.mul_comm q f]
      _ = f * (q + c) := by rw [GF2Poly.right_distrib]
  by_cases hzero : p % f = 0
  · exact hzero
  · cases hrem_reduced with
    | inl hzero_isZero =>
        exact GF2Poly.eq_zero_of_isZero hzero_isZero
    | inr hlt =>
        have hle : f.degree ≤ (p % f).degree :=
          GF2Poly.degree_le_of_dvd_nonzero hf hzero hfdvd_rem
        omega

/-- If `p` reduces to `0` mod `f` then `f` divides `p`: the reverse direction of
`p % f = 0 ↔ f ∣ p`, recovering divisibility from a vanishing remainder. -/
private theorem dvd_of_mod_eq_zero {p f : GF2Poly} (h : p % f = 0) :
    f ∣ p := by
  let q := (GF2Poly.divMod p f).1
  have hspec : q * f + p % f = p := by
    simpa [q, GF2Poly.mod] using GF2Poly.divMod_spec p f
  refine ⟨q, ?_⟩
  rw [h] at hspec
  rw [GF2Poly.add_zero] at hspec
  exact hspec.symm.trans (GF2Poly.mul_comm q f)

/-- Canonical additive identity. -/
@[expose]
def zero : GF2nPoly f hirr :=
  ⟨0, zero_reduced (f := f)⟩

instance : Zero (GF2nPoly f hirr) where
  zero := zero

/-- Reducing the zero polynomial gives the quotient zero. -/
@[simp, grind =] theorem reducePoly_zero :
    reducePoly (f := f) (hirr := hirr) 0 = 0 := by
  apply eq_of_val_eq
  rw [reducePoly_val_eq_mod]
  change 0 % f = 0
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- A polynomial reduces to the zero quotient element exactly when the modulus
divides it in `GF(2)[X]`. -/
theorem reducePoly_eq_zero_iff_dvd {p : GF2Poly} (hf : f ≠ 0) :
    reducePoly (f := f) (hirr := hirr) p = 0 ↔ f ∣ p := by
  constructor
  · intro h
    apply dvd_of_mod_eq_zero
    have hval := congrArg GF2nPoly.val h
    rw [reducePoly_val_eq_mod (f := f) (hirr := hirr) p] at hval
    exact hval
  · intro h
    apply eq_of_val_eq
    change (reducePoly (f := f) (hirr := hirr) p).val = (zero (f := f)).val
    simp [reducePoly_val_eq_mod, zero, mod_eq_zero_of_dvd hf h]

/-- A list map is duplicate-free when the map is injective on the list's own
members. Weaker than global injectivity, which is what the element
enumerations need: multiplication by a fixed nonzero quotient element is
injective on the nonzero elements without being injective on all of them. -/
theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {g : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → g a = g b → a = b) :
    (xs.map g).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hyx : y = x := hinj y (by simp [hy]) x (by simp) hxy
        exact hxs.1 (by simpa [hyx] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

/-- Deleting a member of a duplicate-free list by filtering shortens it by
exactly one. The `Nodup` hypothesis is what rules out the filter removing
several copies at once. -/
theorem length_filter_ne_eq_pred_of_mem_nodup
    {α : Type} [DecidableEq α] {z : α} :
    ∀ {xs : List α}, z ∈ xs → xs.Nodup →
      (xs.filter (fun a => decide (a ≠ z))).length = xs.length - 1
  | [], hmem, _ => by
      cases hmem
  | x :: xs, hmem, hnodup => by
      rw [List.nodup_cons] at hnodup
      by_cases hx : x = z
      · have hnot_mem : x ∉ xs := hnodup.1
        have hfilter : xs.filter (fun a => decide (a ≠ z)) = xs := by
          rw [List.filter_eq_self]
          intro a ha
          exact decide_eq_true (fun haz => hnot_mem (by simpa [hx, haz] using ha))
        rw [List.filter_cons_of_neg]
        · rw [hfilter]
          simp
        · simp [hx]
      · have hz_mem_xs : z ∈ xs := by
          cases hmem with
          | head =>
              exact False.elim (hx rfl)
          | tail _ hz =>
              exact hz
        have ih := length_filter_ne_eq_pred_of_mem_nodup hz_mem_xs hnodup.2
        have hlen_pos : 0 < xs.length := List.length_pos_of_mem hz_mem_xs
        rw [List.filter_cons_of_pos]
        · simp only [List.length_cons]
          rw [ih]
          omega
        · exact decide_eq_true hx

/--
Evaluate a Boolean coefficient list as a quotient expression in the class of
`X`. The list is low-coefficient first: `bs[i]` is the coefficient of `X^i`.
-/
@[expose]
def boolListExpression (bs : List Bool) : GF2nPoly f hirr :=
  reducePoly (f := f) (hirr := hirr) (GF2Poly.Internal.ofBoolList bs)

/-- The value of a Boolean quotient expression is the reduced packed
polynomial built from the same coefficient list. -/
theorem boolListExpression_val_eq_mod (bs : List Bool) :
    (boolListExpression (f := f) (hirr := hirr) bs).val =
      GF2Poly.Internal.ofBoolList bs % f := by
  unfold boolListExpression
  rw [reducePoly_val_eq_mod]

/-- Public quotient-field enumeration: all packed representatives in
`GF2[X]/(f)`, obtained by reducing every length-`f.degree` Boolean coefficient
list. This is exposed for finite-field cardinality, root-count, and Rabin
soundness consumers. -/
@[expose]
def elements : List (GF2nPoly f hirr) :=
  (GF2Poly.Internal.coeffBoolLists f.degree).map
    (boolListExpression (f := f) (hirr := hirr))

/-- The quotient field `GF2[X]/(f)` has exactly `2 ^ f.degree` elements, the
expected cardinality of a degree-`f.degree` extension of `GF(2)`. -/
@[simp, grind =] theorem elements_length :
    (elements (f := f) (hirr := hirr)).length = 2 ^ f.degree := by
  simp [elements]

/-- Every packed quotient-field element appears in `elements`. -/
theorem mem_elements (a : GF2nPoly f hirr) :
    a ∈ elements (f := f) (hirr := hirr) := by
  unfold elements
  apply List.mem_map.mpr
  refine ⟨List.ofFn (coeffVector a), ?_, ?_⟩
  · apply GF2Poly.Internal.mem_coeffBoolLists_of_length_eq
    simp
  · apply eq_of_val_eq
    rw [boolListExpression_val_eq_mod]
    have hofBL_red :
        (GF2Poly.Internal.ofBoolList (List.ofFn (coeffVector a))).IsZero ∨
          (GF2Poly.Internal.ofBoolList (List.ofFn (coeffVector a))).degree < f.degree := by
      have h := GF2Poly.Internal.ofBoolList_isZero_or_degree_lt (List.ofFn (coeffVector a))
      simp at h
      exact h
    have hofBL_eq :
        GF2Poly.Internal.ofBoolList (List.ofFn (coeffVector a)) = a.val := by
      apply GF2Poly.eq_of_reducedCoeffVector_eq hofBL_red a.val_reduced
      funext i
      unfold GF2Poly.reducedCoeffVector
      rw [GF2Poly.Internal.coeff_ofBoolList]
      have hi_lt : i.val < (List.ofFn (coeffVector a)).length := by
        rw [List.length_ofFn]; exact i.is_lt
      rw [List.getElem?_eq_getElem hi_lt]
      simp [List.getElem_ofFn, coeffVector, GF2Poly.reducedCoeffVector]
    rw [hofBL_eq]
    exact GF2Poly.mod_eq_self_of_reduced a.val f a.val_reduced

/-- The quotient expression built from an element's coefficient vector is that
element. -/
theorem boolListExpression_coeffVector (a : GF2nPoly f hirr) :
    boolListExpression (f := f) (hirr := hirr) (List.ofFn (coeffVector a)) = a := by
  apply eq_of_val_eq
  rw [boolListExpression_val_eq_mod]
  have hofBL_red :
      (GF2Poly.Internal.ofBoolList (List.ofFn (coeffVector a))).IsZero ∨
        (GF2Poly.Internal.ofBoolList (List.ofFn (coeffVector a))).degree < f.degree := by
    have h := GF2Poly.Internal.ofBoolList_isZero_or_degree_lt (List.ofFn (coeffVector a))
    simp at h
    exact h
  have hofBL_eq :
      GF2Poly.Internal.ofBoolList (List.ofFn (coeffVector a)) = a.val := by
    apply GF2Poly.eq_of_reducedCoeffVector_eq hofBL_red a.val_reduced
    funext i
    unfold GF2Poly.reducedCoeffVector
    rw [GF2Poly.Internal.coeff_ofBoolList]
    have hi_lt : i.val < (List.ofFn (coeffVector a)).length := by
      rw [List.length_ofFn]; exact i.is_lt
    rw [List.getElem?_eq_getElem hi_lt]
    simp [List.getElem_ofFn, coeffVector, GF2Poly.reducedCoeffVector]
  rw [hofBL_eq]
  exact GF2Poly.mod_eq_self_of_reduced a.val f a.val_reduced

/-- Every packed quotient element is generated by a Boolean coefficient list in
the class of `X`, with exactly `f.degree` coefficients. -/
theorem exists_boolListExpression (a : GF2nPoly f hirr) :
    ∃ bs : List Bool,
      bs.length = f.degree ∧
        boolListExpression (f := f) (hirr := hirr) bs = a := by
  refine ⟨List.ofFn (coeffVector a), ?_, boolListExpression_coeffVector
    (f := f) (hirr := hirr) a⟩
  simp

/-- The quotient enumeration has no duplicate elements. -/
theorem elements_nodup :
    (elements (f := f) (hirr := hirr)).Nodup := by
  unfold elements
  apply nodup_map_of_injective
  · exact GF2Poly.Internal.coeffBoolLists_nodup f.degree
  · intro bs hbs bs' hbs' hred
    have hbs_len := GF2Poly.Internal.length_of_mem_coeffBoolLists hbs
    have hbs'_len := GF2Poly.Internal.length_of_mem_coeffBoolLists hbs'
    have hbs_red :
        (GF2Poly.Internal.ofBoolList bs).IsZero ∨
          (GF2Poly.Internal.ofBoolList bs).degree < f.degree := by
      have h := GF2Poly.Internal.ofBoolList_isZero_or_degree_lt bs
      rw [hbs_len] at h
      exact h
    have hbs'_red :
        (GF2Poly.Internal.ofBoolList bs').IsZero ∨
          (GF2Poly.Internal.ofBoolList bs').degree < f.degree := by
      have h := GF2Poly.Internal.ofBoolList_isZero_or_degree_lt bs'
      rw [hbs'_len] at h
      exact h
    have hofBL_eq : GF2Poly.Internal.ofBoolList bs = GF2Poly.Internal.ofBoolList bs' := by
      have hred_val := congrArg GF2nPoly.val hred
      rw [boolListExpression_val_eq_mod, boolListExpression_val_eq_mod] at hred_val
      rw [GF2Poly.mod_eq_self_of_reduced (GF2Poly.Internal.ofBoolList bs) f hbs_red,
        GF2Poly.mod_eq_self_of_reduced (GF2Poly.Internal.ofBoolList bs') f hbs'_red] at hred_val
      exact hred_val
    apply List.ext_getElem (by rw [hbs_len, hbs'_len])
    intro i hi hi'
    have hcoeff : (GF2Poly.Internal.ofBoolList bs).coeff i =
        (GF2Poly.Internal.ofBoolList bs').coeff i :=
      congrArg (fun p : GF2Poly => p.coeff i) hofBL_eq
    rw [GF2Poly.Internal.coeff_ofBoolList, GF2Poly.Internal.coeff_ofBoolList,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hcoeff
    simpa using hcoeff

/-- The quotient has `2 ^ f.degree` canonical representatives. -/
theorem elements_card :
    (elements (f := f) (hirr := hirr)).length = 2 ^ f.degree :=
  elements_length (f := f) (hirr := hirr)

/-- The nonzero packed quotient-field elements, as a duplicate-free sublist of
`elements`. -/
@[expose]
def nonzeroElements : List (GF2nPoly f hirr) :=
  (elements (f := f) (hirr := hirr)).filter (fun a => decide (a ≠ 0))

/-- Membership in `nonzeroElements` is exactly nonzero quotient membership. -/
theorem mem_nonzeroElements (a : GF2nPoly f hirr) :
    a ∈ nonzeroElements (f := f) (hirr := hirr) ↔ a ≠ 0 := by
  simp [nonzeroElements, mem_elements a]

/-- The nonzero quotient enumeration has no duplicates. -/
theorem nonzeroElements_nodup :
    (nonzeroElements (f := f) (hirr := hirr)).Nodup := by
  unfold nonzeroElements
  exact (elements_nodup (f := f) (hirr := hirr)).filter _

/-- There are `2 ^ f.degree - 1` nonzero quotient representatives. -/
theorem nonzeroElements_card :
    (nonzeroElements (f := f) (hirr := hirr)).length = 2 ^ f.degree - 1 := by
  unfold nonzeroElements
  rw [length_filter_ne_eq_pred_of_mem_nodup
    (mem_elements (f := f) (hirr := hirr) 0)
    (elements_nodup (f := f) (hirr := hirr))]
  rw [elements_card]

/-- The quotient class of `X` modulo the packed irreducible `f`. -/
@[expose]
def X : GF2nPoly f hirr :=
  reducePoly (GF2Poly.monomial 1)

/-- Canonical multiplicative identity. -/
@[expose]
def one : GF2nPoly f hirr :=
  reducePoly 1

instance : One (GF2nPoly f hirr) where
  one := one

/-- Natural-number literals reduce to parity in characteristic two. -/
@[expose]
def natCast (k : Nat) : GF2nPoly f hirr :=
  if k % 2 = 0 then zero else one

instance : NatCast (GF2nPoly f hirr) where
  natCast := natCast

instance (k : Nat) : OfNat (GF2nPoly f hirr) k where
  ofNat := natCast k

/-- Addition in characteristic two is XOR on representatives, followed by
canonical reduction modulo `f`. -/
@[expose]
def add (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val + b.val)

instance : Add (GF2nPoly f hirr) where
  add := add

/-- Reducing a polynomial sum agrees with adding the reduced quotient
representatives. -/
theorem reducePoly_add_eq (p q : GF2Poly) :
    reducePoly (f := f) (hirr := hirr) (p + q) =
      reducePoly (f := f) (hirr := hirr)
        ((reducePoly (f := f) (hirr := hirr) p).val +
          (reducePoly (f := f) (hirr := hirr) q).val) := by
  rw [reducePoly_eq_iff_mod_eq, reducePoly_val_eq_mod, reducePoly_val_eq_mod]
  exact (mod_add_mod_eq_mod_add p q f).symm

/-- Negation is the identity in characteristic two. -/
@[expose]
def neg (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  a

instance : Neg (GF2nPoly f hirr) where
  neg := neg

/-- Subtraction coincides with addition in characteristic two. -/
@[expose]
def sub (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  add a b

instance : Sub (GF2nPoly f hirr) where
  sub := sub

/-- Natural scalar multiplication depends only on parity. -/
@[expose]
def nsmul (k : Nat) (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if k % 2 = 0 then 0 else a

instance : SMul Nat (GF2nPoly f hirr) where
  smul := nsmul

/-- Multiplication uses packed `GF2Poly` multiplication followed by reduction
modulo the irreducible defining polynomial. -/
@[expose]
def mul (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val * b.val)

instance : Mul (GF2nPoly f hirr) where
  mul := mul

/-- Reducing a polynomial product agrees with multiplying the reduced quotient
representatives. -/
theorem reducePoly_mul_eq (p q : GF2Poly) :
    reducePoly (f := f) (hirr := hirr) (p * q) =
      reducePoly (f := f) (hirr := hirr)
        ((reducePoly (f := f) (hirr := hirr) p).val *
          (reducePoly (f := f) (hirr := hirr) q).val) := by
  rw [reducePoly_eq_iff_mod_eq, reducePoly_val_eq_mod, reducePoly_val_eq_mod]
  exact (mod_mul_mod_eq_mod_mul p q f).symm

/-- Natural power in the packed quotient field by repeated squaring. -/
@[expose]
def pow (a : GF2nPoly f hirr) (k : Nat) : GF2nPoly f hirr :=
  let rec go (acc base : GF2nPoly f hirr) (k : Nat) : GF2nPoly f hirr :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      let base' := base * base
      go acc' base' (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 a k

/-- Square-and-multiply accumulator loop for `GF2nPoly.pow`: `go acc base k`
computes `acc * base ^ k`. -/
add_decl_doc GF2nPoly.pow.go

instance : Pow (GF2nPoly f hirr) Nat where
  pow := pow

/-- Iterated Frobenius squaring in the packed quotient, starting from a
specified quotient element. -/
@[expose]
def frobeniusIter (a : GF2nPoly f hirr) : Nat → GF2nPoly f hirr
  | 0 => a
  | k + 1 => frobeniusIter a k * frobeniusIter a k

/-- Zero Frobenius iterations leave the quotient element unchanged. -/
@[simp, grind =] theorem frobeniusIter_zero (a : GF2nPoly f hirr) :
    frobeniusIter a 0 = a := rfl

/-- One more Frobenius iteration squares the previous iterate in the quotient
field. -/
@[simp, grind =] theorem frobeniusIter_succ (a : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter a (k + 1) = frobeniusIter a k * frobeniusIter a k := rfl

/-- Frobenius iterates compose by adding their iteration counts. -/
theorem frobeniusIter_add (a : GF2nPoly f hirr) (m n : Nat) :
    frobeniusIter (frobeniusIter a m) n = frobeniusIter a (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      rw [frobeniusIter_succ, ih]
      have hidx : m + (n + 1) = (m + n) + 1 := by omega
      rw [hidx, frobeniusIter_succ]

/-- Iterated quotient squaring of the class of `X` follows the executable
`xpow2kMod` remainder chain used by Rabin soundness. -/
theorem quotient_X_frobeniusIter_eq_reduce_xpow2kMod (k : Nat) :
    frobeniusIter (X (f := f) (hirr := hirr)) k =
      reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k) := by
  induction k with
  | zero =>
      change X (f := f) (hirr := hirr) =
        reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial 1 % f)
      rw [X, reducePoly_mod_eq]
  | succ k ih =>
      calc
        frobeniusIter (X (f := f) (hirr := hirr)) (k + 1)
            = reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k) *
                reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k) := by
                  rw [frobeniusIter_succ, ih]
        _ = reducePoly (f := f) (hirr := hirr)
              ((reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k)).val *
                (reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k)).val) := rfl
        _ = reducePoly (f := f) (hirr := hirr)
              (GF2Poly.xpow2kMod f k * GF2Poly.xpow2kMod f k) := by
                rw [← reducePoly_mul_eq]
        _ = reducePoly (f := f) (hirr := hirr)
              ((GF2Poly.xpow2kMod f k * GF2Poly.xpow2kMod f k) % f) := by
                rw [reducePoly_mod_eq]
        _ = reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f (k + 1)) := by
                rfl

/-- Integer literals reduce to parity. -/
@[expose]
def intCast (k : Int) : GF2nPoly f hirr :=
  natCast k.natAbs

instance : IntCast (GF2nPoly f hirr) where
  intCast := intCast

/-- Integer scalar multiplication depends only on parity. -/
@[expose]
def zsmul (k : Int) (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if k.natAbs % 2 = 0 then 0 else a

instance : SMul Int (GF2nPoly f hirr) where
  smul := zsmul

/-- The extended Euclidean witness supplies an inverse candidate modulo the
packed irreducible. -/
@[expose]
def invPoly (p : GF2Poly) : GF2Poly :=
  (GF2Poly.xgcd p (modulus (f := f))).left

/-- Inversion follows the packed extended-GCD path and uses the usual junk
value `0⁻¹ = 0`. -/
@[expose]
def inv (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if a.val.isZero then
    0
  else
    reducePoly (invPoly (f := f) a.val)

instance : Inv (GF2nPoly f hirr) where
  inv := inv

/-- Division is multiplication by the inverse candidate. -/
@[expose]
def div (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  a * b⁻¹

instance : Div (GF2nPoly f hirr) where
  div := div

/-- Integer exponentiation uses inversion for negative exponents. -/
@[expose]
def zpow (a : GF2nPoly f hirr) : Int → GF2nPoly f hirr
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹

instance : HPow (GF2nPoly f hirr) Int (GF2nPoly f hirr) where
  hPow := zpow

/-- Division in `GF2nPoly` unfolds to multiplication by the multiplicative
inverse. -/
@[grind =] theorem div_eq_mul_inv (a b : GF2nPoly f hirr) :
    a / b = a * b⁻¹ :=
  rfl

/-- The inverse of `0` in `GF2nPoly` is `0` (the field convention that makes
inversion total). -/
@[simp, grind =] theorem inv_zero : (0 : GF2nPoly f hirr)⁻¹ = 0 := by
  have hzeroVal : (0 : GF2nPoly f hirr).val = 0 := by
    simp [OfNat.ofNat, natCast, zero]
  apply eq_of_val_eq
  simp [Inv.inv, inv, hzeroVal]

/-- Every nonzero element of `GF2nPoly` cancels against its inverse, witnessing
that `GF2nPoly` is a field. -/
@[grind =] theorem mul_inv_cancel (a : GF2nPoly f hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hval_ne : a.val ≠ 0 := by
    intro hval
    apply ha
    apply eq_of_val_eq
    change a.val = (zero (f := f) (hirr := hirr)).val
    simpa [zero] using hval
  have hval_nonzero : a.val.isZero = false := by
    cases hzero : a.val.isZero
    · rfl
    · exfalso
      exact hval_ne (GF2Poly.eq_zero_of_isZero hzero)
  apply eq_of_val_eq
  simp [HMul.hMul, Mul.mul, mul, Inv.inv, inv, hval_nonzero, invPoly]
  change (a.val * ((GF2Poly.xgcd a.val f).left % f)) % f =
    (reducePoly (f := f) (hirr := hirr) 1).val
  rw [reducePoly_val_eq_mod]
  exact GF2Poly.mul_mod_xgcd_left_mod_eq_one_of_irreducible_of_nonzero_reduced
    hirr hval_ne a.val_reduced

/-- The value of a quotient product is the polynomial product reduced modulo
the defining irreducible. -/
@[simp, grind =] theorem mul_val (a b : GF2nPoly f hirr) :
    (a * b).val = (a.val * b.val) % f := by
  show (mul a b).val = _
  unfold mul
  rw [reducePoly_val_eq_mod]

/-- The value of the multiplicative identity is `(1 : GF2Poly) % f`. -/
@[simp, grind =] theorem one_val :
    (1 : GF2nPoly f hirr).val = (1 : GF2Poly) % f := by
  show (one (f := f) (hirr := hirr)).val = _
  unfold one
  rw [reducePoly_val_eq_mod]

/-- The value of a quotient sum is the polynomial sum reduced modulo the
defining irreducible. -/
@[simp, grind =] theorem add_val (a b : GF2nPoly f hirr) :
    (a + b).val = (a.val + b.val) % f := by
  show (add a b).val = _
  unfold add
  rw [reducePoly_val_eq_mod]

/-- Negation is the identity on the packed quotient. -/
@[simp, grind =] theorem neg_val (a : GF2nPoly f hirr) : (-a).val = a.val := rfl

/-- Subtraction coincides with addition on the packed quotient. -/
@[simp, grind =] theorem sub_val (a b : GF2nPoly f hirr) :
    (a - b).val = (a.val + b.val) % f := by
  show (sub a b).val = _
  unfold sub
  exact add_val a b

/-- The value of the additive identity is the zero polynomial. -/
@[simp, grind =] theorem zero_val :
    (0 : GF2nPoly f hirr).val = (0 : GF2Poly) := by
  simp [OfNat.ofNat, natCast, zero]

example (a b : GF2nPoly f hirr) :
    ((a * b) + 1).val = ((a.val * b.val) % f + (1 : GF2Poly) % f) % f := by
  simp

/-- A reduced quotient value is its own remainder modulo `f`. -/
theorem val_mod_eq (a : GF2nPoly f hirr) : a.val % f = a.val :=
  GF2Poly.mod_eq_self_of_reduced a.val f a.val_reduced

/-- Addition is commutative on the packed quotient. -/
theorem add_comm (a b : GF2nPoly f hirr) : a + b = b + a := by
  apply eq_of_val_eq
  rw [add_val, add_val, GF2Poly.add_comm]

/-- Addition is associative on the packed quotient. -/
theorem add_assoc (a b c : GF2nPoly f hirr) :
    (a + b) + c = a + (b + c) := by
  apply eq_of_val_eq
  rw [add_val, add_val, add_val, add_val]
  have hleft : (((a.val + b.val) % f) + c.val) % f =
      (a.val + b.val + c.val) % f := by
    have h := mod_add_mod_eq_mod_add (a.val + b.val) c.val f
    rw [val_mod_eq c] at h
    exact h
  have hright : (a.val + ((b.val + c.val) % f)) % f =
      (a.val + (b.val + c.val)) % f := by
    have h := mod_add_mod_eq_mod_add a.val (b.val + c.val) f
    rw [val_mod_eq a] at h
    exact h
  rw [hleft, hright, GF2Poly.add_assoc]

/-- Regroup a sum of two pairs by swapping the inner terms. Commutativity and
associativity give this, but as a single rewrite it keeps the characteristic-two
cancellation arguments from turning into long `rw` chains. -/
theorem add_pair_swap_quot
    (a b c d : GF2nPoly f hirr) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc a b (c + d), ← add_assoc b c d, add_comm b c, add_assoc c b d,
    ← add_assoc a c (b + d)]

/-- The additive identity is a left identity. -/
@[simp, grind =] theorem zero_add (a : GF2nPoly f hirr) :
    (0 : GF2nPoly f hirr) + a = a := by
  apply eq_of_val_eq
  rw [add_val, zero_val, GF2Poly.zero_add, val_mod_eq]

/-- The additive identity is a right identity. -/
@[simp, grind =] theorem add_zero (a : GF2nPoly f hirr) :
    a + (0 : GF2nPoly f hirr) = a := by
  rw [add_comm, zero_add]

/-- Every packed quotient element is its own additive inverse in
characteristic two. -/
@[simp, grind =] theorem add_self (a : GF2nPoly f hirr) : a + a = 0 := by
  apply eq_of_val_eq
  rw [add_val, GF2Poly.add_self]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Multiplication by zero on the right is zero. -/
@[simp, grind =] theorem mul_zero (a : GF2nPoly f hirr) :
    a * (0 : GF2nPoly f hirr) = 0 := by
  apply eq_of_val_eq
  rw [mul_val, zero_val, GF2Poly.mul_zero]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Multiplication by zero on the left is zero. -/
@[simp, grind =] theorem zero_mul (a : GF2nPoly f hirr) :
    (0 : GF2nPoly f hirr) * a = 0 := by
  apply eq_of_val_eq
  rw [mul_val, zero_val, GF2Poly.zero_mul]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Multiplication is commutative on the packed quotient. -/
theorem mul_comm (a b : GF2nPoly f hirr) : a * b = b * a := by
  apply eq_of_val_eq
  rw [mul_val, mul_val, GF2Poly.mul_comm]

/-- Multiplication is associative on the packed quotient. -/
theorem mul_assoc (a b c : GF2nPoly f hirr) :
    (a * b) * c = a * (b * c) := by
  apply eq_of_val_eq
  rw [mul_val, mul_val, mul_val, mul_val]
  have hca : ((a.val * b.val) % f * c.val) % f = (a.val * b.val * c.val) % f := by
    have h := mod_mul_mod_eq_mod_mul (a.val * b.val) c.val f
    rw [val_mod_eq c] at h
    exact h
  have hcb : (a.val * ((b.val * c.val) % f)) % f = (a.val * (b.val * c.val)) % f := by
    have h := mod_mul_mod_eq_mod_mul a.val (b.val * c.val) f
    rw [val_mod_eq a] at h
    exact h
  rw [hca, hcb, GF2Poly.mul_assoc]

/-- The multiplicative identity is a left identity. -/
@[simp, grind =] theorem one_mul (a : GF2nPoly f hirr) :
    (1 : GF2nPoly f hirr) * a = a := by
  apply eq_of_val_eq
  rw [mul_val, one_val]
  have h : ((1 : GF2Poly) % f * a.val) % f = ((1 : GF2Poly) * a.val) % f := by
    have hh := mod_mul_mod_eq_mod_mul 1 a.val f
    rw [val_mod_eq a] at hh
    exact hh
  rw [h, GF2Poly.one_mul, val_mod_eq]

/-- The multiplicative identity is a right identity. -/
@[simp, grind =] theorem mul_one (a : GF2nPoly f hirr) :
    a * (1 : GF2nPoly f hirr) = a := by
  rw [mul_comm, one_mul]

/-- Multiplication distributes over addition on the left in the packed
quotient. -/
theorem left_distrib (a b c : GF2nPoly f hirr) :
    a * (b + c) = a * b + a * c := by
  apply eq_of_val_eq
  rw [mul_val, add_val, add_val, mul_val, mul_val]
  have hmul : (a.val * ((b.val + c.val) % f)) % f =
      (a.val * (b.val + c.val)) % f := by
    have h := mod_mul_mod_eq_mod_mul a.val (b.val + c.val) f
    rw [val_mod_eq a] at h
    exact h
  have hadd : (((a.val * b.val) % f) + ((a.val * c.val) % f)) % f =
      (a.val * b.val + a.val * c.val) % f :=
    mod_add_mod_eq_mod_add (a.val * b.val) (a.val * c.val) f
  rw [hmul, hadd, GF2Poly.right_distrib]

/-- Multiplication distributes over addition on the right in the packed
quotient. -/
theorem right_distrib (a b c : GF2nPoly f hirr) :
    (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, left_distrib, mul_comm c a, mul_comm c b]

/-- Squaring a sum is additive in characteristic two. -/
theorem add_sq (a b : GF2nPoly f hirr) :
    (a + b) * (a + b) = a * a + b * b := by
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) := by
      rw [right_distrib]
    _ = (a * a + a * b) + (b * a + b * b) := by
      rw [left_distrib, left_distrib]
    _ = (a * a + b * b) + (a * b + b * a) := by
      rw [add_comm (b * a) (b * b), add_pair_swap_quot]
    _ = (a * a + b * b) + (a * b + a * b) := by
      rw [mul_comm b a]
    _ = a * a + b * b := by
      rw [add_self, add_zero]

/-- The quotient identity is not zero under a positive-degree modulus. -/
theorem one_ne_zero (hf_pos : 0 < f.degree) :
    (1 : GF2nPoly f hirr) ≠ 0 := by
  intro h
  have hval := congrArg GF2nPoly.val h
  have hone_val : (1 : GF2nPoly f hirr).val = (1 : GF2Poly) := by
    rw [one_val]
    exact GF2Poly.mod_eq_self_of_reduced (1 : GF2Poly) f
      (Or.inr (by
        change (GF2Poly.monomial 0).degree < f.degree
        rw [show (GF2Poly.monomial 0).degree = 0 from by
          exact GF2Poly.degree_eq_of_degree?_eq_some (GF2Poly.degree?_monomial 0)]
        exact hf_pos))
  rw [hone_val, zero_val] at hval
  have hcoeff := congrArg (fun p : GF2Poly => p.coeff 0) hval
  change (GF2Poly.monomial 0).coeff 0 = (0 : GF2Poly).coeff 0 at hcoeff
  rw [GF2Poly.coeff_monomial_self, GF2Poly.coeff_zero] at hcoeff
  contradiction

end GF2nPoly

end Hex
