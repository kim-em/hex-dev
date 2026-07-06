/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Grind.Ring.Basic
public import Init.Data.List.Lemmas
public import HexPoly.Operations
public import HexPoly.Euclid.Reconstruction
import all HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.MulRing
import all HexPoly.Euclid.Reconstruction

public section
set_option backward.proofsInPublic true

/-!
Integer content and primitive part for `DensePoly Int`, with the
content-divides-coefficient and content/primitive-part multiplicativity
supporting lemmas.
-/
namespace Hex

universe u

namespace DensePoly
/-- The nonnegative gcd of the coefficients of an integer polynomial.

Kernel-facing specification: one fold over the spec-level coefficient list.
Compiled code runs the `Array.foldl` loop `contentNatImpl` via the `@[csimp]`
proof `contentNat_eq_impl`. -/
@[expose]
noncomputable def contentNat (p : DensePoly Int) : Nat :=
  p.toList.foldl (fun acc coeff => Nat.gcd acc coeff.natAbs) 0

/-- Runtime implementation of `contentNat`: a direct `Array.foldl` with no
intermediate list (value-equal to `contentNat` by `contentNat_eq_impl`,
registered `@[csimp]`). -/
@[expose]
def contentNatImpl (p : DensePoly Int) : Nat :=
  p.toArray.foldl (fun acc coeff => Nat.gcd acc coeff.natAbs) 0

/-- The spec `contentNat` and the `Array.foldl` runtime loop agree. -/
theorem contentNat_eq_contentNatImpl (p : DensePoly Int) :
    contentNat p = contentNatImpl p := by
  unfold contentNat contentNatImpl
  rw [← Array.foldl_toList]
  rfl

/-- Register the `Array.foldl` loop as the compiled implementation of
`contentNat`. -/
@[csimp]
theorem contentNat_eq_impl : @contentNat = @contentNatImpl :=
  funext contentNat_eq_contentNatImpl

/-- The integer content of a polynomial. This is always nonnegative. -/
@[expose]
def content (p : DensePoly Int) : Int :=
  Int.ofNat (contentNat p)

/-- The primitive part obtained by dividing every coefficient by the content.

Kernel-facing specification: one map over the spec-level coefficient list.
Compiled code runs the `Array.map` pass `primitivePartImpl` via the `@[csimp]`
proof `primitivePart_eq_impl`. -/
@[expose]
noncomputable def primitivePart (p : DensePoly Int) : DensePoly Int :=
  let cNat := contentNat p
  if cNat = 0 then
    0
  else
    let c := Int.ofNat cNat
    ofCoeffs (p.toList.map (fun coeff => coeff / c)).toArray

/-- Runtime implementation of `primitivePart`: one `Array.map` pass over the
stored coefficients (value-equal to `primitivePart` by
`primitivePart_eq_impl`, registered `@[csimp]`). -/
@[expose]
def primitivePartImpl (p : DensePoly Int) : DensePoly Int :=
  let cNat := contentNatImpl p
  if cNat = 0 then
    0
  else
    let c := Int.ofNat cNat
    ofCoeffs (p.toArray.map (fun coeff => coeff / c))

/-- The spec `primitivePart` and the `Array.map` runtime pass agree. -/
theorem primitivePart_eq_primitivePartImpl (p : DensePoly Int) :
    primitivePart p = primitivePartImpl p := by
  simp only [primitivePart, primitivePartImpl, ← contentNat_eq_contentNatImpl]
  by_cases h : contentNat p = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    congr 1
    show ((p.toArray.toList).map
        (fun coeff => coeff / Int.ofNat (contentNat p))).toArray = _
    rw [← Array.toList_map, Array.toArray_toList]

/-- Register the `Array.map` pass as the compiled implementation of
`primitivePart`. -/
@[csimp]
theorem primitivePart_eq_impl : @primitivePart = @primitivePartImpl :=
  funext primitivePart_eq_primitivePartImpl

/-- Folding `Nat.gcd` over `xs` starting from `acc` yields a divisor of the seed `acc`, the base step for showing `contentNat` divides each coefficient. -/
private theorem foldl_gcd_dvd_acc (xs : List Nat) (acc : Nat) :
    xs.foldl (fun g x => Nat.gcd g x) acc ∣ acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      exact Nat.dvd_trans (ih (Nat.gcd acc x)) (Nat.gcd_dvd_left acc x)

/-- The running `Nat.gcd` fold over `xs` divides every member `x` of the list, the step giving `contentNat ∣ coeff` for coefficients actually present. -/
private theorem foldl_gcd_dvd_of_mem {xs : List Nat} {x acc : Nat}
    (hx : x ∈ xs) :
    xs.foldl (fun g x => Nat.gcd g x) acc ∣ x := by
  induction xs generalizing acc with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp at hx
      cases hx with
      | inl hxy =>
          subst hxy
          exact Nat.dvd_trans (foldl_gcd_dvd_acc ys (Nat.gcd acc x))
            (Nat.gcd_dvd_right acc x)
      | inr hy =>
          exact ih (acc := Nat.gcd acc y) hy

/-- `contentNat p`, viewed as an `Int`, divides every coefficient `p.coeff n`, the forward half of content-divides-coefficient reasoning. -/
private theorem contentNat_dvd_coeff (p : DensePoly Int) (n : Nat) :
    (contentNat p : Int) ∣ p.coeff n := by
  by_cases hn : n < p.size
  · rw [Int.ofNat_dvd_left]
    unfold contentNat coeff toList toArray
    have hmem : p.coeffs[n].natAbs ∈ p.coeffs.toList.map Int.natAbs := by
      apply List.mem_map.mpr
      refine ⟨p.coeffs[n], ?_, rfl⟩
      rw [List.mem_iff_getElem]
      exact ⟨n, by simpa [size] using hn, by simp [Array.getElem_toList]; rfl⟩
    have hfold := foldl_gcd_dvd_of_mem (acc := 0) hmem
    have hcoeff : (p.coeffs.getD n (Zero.zero : Int)).natAbs = p.coeffs[n].natAbs := by
      change (p.coeffs.getD n (0 : Int)).natAbs = p.coeffs[n].natAbs
      rw [Array.getElem_eq_getD (0 : Int)]
    rw [hcoeff]
    simpa only [List.foldl_map] using hfold
  · have hnle : p.size ≤ n := Nat.le_of_not_gt hn
    rw [coeff_eq_zero_of_size_le p hnle]
    exact ⟨0, by rw [Int.mul_zero]; rfl⟩

/-- The content of an integer polynomial divides every coefficient. -/
theorem content_dvd_coeff (p : DensePoly Int) (n : Nat) :
    content p ∣ p.coeff n := by
  simpa [content] using contentNat_dvd_coeff p n

/-- Any `d` dividing the seed `acc` and every member of `xs` also divides their `Nat.gcd` fold, the converse direction characterising `contentNat` as a greatest common divisor. -/
private theorem dvd_foldl_gcd_of_dvd_mem (xs : List Nat) (d acc : Nat)
    (hacc : d ∣ acc) (hxs : ∀ x, x ∈ xs → d ∣ x) :
    d ∣ xs.foldl (fun g x => Nat.gcd g x) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Nat.dvd_gcd hacc (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

/-- Any `d` dividing every coefficient of `p` divides `contentNat p`, the universal property making `contentNat` the gcd of the coefficients. -/
private theorem dvd_contentNat_of_dvd_coeff (p : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ p.coeff n) :
    d ∣ contentNat p := by
  unfold contentNat
  rw [← List.foldl_map]
  apply dvd_foldl_gcd_of_dvd_mem
  · exact Nat.dvd_zero d
  · intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨coeff, hcoeff, rfl⟩
    rw [List.mem_iff_getElem] at hcoeff
    rcases hcoeff with ⟨n, hn, hget⟩
    have hcoeff_eq : p.coeff n = coeff := by
      have hnArray : n < p.coeffs.size := by
        rw [length_toList] at hn
        exact hn
      have hgetArray : p.coeffs[n] = coeff := by
        simpa [toList, toArray, Array.getElem_toList] using hget
      change p.coeffs.getD n (0 : Int) = coeff
      rw [← Array.getElem_eq_getD (0 : Int)]
      exact hgetArray
    have hdiv := h n
    rw [hcoeff_eq] at hdiv
    rwa [Int.ofNat_dvd_left] at hdiv

/-- Every integer `a` is a unit-signed multiple of its `natAbs`, supplying the `±1` factor relating a coefficient to its absolute value in content arguments. -/
private theorem int_natAbs_signed_mul (a : Int) :
    ∃ s : Int, s * a = Int.ofNat a.natAbs := by
  rcases Int.natAbs_eq a with ha | ha
  · exact ⟨1, by rw [ha]; grind⟩
  · exact ⟨-1, by rw [ha]; grind⟩

/-- `Nat.gcd a b` admits an integer Bezout combination `x * a + y * b`, the Bezout identity underlying primitive-part divisibility reasoning. -/
private theorem nat_gcd_bezout (a b : Nat) :
    ∃ x y : Int, x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) := by
  induction a, b using Nat.gcd.induction with
  | H0 b =>
      exact ⟨0, 1, by simp [Nat.gcd_zero_left]⟩
  | H1 a b hpos ih =>
      rcases ih with ⟨x, y, hxy⟩
      refine ⟨y - x * (b / a : Nat), x, ?_⟩
      have hmod : ((b % a : Nat) : Int) = (b : Int) - (b / a : Nat) * (a : Int) := by
        have h := congrArg (fun n : Nat => (n : Int)) (Nat.mod_add_div b a)
        change ((b % a : Nat) : Int) + ((a * (b / a) : Nat) : Int) = (b : Int) at h
        rw [Int.natCast_mul] at h
        rw [Int.mul_comm ((a : Int)) ((b / a : Nat) : Int)] at h
        omega
      rw [Nat.gcd_rec, ← hxy]
      calc
        (y - x * (b / a : Nat)) * (a : Int) + x * (b : Int) =
            x * ((b : Int) - (b / a : Nat) * (a : Int)) + y * (a : Int) := by
              grind
        _ = x * (b % a : Nat) + y * (a : Int) := by
              rw [← hmod]

/-- Summing a list of integers from a seed `z` equals `z` plus the sum from `0`, the accumulator-extraction lemma for additive folds. -/
private theorem list_foldl_add_int (xs : List Int) (z : Int) :
    xs.foldl (fun s t => s + t) z = z + xs.foldl (fun s t => s + t) 0 := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (z + x), ih (0 + x)]
      grind

/-- If `d` divides every member of `xs` then it divides their additive fold, the divisibility-of-sum step for integer lists. -/
private theorem dvd_list_foldl_add_int_of_forall
    (d : Int) (xs : List Int) (h : ∀ x ∈ xs, d ∣ x) :
    d ∣ xs.foldl (fun s t => s + t) 0 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [list_foldl_add_int xs (0 + x)]
      simpa using Int.dvd_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- If `d` divides each `term x` for `x ∈ xs` then it divides the additive fold of `term` over `xs`, the divisibility-of-sum step for indexed term families. -/
private theorem dvd_list_foldl_add_term_of_forall
    (d : Int) (xs : List Nat) (term : Nat → Int)
    (h : ∀ x ∈ xs, d ∣ term x) :
    d ∣ xs.foldl (fun s x => s + term x) 0 := by
  have hmap : ∀ y ∈ xs.map term, d ∣ y := by
    intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h x hx
  simpa [List.foldl_map] using dvd_list_foldl_add_int_of_forall d (xs.map term) hmap

/-- The accumulator-extraction lemma for an additive fold of `term x`, pulling the seed `z` in front of the fold from `0`. -/
private theorem list_foldl_add_term_int
    (xs : List Nat) (term : Nat → Int) (z : Int) :
    xs.foldl (fun s x => s + term x) z =
      z + xs.foldl (fun s x => s + term x) 0 := by
  simpa [List.foldl_map] using list_foldl_add_int (xs.map term) z

/-- The difference of the additive folds of `f` and `g` equals the additive fold of `fun x => f x - g x`, the linearity step combining two term-family sums. -/
private theorem foldl_add_int_sub_terms
    (xs : List Nat) (f g : Nat → Int) :
    xs.foldl (fun s x => s + f x) 0 -
      xs.foldl (fun s x => s + g x) 0 =
    xs.foldl (fun s x => s + (f x - g x)) 0 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [list_foldl_add_term_int xs f (0 + f x), list_foldl_add_term_int xs g (0 + g x),
        list_foldl_add_term_int xs (fun x => f x - g x) (0 + (f x - g x)), ← ih]
      grind

/-- If `d` divides the additive fold of `f` and divides each `f x - g x`, then it divides the additive fold of `g`, transporting divisibility across a term-wise congruence. -/
private theorem dvd_foldl_add_term_of_dvd_congr
    (d : Int) (xs : List Nat) (f g : Nat → Int)
    (hf : d ∣ xs.foldl (fun s x => s + f x) 0)
    (hcongr : ∀ x ∈ xs, d ∣ f x - g x) :
    d ∣ xs.foldl (fun s x => s + g x) 0 := by
  have hdiff : d ∣ xs.foldl (fun s x => s + (f x - g x)) 0 :=
    dvd_list_foldl_add_term_of_forall d xs (fun x => f x - g x) hcongr
  have hsub : d ∣
      xs.foldl (fun s x => s + f x) 0 -
        xs.foldl (fun s x => s + (f x - g x)) 0 :=
    Int.dvd_sub hf hdiff
  have hrewrite :
      xs.foldl (fun s x => s + f x) 0 -
        xs.foldl (fun s x => s + (f x - g x)) 0 =
      xs.foldl (fun s x => s + g x) 0 := by
    have hfg := foldl_add_int_sub_terms xs f g
    grind
  rwa [hrewrite] at hsub

/-- Over a `Nodup` index list, if `d` divides the whole additive fold and every term except the one at `idx`, then it divides the `idx` term, the single-term isolation step for convolution-coefficient divisibility. -/
private theorem dvd_term_of_dvd_foldl_add_of_dvd_others
    (d : Int) :
    ∀ (xs : List Nat) (term : Nat → Int) (idx : Nat),
      xs.Nodup →
      idx ∈ xs →
      d ∣ xs.foldl (fun s x => s + term x) 0 →
      (∀ r, r ∈ xs → r ≠ idx → d ∣ term r) →
      d ∣ term idx
  | [], _term, _idx, _hnodup, hmem, _hsum, _hothers => by
      cases hmem
  | x :: xs, term, idx, hnodup, hmem, hsum, hothers => by
      simp only [List.foldl_cons] at hsum
      have hfold :
          xs.foldl (fun s x => s + term x) (0 + term x) =
            term x + xs.foldl (fun s x => s + term x) 0 := by
        simpa [List.foldl_map] using list_foldl_add_int (xs.map term) (0 + term x)
      rw [hfold] at hsum
      have hnodup_tail : xs.Nodup := hnodup.tail
      have hx_not_mem : x ∉ xs := by
        rw [List.nodup_cons] at hnodup
        exact hnodup.1
      by_cases hxidx : x = idx
      · subst idx
        have htail : d ∣ xs.foldl (fun s x => s + term x) 0 := by
          apply dvd_list_foldl_add_term_of_forall
          intro y hy
          exact hothers y (List.mem_cons_of_mem x hy) (by
            intro hyx
            exact hx_not_mem (by simpa [hyx] using hy))
        have hdiff := Int.dvd_sub hsum htail
        simpa using hdiff
      · have hxdiv : d ∣ term x :=
          hothers x List.mem_cons_self hxidx
        have htail_sum : d ∣ xs.foldl (fun s x => s + term x) 0 := by
          have hdiff := Int.dvd_sub hsum hxdiv
          have heq :
              term x + xs.foldl (fun s x => s + term x) 0 - term x =
                xs.foldl (fun s x => s + term x) 0 := by
            grind
          rwa [heq] at hdiff
        have hidx_mem_tail : idx ∈ xs := by
          rcases List.mem_cons.mp hmem with hidx | htail
          · exact False.elim (hxidx hidx.symm)
          · exact htail
        exact dvd_term_of_dvd_foldl_add_of_dvd_others d xs term idx
          hnodup_tail hidx_mem_tail htail_sum
          (fun r hr hri => hothers r (List.mem_cons_of_mem x hr) hri)

private def finiteCoeffConvolution (pCoeff qCoeff : Nat → Int) (n : Nat) : Int :=
  (List.range (n + 1)).foldl (fun acc r => acc + pCoeff r * qCoeff (n - r)) 0

private def finiteCoeffFamilyPoly (coeff : Nat → Int) (bound : Nat) : DensePoly Int :=
  ofCoeffs ((List.range (bound + 1)).map coeff).toArray

/-- `finiteCoeffFamilyPoly coeff bound` reads back its defining coefficient
`coeff i` at every index `i ≤ bound`. -/
private theorem finiteCoeffFamilyPoly_coeff_of_le
    (coeff : Nat → Int) (bound i : Nat) (hi : i ≤ bound) :
    (finiteCoeffFamilyPoly coeff bound).coeff i = coeff i := by
  unfold finiteCoeffFamilyPoly
  rw [coeff_ofCoeffs_list]
  simp [hi, Nat.lt_succ_iff]

/-- `finiteCoeffFamilyPoly coeff bound` has coefficient `0` at every index `i`
past its bound (`bound < i`). -/
private theorem finiteCoeffFamilyPoly_coeff_of_lt
    (coeff : Nat → Int) (bound i : Nat) (hi : bound < i) :
    (finiteCoeffFamilyPoly coeff bound).coeff i = 0 := by
  unfold finiteCoeffFamilyPoly
  rw [coeff_ofCoeffs_list]
  simp [hi, Nat.lt_succ_iff]
  rfl

/-- `dvd_finiteCoeffConvolution_term_of_dvd_others`: if `d` divides the finite
convolution `finiteCoeffConvolution pCoeff qCoeff n` and every other term, then
it divides the single term `pCoeff i * qCoeff (n - i)`. -/
private theorem dvd_finiteCoeffConvolution_term_of_dvd_others
    (pCoeff qCoeff : Nat → Int) (d n i : Nat)
    (hi : i < n + 1)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hothers : ∀ r, r < n + 1 → r ≠ i → (d : Int) ∣ pCoeff r * qCoeff (n - r)) :
    (d : Int) ∣ pCoeff i * qCoeff (n - i) := by
  exact dvd_term_of_dvd_foldl_add_of_dvd_others (d : Int) (List.range (n + 1))
    (fun r => pCoeff r * qCoeff (n - r)) i
    List.nodup_range (List.mem_range.mpr hi) hprod
    (fun r hr hri => hothers r (List.mem_range.mp hr) hri)

/-- `dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms`: if `d`
divides the degree-`i+j` convolution and every product `pCoeff r * qCoeff s` with
`r + s = i + j` and `r ≠ i`, then it divides the `(i, j)` product
`pCoeff i * qCoeff j`. -/
private theorem dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms
    (pCoeff qCoeff : Nat → Int) (d i j : Nat)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff (i + j))
    (hothers :
      ∀ r s, r + s = i + j → r ≠ i → (d : Int) ∣ pCoeff r * qCoeff s) :
    (d : Int) ∣ pCoeff i * qCoeff j := by
  have hterm :
      (d : Int) ∣ pCoeff i * qCoeff (i + j - i) :=
    dvd_finiteCoeffConvolution_term_of_dvd_others
      pCoeff qCoeff d (i + j) i (by omega) hprod (by
        intro r hr hri
        exact hothers r (i + j - r) (by omega) hri)
  have hsub : i + j - i = j := by omega
  simpa [hsub] using hterm

/-- `dvd_coeff_product_last_of_dvd_finiteCoeffConvolution_of_dvd_larger_left_products`:
refines the previous lemma to derive `d ∣ pCoeff i * qCoeff k` from `d` dividing
`qCoeff` above index `k` together with every larger-left product
`pCoeff r * qCoeff (i + k - r)` (`i < r`). -/
private theorem dvd_coeff_product_last_of_dvd_finiteCoeffConvolution_of_dvd_larger_left_products
    (pCoeff qCoeff : Nat → Int) (d i k : Nat)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff (i + k))
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hlarger :
      ∀ r, i < r → (d : Int) ∣ pCoeff r * qCoeff (i + k - r)) :
    (d : Int) ∣ pCoeff i * qCoeff k := by
  exact dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms
    pCoeff qCoeff d i k hprod (by
      intro r s hrs hri
      by_cases hri_lt : r < i
      · have hks : k < s := by omega
        exact Int.dvd_mul_of_dvd_right (hqAbove s hks)
      · have hir : i < r := by omega
        have hs : s = i + k - r := by omega
        simpa [hs] using hlarger r hir)

/-- `dvd_finiteCoeffConvolution_last_of_boundaries_and_larger_left`: derives
`d ∣ pCoeff i * qCoeff k` from divisibility of `qCoeff` above `k`, of every
product whose left index exceeds `bound`, and of the larger-left products with
`i < r ≤ bound`. -/
private theorem dvd_finiteCoeffConvolution_last_of_boundaries_and_larger_left
    (pCoeff qCoeff : Nat → Int) (d bound i k : Nat)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff (i + k))
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s)
    (hlarger :
      ∀ r, i < r → r ≤ bound → (d : Int) ∣ pCoeff r * qCoeff (i + k - r)) :
    (d : Int) ∣ pCoeff i * qCoeff k := by
  exact dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms
    pCoeff qCoeff d i k hprod (by
      intro r s hrs hri
      by_cases hri_lt : r < i
      · have hks : k < s := by omega
        exact Int.dvd_mul_of_dvd_right (hqAbove s hks)
      · have hir : i < r := by omega
        by_cases hr : r ≤ bound
        · have hs : s = i + k - r := by omega
          simpa [hs] using hlarger r hir hr
        · exact hleft r s (Nat.lt_of_not_ge hr))

/-- `finiteToeplitzMcCoyRow_of_larger_left_products`: applies the boundary
descent across the whole row, giving `d ∣ pCoeff i * qCoeff k` for every
`i ≤ bound` once all convolutions up to `bound + k`, the `qCoeff`-above-`k`,
boundary, and larger-left hypotheses hold. -/
private theorem finiteToeplitzMcCoyRow_of_larger_left_products
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod : ∀ n, n ≤ bound + k → (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s)
    (hlarger :
      ∀ i, i ≤ bound →
        ∀ r, i < r → r ≤ bound → (d : Int) ∣ pCoeff r * qCoeff (i + k - r)) :
    ∀ i, i ≤ bound → (d : Int) ∣ pCoeff i * qCoeff k := by
  intro i hi
  exact dvd_finiteCoeffConvolution_last_of_boundaries_and_larger_left
    pCoeff qCoeff d bound i k (hprod (i + k) (by omega)) hqAbove hleft
    (hlarger i hi)

/-- `dvd_diagonalMulCoeffTerm_of_dvd_mul_coeff_of_dvd_other_diagonal_terms`: if
`d` divides `(p * q).coeff n` and every diagonal term
`diagonalMulCoeffTerm p q n r` with `r ≠ i`, then it divides the `i`-th diagonal
term. -/
private theorem dvd_diagonalMulCoeffTerm_of_dvd_mul_coeff_of_dvd_other_diagonal_terms
    (p q : DensePoly Int) (d n i : Nat)
    (hprod : (d : Int) ∣ (p * q).coeff n)
    (hothers : ∀ r, r ≠ i → (d : Int) ∣ diagonalMulCoeffTerm p q n r) :
    (d : Int) ∣ diagonalMulCoeffTerm p q n i := by
  by_cases hi : i < n + 1
  · have hsum :
        (d : Int) ∣ (List.range (n + 1)).foldl
          (fun s r => s + diagonalMulCoeffTerm p q n r) 0 := by
      rw [← diagonalSum_eq_degree_bound p q n, ← mulCoeffSum_eq_diagonal p q n, ← coeff_mul p q n]
      exact hprod
    exact dvd_term_of_dvd_foldl_add_of_dvd_others (d : Int) (List.range (n + 1))
      (fun r => diagonalMulCoeffTerm p q n r) i
      List.nodup_range (List.mem_range.mpr hi) hsum
      (fun r _hr hri => hothers r hri)
  · have hni : n < i := by omega
    rw [diagonalMulCoeffTerm_eq_zero_of_degree_lt p q n i hni]
    simp

/-- `dvd_coeff_mul_of_dvd_mul_coeff_of_dvd_other_diagonal_products`: the
`DensePoly Int` analogue — if `d` divides `(p * q).coeff (i + j)` and every
product `p.coeff r * q.coeff s` with `r + s = i + j` and `r ≠ i`, then it divides
`p.coeff i * q.coeff j`. -/
private theorem dvd_coeff_mul_of_dvd_mul_coeff_of_dvd_other_diagonal_products
    (p q : DensePoly Int) (d i j : Nat)
    (hprod : (d : Int) ∣ (p * q).coeff (i + j))
    (hothers :
      ∀ r s, r + s = i + j → r ≠ i → (d : Int) ∣ p.coeff r * q.coeff s) :
    (d : Int) ∣ p.coeff i * q.coeff j := by
  have hterm :
      (d : Int) ∣ diagonalMulCoeffTerm p q (i + j) i :=
    dvd_diagonalMulCoeffTerm_of_dvd_mul_coeff_of_dvd_other_diagonal_terms
      p q d (i + j) i hprod (by
        intro r hri
        unfold diagonalMulCoeffTerm
        by_cases hr : i + j < r
        · simp [hr]
        · simp [hr]
          exact hothers r (i + j - r) (by omega) hri)
  unfold diagonalMulCoeffTerm at hterm
  have hnot : ¬ i + j < i := by omega
  simpa [hnot] using hterm

/-- `dvd_coeff_mul_last_of_dvd_mul_coeff_of_dvd_larger_left_products`: the
`DensePoly Int` analogue concluding `d ∣ p.coeff i * q.coeff k` from `d`
dividing `q.coeff` above `k` and every larger-left product
`p.coeff r * q.coeff (i + k - r)` (`i < r`). -/
private theorem dvd_coeff_mul_last_of_dvd_mul_coeff_of_dvd_larger_left_products
    (p q : DensePoly Int) (d i k : Nat)
    (hprod : (d : Int) ∣ (p * q).coeff (i + k))
    (hqAbove : ∀ s, k < s → (d : Int) ∣ q.coeff s)
    (hlarger :
      ∀ r, i < r → (d : Int) ∣ p.coeff r * q.coeff (i + k - r)) :
    (d : Int) ∣ p.coeff i * q.coeff k := by
  exact dvd_coeff_mul_of_dvd_mul_coeff_of_dvd_other_diagonal_products
    p q d i k hprod (by
      intro r s hrs hri
      by_cases hri_lt : r < i
      · have hks : k < s := by omega
        exact Int.dvd_mul_of_dvd_right (hqAbove s hks)
      · have hir : i < r := by omega
        have hs : s = i + k - r := by omega
        simpa [hs] using hlarger r hir)

/-- `mcCoy_grid_band_descent`: the strong-induction descent over the `(i, j)`
grid — if predicate `D` holds whenever the left index exceeds `bound` and is
preserved by the step from all larger-left cells, then `D i j` holds for every
`i` and every `j ≤ k`. -/
private theorem mcCoy_grid_band_descent
    (D : Nat → Nat → Prop) (bound k : Nat)
    (hRight : ∀ r s, bound < r → D r s)
    (hstep : ∀ i j, i ≤ bound → j ≤ k →
      (∀ r, i < r → D r (i + j - r)) → D i j) :
    ∀ i j, j ≤ k → D i j := by
  intro i
  by_cases hi : i ≤ bound
  · let m := bound - i
    have hm : bound - i = m := rfl
    clear_value m
    revert i
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro i hi hm j hj
        exact hstep i j hi hj (by
          intro r hir
          by_cases hr : r ≤ bound
          · have hltm : bound - r < m := by omega
            exact ih (bound - r) hltm r hr rfl (i + j - r) (by omega)
          · exact hRight r (i + j - r) (Nat.lt_of_not_ge hr))
  · intro j _hj
    exact hRight i j (Nat.lt_of_not_ge hi)

/-- `mcCoy_top_row_descent`: the top-row corollary of `mcCoy_grid_band_descent`
— under the same boundary and step hypotheses, `D i k` holds for every `i`. -/
private theorem mcCoy_top_row_descent
    (D : Nat → Nat → Prop) (bound k : Nat)
    (hRight : ∀ r s, bound < r → D r s)
    (hstep : ∀ i j, i ≤ bound → j ≤ k →
      (∀ r, i < r → D r (i + j - r)) → D i j) :
    ∀ i, D i k := by
  intro i
  exact mcCoy_grid_band_descent D bound k hRight hstep i k (Nat.le_refl k)

/-- `list_natAbs_gcd_bezout_aux`: starting from an accumulator `acc`, produces a
scalar `a` and integer weights expressing the running natAbs-gcd of the
coefficient list as `a * acc` plus the weighted `zipWith` fold-sum of the
coefficients. -/
private theorem list_natAbs_gcd_bezout_aux (xs : List Int) (acc : Nat) :
    ∃ a : Int, ∃ weights : List Int,
      weights.length = xs.length ∧
      a * (acc : Int) +
          (List.zipWith (fun w c : Int => w * c) weights xs).foldl (fun s t => s + t) 0 =
        ((xs.foldl (fun (g : Nat) (x : Int) => Nat.gcd g x.natAbs) acc : Nat) : Int) := by
  induction xs generalizing acc with
  | nil =>
      exact ⟨1, [], by simp⟩
  | cons x xs ih =>
      rcases nat_gcd_bezout acc x.natAbs with ⟨u, v, huv⟩
      rcases int_natAbs_signed_mul x with ⟨sgn, hsgn⟩
      rcases ih (Nat.gcd acc x.natAbs) with ⟨a, weights, hlen, hsum⟩
      refine ⟨a * u, (a * v * sgn) :: weights, ?_, ?_⟩
      · simp [hlen]
      · simp only [List.zipWith_cons_cons, List.foldl_cons, List.foldl_cons]
        rw [← hsum, ← huv, list_foldl_add_int]
        have hterm : a * v * sgn * x = a * v * Int.ofNat x.natAbs := by
          rw [← hsgn]
          grind
        rw [hterm]
        grind

/-- `list_natAbs_gcd_bezout`: the `acc = 0` specialisation of
`list_natAbs_gcd_bezout_aux`, giving integer weights whose weighted `zipWith`
fold-sum of a coefficient list equals that list's natAbs-gcd. -/
private theorem list_natAbs_gcd_bezout (xs : List Int) :
    ∃ weights : List Int,
      weights.length = xs.length ∧
      (List.zipWith (fun w c : Int => w * c) weights xs).foldl (fun s t => s + t) 0 =
        ((xs.foldl (fun (g : Nat) (x : Int) => Nat.gcd g x.natAbs) 0 : Nat) : Int) := by
  rcases list_natAbs_gcd_bezout_aux xs 0 with ⟨_a, weights, hlen, hsum⟩
  refine ⟨weights, hlen, ?_⟩
  simpa using hsum

/-- `exists_linear_combination_coeffs_eq_one_of_content_eq_one`: from
`content p = 1`, produces integer weights whose weighted `zipWith` fold-sum
against `p`'s coefficients equals `1`. -/
private theorem exists_linear_combination_coeffs_eq_one_of_content_eq_one
    (p : DensePoly Int) (hp : content p = 1) :
    ∃ weights : List Int,
      weights.length = p.toArray.toList.length ∧
      (List.zipWith (fun w c : Int => w * c) weights p.toArray.toList).foldl
          (fun s t => s + t) 0 = 1 := by
  rcases list_natAbs_gcd_bezout p.toArray.toList with ⟨weights, hlen, hsum⟩
  refine ⟨weights, hlen, ?_⟩
  unfold content contentNat at hp
  rw [hsum]
  exact hp

/-- If a natural number divides every integer coefficient, its integer cast
divides the polynomial content. -/
theorem dvd_content_of_nat_dvd_coeff (p : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ p.coeff n) :
    (d : Int) ∣ content p := by
  rw [content, Int.ofNat_dvd_left]
  exact dvd_contentNat_of_dvd_coeff p d h

/-- If a natural number divides every coefficient, then it divides the content. -/
theorem natCast_dvd_content_of_dvd_coeff (p : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ p.coeff n) :
    (d : Int) ∣ content p := by
  exact dvd_content_of_nat_dvd_coeff p d h

/-- A natural number that divides every coefficient of a primitive integer
polynomial must be `1`. -/
theorem nat_eq_one_of_content_eq_one_of_nat_dvd_coeff (p : DensePoly Int) (d : Nat)
    (hp : content p = 1) (h : ∀ n, (d : Int) ∣ p.coeff n) :
    d = 1 := by
  have hdvd : (d : Int) ∣ (1 : Int) := by
    simpa [hp] using dvd_content_of_nat_dvd_coeff p d h
  rw [Int.ofNat_dvd_left] at hdvd
  exact Nat.dvd_one.mp hdvd

/-- `foldl_zipWith_mul_scale_int`: pulls a scalar `a` through a `zipWith (· * ·)`
fold-sum, rewriting `a *` the weighted sum as the weighted sum of the `a`-scaled
values. -/
private theorem foldl_zipWith_mul_scale_int
    (a : Int) (weights values : List Int) :
    a * (List.zipWith (fun w c : Int => w * c) weights values).foldl
          (fun s t => s + t) 0 =
      (List.zipWith (fun w c : Int => w * (a * c)) weights values).foldl
          (fun s t => s + t) 0 := by
  induction weights generalizing values with
  | nil => simp
  | cons w ws ih =>
      cases values with
      | nil => simp
      | cons c cs =>
          simp only [List.zipWith_cons_cons, List.foldl_cons]
          rw [list_foldl_add_int (List.zipWith (fun w c : Int => w * c) ws cs)
                (0 + w * c)]
          rw [list_foldl_add_int (List.zipWith (fun w c : Int => w * (a * c)) ws cs)
                (0 + w * (a * c))]
          rw [← ih cs]
          grind

/-- `dvd_foldl_zipWith_scale_mul`: a divisor `d` of every product `a * c` also
divides the `zipWith` fold-sum of the weights against the `a`-scaled values. -/
private theorem dvd_foldl_zipWith_scale_mul
    (d : Int) (a : Int) (weights values : List Int)
    (h : ∀ c ∈ values, d ∣ a * c) :
    d ∣ (List.zipWith (fun w c : Int => w * (a * c)) weights values).foldl
          (fun s t => s + t) 0 := by
  induction weights generalizing values with
  | nil => simp
  | cons w ws ih =>
      cases values with
      | nil => simp
      | cons c cs =>
          simp only [List.zipWith_cons_cons, List.foldl_cons]
          rw [list_foldl_add_int]
          have hac : d ∣ a * c := h c List.mem_cons_self
          have hrest : ∀ c' ∈ cs, d ∣ a * c' :=
            fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc'))
          have hwac : d ∣ w * (a * c) := Int.dvd_mul_of_dvd_right hac
          have h0wac : d ∣ (0 + w * (a * c) : Int) := by simpa using hwac
          exact Int.dvd_add h0wac (ih cs hrest)

/-- Scalar annihilator for primitive integer polynomials: if `d` divides every
coefficient of `a * p` and `p` is primitive (content one), then `d` already
divides `a`. -/
theorem nat_dvd_of_scalar_mul_primitive_coeff_dvd
    (p : DensePoly Int) (d : Nat) (a : Int)
    (hp : content p = 1)
    (h : ∀ n, (d : Int) ∣ a * p.coeff n) :
    (d : Int) ∣ a := by
  rcases exists_linear_combination_coeffs_eq_one_of_content_eq_one p hp with
    ⟨weights, _hlen, hsum⟩
  have hval_dvd : ∀ c ∈ p.toArray.toList, (d : Int) ∣ a * c := by
    intro c hc
    rw [List.mem_iff_getElem] at hc
    rcases hc with ⟨i, hi, hget⟩
    have hcoeff_eq : p.coeff i = c := by
      have hgetArray : p.coeffs[i] = c := by
        simp only [toArray, Array.getElem_toList] at hget
        exact hget
      change p.coeffs.getD i (0 : Int) = c
      rw [← Array.getElem_eq_getD (0 : Int)]
      exact hgetArray
    rw [← hcoeff_eq]
    exact h i
  have hexp :
      a = (List.zipWith (fun w c : Int => w * (a * c)) weights p.toArray.toList).foldl
            (fun s t => s + t) 0 := by
    have key := foldl_zipWith_mul_scale_int a weights p.toArray.toList
    rw [hsum, Int.mul_one] at key
    exact key
  rw [hexp]
  exact dvd_foldl_zipWith_scale_mul (d : Int) a weights p.toArray.toList hval_dvd

/-- `exists_max_prop_below`: extracts the greatest index below `N` satisfying a
decidable predicate, given that some index below `N` satisfies it. -/
private theorem exists_max_prop_below
    (P : Nat → Prop) [DecidablePred P] :
    ∀ N, (∃ n, n < N ∧ P n) →
      ∃ k, k < N ∧ P k ∧ ∀ j, k < j → j < N → ¬ P j
  | 0, h => by
      rcases h with ⟨n, hn, _⟩
      omega
  | N + 1, h => by
      by_cases hN : P N
      · exact ⟨N, by omega, hN, by
          intro j hj hjN
          omega⟩
      · have hbelow : ∃ n, n < N ∧ P n := by
          rcases h with ⟨n, hn, hp⟩
          by_cases hnN : n = N
          · subst n
            exact False.elim (hN hp)
          · exact ⟨n, by omega, hp⟩
        rcases exists_max_prop_below P N hbelow with ⟨k, hkN, hkP, hmax⟩
        exact ⟨k, by omega, hkP, by
          intro j hkj hjNsucc
          by_cases hj : j = N
          · subst j
            exact hN
          · exact hmax j hkj (by omega)⟩

/-- `exists_last_not_natCast_dvd_coeff`: given some coefficient of `q` is not
divisible by `(d : Int)`, returns the last such index, with every later
coefficient divisible by `d`. -/
private theorem exists_last_not_natCast_dvd_coeff
    (q : DensePoly Int) (d : Nat)
    (hq : ∃ n, ¬ (d : Int) ∣ q.coeff n) :
    ∃ k, (¬ (d : Int) ∣ q.coeff k) ∧
      ∀ j, k < j → (d : Int) ∣ q.coeff j := by
  have hbelow : ∃ n, n < q.size ∧ ¬ (d : Int) ∣ q.coeff n := by
    rcases hq with ⟨n, hn⟩
    by_cases hsize : n < q.size
    · exact ⟨n, hsize, hn⟩
    · have hcoeff : q.coeff n = 0 := coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hsize)
      have hdvd : (d : Int) ∣ q.coeff n := by
        rw [hcoeff]
        exact ⟨0, by simp⟩
      exact False.elim (hn hdvd)
  rcases exists_max_prop_below (fun n => ¬ (d : Int) ∣ q.coeff n) q.size hbelow with
    ⟨k, _hkSize, hk, hmax⟩
  exact ⟨k, hk, by
    intro j hkj
    by_cases hjSize : j < q.size
    · exact Classical.byContradiction (fun hnot => hmax j hkj hjSize hnot)
    · have hcoeff : q.coeff j = 0 := coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hjSize)
      rw [hcoeff]
      exact ⟨0, by simp⟩⟩

/-- `list_getD_map_ediv_zero`: `getD` commutes with mapping integer division by
`c` over a coefficient list, using default `0`. -/
private theorem list_getD_map_ediv_zero (c : Int) (coeffs : List Int) (n : Nat) :
    (coeffs.map fun coeff => coeff / c).getD n (Zero.zero : Int) =
      coeffs.getD n (Zero.zero : Int) / c := by
  induction coeffs generalizing n with
  | nil =>
      exact (Int.zero_ediv c).symm
  | cons coeff coeffs ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa using ih n

/-- Scaling the primitive part by the content reconstructs the original
integer polynomial. -/
@[simp, grind =]
theorem content_mul_primitivePart (p : DensePoly Int) :
    scale (content p) (primitivePart p) = p := by
  apply ext_coeff
  intro n
  calc
    (scale (content p) (primitivePart p)).coeff n =
        content p * (primitivePart p).coeff n := by
          exact coeff_scale (content p) (primitivePart p) n (Int.mul_zero _)
    _ = p.coeff n := by
      by_cases hc : contentNat p = 0
      · have hdiv := contentNat_dvd_coeff p n
        rw [hc] at hdiv
        rcases hdiv with ⟨k, hk⟩
        have hpzero : p.coeff n = 0 := by
          simpa using hk
        simp [content, primitivePart, hc, hpzero]
      · have hpart :
            (primitivePart p).coeff n = p.coeff n / content p := by
          unfold primitivePart content
          rw [if_neg hc, coeff_ofCoeffs_list, list_getD_map_ediv_zero]
          unfold coeff toList toArray Array.getD
          by_cases hn : n < p.coeffs.size
          · simp [hn]
          · simp [hn]
        have hmul : content p * (p.coeff n / content p) = p.coeff n := by
          unfold content
          exact Int.mul_ediv_cancel' (contentNat_dvd_coeff p n)
        rw [hpart, hmul]

/-- Multiplying an integer polynomial by `-1` preserves its content. -/
@[simp, grind =]
theorem content_scale_neg_one (p : DensePoly Int) :
    content (scale (-1 : Int) p) = content p := by
  unfold content
  apply congrArg Int.ofNat
  apply Nat.dvd_antisymm
  · apply dvd_contentNat_of_dvd_coeff
    intro n
    have hcoeff := contentNat_dvd_coeff (scale (-1 : Int) p) n
    rw [coeff_scale (-1 : Int) p n (Int.mul_zero (-1 : Int))] at hcoeff
    rcases hcoeff with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have hneg : p.coeff n = -((-1 : Int) * p.coeff n) := by grind
    rw [hneg, hk]
    grind
  · apply dvd_contentNat_of_dvd_coeff
    intro n
    rw [coeff_scale (-1 : Int) p n (Int.mul_zero (-1 : Int))]
    have hcoeff := contentNat_dvd_coeff p n
    rcases hcoeff with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk]
    grind

/-- Scaling every coefficient by `c` pulls `c.natAbs` out of the
`Nat.gcd`-over-`natAbs` fold: folding the scaled list from `c.natAbs * acc`
yields `c.natAbs` times the fold of the unscaled list from `acc`. This is the
fold-level identity behind `content (scale c p) = |c| * content p`. -/
private theorem foldl_gcd_natAbs_mul_const_int (c : Int) (xs : List Int) (acc : Nat) :
    xs.foldl (fun g x => Nat.gcd g (c * x).natAbs) (c.natAbs * acc) =
      c.natAbs * xs.foldl (fun g x => Nat.gcd g x.natAbs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
      simp only [List.foldl_cons]
      rw [Int.natAbs_mul, Nat.gcd_mul_left]
      exact ih (Nat.gcd acc x.natAbs)

/-- A `Nat.gcd`-over-`natAbs` fold across an all-zero coefficient list returns
the accumulator unchanged, since `gcd g 0 = g` at every step. Used to discharge
the trailing-zeros branch when trimming empties the tail. -/
private theorem foldl_gcd_natAbs_of_all_zero (xs : List Int) (acc : Nat)
    (hzero : ∀ y ∈ xs, y = (0 : Int)) :
    xs.foldl (fun g x => Nat.gcd g x.natAbs) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
      have hx : x = 0 := hzero x List.mem_cons_self
      have hxs' : ∀ y ∈ xs', y = (0 : Int) :=
        fun y hy => hzero y (List.mem_cons_of_mem x hy)
      simp only [List.foldl_cons, hx, Int.natAbs_zero, Nat.gcd_zero_right]
      exact ih acc hxs'

/-- The defining `cons` unfolding of `trimTrailingZerosList` on `Int` lists:
the head is dropped only when the trimmed tail is empty and the head itself is
zero, otherwise it is kept in front of the trimmed tail. -/
private theorem trimTrailingZerosList_cons_int (x : Int) (xs : List Int) :
    trimTrailingZerosList (x :: xs) =
      if trimTrailingZerosList xs = [] ∧ x = (0 : Int) then ([] : List Int)
      else x :: trimTrailingZerosList xs := rfl

/-- If trimming trailing zeros empties a list entirely, then every entry of the
original list was zero. The converse direction needed to push the gcd fold
through `trimTrailingZerosList`. -/
private theorem all_zero_of_trimTrailingZerosList_nil (xs : List Int)
    (htrim : trimTrailingZerosList xs = []) :
    ∀ y ∈ xs, y = (0 : Int) := by
  induction xs with
  | nil => intro y hy; cases hy
  | cons x xs' ih =>
      rw [trimTrailingZerosList_cons_int] at htrim
      by_cases hinner : trimTrailingZerosList xs' = [] ∧ x = (0 : Int)
      · rw [if_pos hinner] at htrim
        intro y hy
        rcases List.mem_cons.mp hy with hyx | hyxs
        · rw [hyx]; exact hinner.2
        · exact ih hinner.1 y hyxs
      · rw [if_neg hinner] at htrim
        exact absurd htrim (List.cons_ne_nil _ _)

/-- Trimming trailing zeros before the `Nat.gcd`-over-`natAbs` fold gives the
same result as folding the untrimmed list, because the dropped trailing zeros
contribute nothing to the gcd. Lets `contentNat` ignore the trimming step. -/
private theorem foldl_gcd_natAbs_trim_eq (xs : List Int) (acc : Nat) :
    (trimTrailingZerosList xs).foldl (fun g x => Nat.gcd g x.natAbs) acc =
      xs.foldl (fun g x => Nat.gcd g x.natAbs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
      rw [trimTrailingZerosList_cons_int]
      by_cases hinner : trimTrailingZerosList xs' = [] ∧ x = (0 : Int)
      · rw [if_pos hinner]
        rw [List.foldl_nil, List.foldl_cons, hinner.2]
        simp only [Int.natAbs_zero, Nat.gcd_zero_right]
        have hzero : ∀ y ∈ xs', y = (0 : Int) :=
          all_zero_of_trimTrailingZerosList_nil xs' hinner.1
        exact (foldl_gcd_natAbs_of_all_zero xs' acc hzero).symm
      · rw [if_neg hinner]
        rw [List.foldl_cons, List.foldl_cons]
        exact ih (Nat.gcd acc x.natAbs)

/-- Content scales by the absolute value of the scaling integer. -/
@[simp, grind =]
theorem content_scale_int (c : Int) (p : DensePoly Int) :
    content (scale c p) = Int.ofNat c.natAbs * content p := by
  show Int.ofNat (contentNat (scale c p)) =
      Int.ofNat c.natAbs * Int.ofNat (contentNat p)
  show Int.ofNat (contentNat (scale c p)) =
      Int.ofNat (c.natAbs * contentNat p)
  apply congrArg Int.ofNat
  -- Goal: contentNat (scale c p) = c.natAbs * contentNat p.
  unfold contentNat
  have hscale_coeffs :
      (scale c p).toList =
        trimTrailingZerosList (p.toArray.toList.map (fun x => c * x)) := by
    unfold scale ofCoeffs toList toArray trimTrailingZeros
    simp
  rw [hscale_coeffs, foldl_gcd_natAbs_trim_eq, List.foldl_map]
  have h := foldl_gcd_natAbs_mul_const_int c p.toArray.toList 0
  rw [Nat.mul_zero] at h
  exact h

/-- Scaling the zero integer polynomial by `-1` is still zero. -/
theorem scale_neg_one_zero :
    scale (-1 : Int) (0 : DensePoly Int) = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_scale (-1 : Int) (0 : DensePoly Int) n (Int.mul_zero (-1 : Int))]
  simp

/-- The zero integer polynomial has content zero. -/
@[simp, grind =]
theorem content_zero :
    content (0 : DensePoly Int) = 0 := by
  rfl

/-- The content of a constant integer polynomial is the absolute value of the
constant. -/
@[simp, grind =]
theorem content_C (c : Int) :
    content (C c) = Int.ofNat c.natAbs := by
  unfold content contentNat toList toArray
  by_cases hc : c = 0
  · simp [hc]
  · rw [coeffs_C_of_ne_zero hc]
    simp

/-- If an integer polynomial has zero content, its primitive part is zero. -/
@[simp, grind =]
theorem primitivePart_eq_zero_of_content_eq_zero (p : DensePoly Int) (h : content p = 0) :
    primitivePart p = 0 := by
  have hc : contentNat p = 0 := by
    rw [← Int.natCast_eq_zero]
    simpa [content] using h
  simp [primitivePart, hc]

/-- A polynomial whose content is `1` equals its primitive part. -/
@[simp, grind =]
theorem primitivePart_eq_self_of_content_eq_one
    (p : DensePoly Int) (h : content p = 1) :
    primitivePart p = p := by
  have hscale : scale (content p) (primitivePart p) = p :=
    content_mul_primitivePart p
  apply ext_coeff
  intro n
  have hcoeff :
      (scale (content p) (primitivePart p)).coeff n = p.coeff n := by
    rw [hscale]
  rw [coeff_scale (content p) (primitivePart p) n (Int.mul_zero _)] at hcoeff
  rw [h] at hcoeff
  simpa using hcoeff

/-- The primitive part of a polynomial with nonzero content has content `1`. -/
theorem primitivePart_primitive (p : DensePoly Int) (h : content p ≠ 0) :
    content (primitivePart p) = 1 := by
  unfold content
  let c := contentNat p
  let q := primitivePart p
  let cp := contentNat q
  have hc : c ≠ 0 := by
    intro hc0
    apply h
    simpa [content, c] using congrArg Int.ofNat hc0
  have hscale : scale (content p) q = p := by
    simp [q]
  have hmul_dvd_coeff : ∀ n, ((c * cp : Nat) : Int) ∣ p.coeff n := by
    intro n
    have hcoeff := congrArg (fun r : DensePoly Int => r.coeff n) hscale
    change (scale (content p) q).coeff n = p.coeff n at hcoeff
    rw [coeff_scale (content p) q n (Int.mul_zero _)] at hcoeff
    have hcp : (cp : Int) ∣ q.coeff n := by
      simpa [cp, q] using contentNat_dvd_coeff q n
    rcases hcp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hcoeff, hk]
    simp [content, c, cp]
    grind
  have hmul_dvd_c : c * cp ∣ c := by
    simpa [c, cp] using dvd_contentNat_of_dvd_coeff p (c * cp) hmul_dvd_coeff
  rcases hmul_dvd_c with ⟨k, hk⟩
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  have hcp_one : cp = 1 := by
    have hcancel : cp * k = 1 := by
      have hk' : c * 1 = c * (cp * k) := by
        simpa [Nat.mul_assoc] using hk
      exact Nat.eq_of_mul_eq_mul_left hcpos hk'.symm
    exact Nat.eq_one_of_mul_eq_one_right hcancel
  change (cp : Int) = 1
  rw [hcp_one]
  rfl

end DensePoly
end Hex
