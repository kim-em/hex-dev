/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.QuadraticNormRecover
public import HexBerlekampZassenhausMathlib.QuadraticNorm
public import HexBerlekampZassenhausMathlib.Multiquadratic

public section
set_option backward.proofsInPublic true

/-!
# The certificate proves irreducibility

Two developments meet here. `HexBerlekampZassenhausMathlib.QuadraticNorm`
identifies the executable {name}`Hex.iteratedNorm` with a sign-pattern product
written as a `List.prod` over a fold-built list of signed sums; the
multiquadratic tower theorem of `HexBerlekampZassenhausMathlib.Multiquadratic`
proves a sign-pattern product of independent square classes irreducible, but
writes it as a `Finset.prod` over `Fin n → Bool`. The two encodings are the same
polynomial -- `signPatternPoly_ofFn` -- and once that is said,
{name}`Hex.QuadraticNormCertificate.check` returning `true` gives `Irreducible`
outright.

The `Fin n → Bool` indexing is not decoration: it is what lets an automorphism
act on the product by a reindexing equivalence, which is the whole trivial-
stabilizer argument. The fold is not decoration either: it is what the iterated
norm literally computes, one level per radicand. So neither side can adopt the
other's encoding, and the bridge is a real lemma rather than a definitional
unfolding. It is proved by induction on the number of radicands, splitting the
last sign off with {name}`Fin.snocEquiv` on one side and the last fold step on
the other.

## Main results

* `signPatternPoly_ofFn`: the two encodings agree.
* `irreducible_of_check`: a successful check makes its input irreducible in
  `Polynomial ℤ`.
* `irreducible_of_quadraticNormCertified`: the same for the budget-gated
  production gate {name}`Hex.quadraticNormCertified`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial
open HexPolyZMathlib (toPolynomial)

/-! ## The two sign-pattern encodings agree -/

section Encoding

variable {K : Type*} [CommRing K]

/-- Appending one radicand is one more doubling of the signed sums. -/
private theorem signedSums_concat (rs : List K) (x : K) :
    signedSums (rs ++ [x]) = (signedSums rs).flatMap fun s => [s + x, s - x] := by
  simp [signedSums, List.foldl_append]

/-- One doubling step, read through an arbitrary `g`. -/
private theorem prod_map_flatMap_pair {M : Type*} [CommMonoid M] (g : K → M) (x : K)
    (l : List K) :
    ((l.flatMap fun s => [s + x, s - x]).map g).prod
      = (l.map fun s => g (s + x) * g (s - x)).prod := by
  induction l with
  | nil => simp
  | cons s l ih => simp [List.flatMap_cons, ih, mul_assoc]

/-- The fold-built signed sums enumerate the `2ⁿ` sign patterns.

Stated for an arbitrary `g` into an arbitrary commutative monoid, because the
induction step replaces `g` by `fun s => g (s + x) * g (s - x)`: the last
radicand is consumed by the *function*, not by the list. -/
theorem prod_map_signedSums {M : Type*} [CommMonoid M] :
    ∀ {n : ℕ} (r : Fin n → K) (g : K → M),
      ((signedSums (List.ofFn r)).map g).prod
        = ∏ ε : Fin n → Bool, g (∑ i, if ε i then r i else -r i) := by
  intro n
  induction n with
  | zero =>
      intro r g
      simp [signedSums]
  | succ n ih =>
      intro r g
      have hsplit :
          ∀ (ε' : Fin n → Bool) (b : Bool),
            (∑ i, if (Fin.snoc ε' b : Fin (n + 1) → Bool) i then r i else -r i)
              = (∑ i : Fin n, if ε' i then r i.castSucc else -r i.castSucc)
                + (if b then r (Fin.last n) else -r (Fin.last n)) := by
        intro ε' b
        rw [Fin.sum_univ_castSucc]
        simp
      rw [List.ofFn_succ', List.concat_eq_append, signedSums_concat,
        prod_map_flatMap_pair]
      rw [ih (fun i : Fin n => r i.castSucc)
        (fun s => g (s + r (Fin.last n)) * g (s - r (Fin.last n)))]
      rw [← Equiv.prod_comp (Fin.snocEquiv fun _ : Fin (n + 1) => Bool)
        (fun ε : Fin (n + 1) → Bool => g (∑ i, if ε i then r i else -r i))]
      rw [Fintype.prod_prod_type]
      simp only [Fin.snocEquiv_apply]
      rw [Fintype.prod_bool]
      simp only [hsplit]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun ε _ => by simp [sub_eq_add_neg]

/-- The two sign-pattern products are the same polynomial: the `List.prod` the
iterated norm computes and the `Finset.prod` the tower theorem is about. -/
theorem signPatternPoly_ofFn (c : ℤ) {n : ℕ} (r : Fin n → K) :
    signPatternPoly ((c : K)) (List.ofFn r) = Hex.SquareClass.signPoly c r := by
  rw [signPatternPoly, Hex.SquareClass.signPoly,
    prod_map_signedSums r (fun s => X - C ((c : K) + s))]
  exact Finset.prod_congr rfl fun ε _ => by rw [Hex.SquareClass.signSum]

end Encoding

/-! ## The certificate implies irreducibility -/

section Certificate

open Hex.SquareClass

/-- Complex square roots of the radicands, chosen once. -/
private theorem exists_roots (ds : List ℤ) :
    ∃ r : Fin ds.length → ℂ, ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ) := by
  have hchoice : ∀ i : Fin ds.length, ∃ z : ℂ, z ^ 2 = ((ds[i] : ℤ) : ℂ) := by
    intro i
    exact IsAlgClosed.exists_pow_nat_eq _ (n := 2) (by norm_num)
  exact ⟨fun i => (hchoice i).choose, fun i => (hchoice i).choose_spec⟩

/-- The chosen roots, listed, are square roots of the radicands in the order the
iterated norm takes them. -/
private theorem forall₂_ofFn {ds : List ℤ} {r : Fin ds.length → ℂ}
    (hr : ∀ i, r i ^ 2 = ((ds[i] : ℤ) : ℂ)) :
    List.Forall₂ (fun (d : ℤ) (z : ℂ) => z ^ 2 = (d : ℂ)) ds (List.ofFn r) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h₁ h₂
  simpa using hr ⟨i, h₁⟩

/--
**The certificate is sound.** A successful
{name}`Hex.QuadraticNormCertificate.check` makes its input irreducible in
`Polynomial ℤ`.

No hypothesis is needed on `f`: the check pins `f` to an associate of the
iterated norm, and the iterated norm is monic whatever `f` was.
-/
theorem irreducible_of_check {cert : Hex.QuadraticNormCertificate} {f : Hex.ZPoly}
    (h : cert.check f = true) : Irreducible (toPolynomial f) := by
  obtain ⟨r, hr⟩ := exists_roots cert.radicands.toList
  have hmap :
      (toPolynomial (Hex.iteratedNorm cert.translation cert.radicands)).map
          (algebraMap ℤ ℂ)
        = signPoly cert.translation r := by
    rw [map_iteratedNorm cert.translation cert.radicands (forall₂_ofFn hr),
      signPatternPoly_ofFn]
  have hcast : (algebraMap ℤ ℂ) = Int.castRingHom ℂ := by
    exact RingHom.ext_int _ _
  rw [hcast] at hmap
  have hmonic : (toPolynomial (Hex.iteratedNorm cert.translation cert.radicands)).Monic :=
    Polynomial.monic_of_injective (f := Int.castRingHom ℂ)
      (fun a b hab => by simpa using hab) (by rw [hmap]; exact signPoly_monic _ _)
  have hirr : Irreducible (toPolynomial (Hex.iteratedNorm cert.translation cert.radicands)) :=
    irreducible_int_of_map_eq_signPoly (independent_of_check h) hr cert.translation hmonic hmap
  exact (associated_toPolynomial_of_check h).symm.irreducible hirr

/--
**The production gate is sound.** Whenever the budget-gated certificate reports
`true`, its input is irreducible.
-/
theorem irreducible_of_quadraticNormCertified {core : Hex.ZPoly} {width : Nat}
    (h : Hex.quadraticNormCertified core width = true) :
    Irreducible (toPolynomial core) := by
  rw [Hex.quadraticNormCertified, Bool.and_eq_true] at h
  obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.1 h.2
  exact irreducible_of_check (Hex.QuadraticNormCertificate.check_of_certify? hcert)

end Certificate

end

end HexBerlekampZassenhausMathlib
