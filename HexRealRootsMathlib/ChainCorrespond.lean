/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexPolyZ
public import HexPolyMathlib.Euclid
public import HexRealRootsMathlib.SturmTheorem
public import HexRealRootsMathlib.Separation
public import HexRealRoots.Var
-- `import all` on the executable modules so the non-`@[expose]` bodies of
-- `signVar`, `sturmVarAt`, `evalDyadic`, and `dyadicSign` unfold here, and on
-- `Separation` so `Dyadic.toReal` unfolds.
import all HexRealRootsMathlib.Separation
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

public section

/-!
# Correspondence between the executable Sturm machinery and the abstract theorem

This module connects the executable real-root machinery in `HexRealRoots`
(`Hex.ZPoly.sturmChain`, `Hex.sturmVarAt`, `Hex.sturmCount`, `Hex.rootCount`,
`Hex.ZPoly.SquareFreeRat`) to the abstract `Polynomial ℝ` development in
`HexRealRootsMathlib.SturmTheorem`.

The first load-bearing bridge is `squareFreeRat_iff`: the executable
`SquareFreeRat` test (a `size ≤ 1` inequality on the rational gcd of `p` and
`p'`) matches Mathlib's `Squarefree` of the rational cast `toPolyℚ p`, for
`p ≠ 0`. It reuses the field-generic gcd correspondence
`HexPolyMathlib.toPolynomial_gcd_associated` together with the standard
`Separable`/`Squarefree`/`IsCoprime`/gcd characterizations over the perfect
field `ℚ`.

The `p = 0` corner is genuinely excluded: `SquareFreeRat 0` holds (the gcd of
the two zero polynomials has size `0`), while `Squarefree (0 : ℚ[X])` is false.
Every downstream consumer supplies a nonzero (indeed positive-degree) input.
-/

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-- The rational cast of an executable integer polynomial. -/
abbrev toPolyℚ (p : Hex.ZPoly) : Polynomial ℚ :=
  (toPolynomial p).map (Int.castRingHom ℚ)

/-- A dense polynomial stores at most one coefficient exactly when its Mathlib
image is a constant. The `DensePoly` normalization invariant makes `size ≤ 1`
(zero, or a single nonzero coefficient) coincide with `natDegree = 0`. -/
theorem size_le_one_iff_natDegree_eq_zero {R : Type*} [Semiring R] [DecidableEq R]
    (g : Hex.DensePoly R) :
    g.size ≤ 1 ↔ (HexPolyMathlib.toPolynomial g).natDegree = 0 := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases h : g.size = 0
  · rw [(Hex.DensePoly.degree?_eq_none_iff g).mpr h]; simp [h]
  · rw [Hex.DensePoly.degree?_eq_some_of_pos_size g (Nat.pos_of_ne_zero h),
      Option.getD_some]
    omega

/-- `toRatPoly` corresponds to the rational cast under `toPolynomial`. -/
theorem toPolynomial_toRatPoly (f : Hex.ZPoly) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.toRatPoly f) = toPolyℚ f := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.ZPoly.coeff_toRatPoly, toPolyℚ,
    Polynomial.coeff_map, coeff_toPolynomial]
  simp

/-- The rational cast of a nonzero executable polynomial is nonzero. -/
theorem toPolyℚ_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) : toPolyℚ f ≠ 0 := by
  rw [toPolyℚ, Ne, Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℚ))]
  intro h
  exact hf (by have := congrArg ofPolynomial h; simpa using this)

/-- **Square-freeness bridge.** For a nonzero executable integer polynomial `f`,
the executable rational-gcd test `SquareFreeRat f` holds exactly when the
rational cast `toPolyℚ f` is square-free.

The executable test is `(gcd (toRatPoly f) (toRatPoly f)').size ≤ 1`. Under
`toPolynomial` this raw gcd is associated to Mathlib's normalized
`EuclideanDomain.gcd` of `toPolyℚ f` and its derivative
(`HexPolyMathlib.toPolynomial_gcd_associated`), so the size test becomes a
degree-zero test on that gcd. For nonzero `toPolyℚ f` the gcd is nonzero, so
degree zero means the gcd is a unit, i.e. `toPolyℚ f` is coprime to its
derivative, i.e. `Separable`, i.e. (over the perfect field `ℚ`) `Squarefree`. -/
theorem squareFreeRat_iff (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.SquareFreeRat f ↔ Squarefree (toPolyℚ f) := by
  unfold Hex.ZPoly.SquareFreeRat
  set a := Hex.ZPoly.toRatPoly f with ha
  set a' := Hex.DensePoly.derivative a with ha'
  have hPa : HexPolyMathlib.toPolynomial a = toPolyℚ f := toPolynomial_toRatPoly f
  have hPa' : HexPolyMathlib.toPolynomial a' = derivative (toPolyℚ f) := by
    rw [ha', HexPolyMathlib.toPolynomial_derivative, hPa]
  have hP0 : toPolyℚ f ≠ 0 := toPolyℚ_ne_zero hf
  rw [size_le_one_iff_natDegree_eq_zero]
  -- The raw dense gcd's image is degree-associated to Mathlib's normalized gcd.
  have hassoc := HexPolyMathlib.toPolynomial_gcd_associated a a'
  have hdeg : (HexPolyMathlib.toPolynomial (Hex.DensePoly.gcd a a')).natDegree
      = (EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f))).natDegree := by
    have h := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassoc)
    rw [hPa, hPa'] at h
    exact h
  rw [hdeg]
  set G := EuclideanDomain.gcd (toPolyℚ f) (derivative (toPolyℚ f)) with hG
  have hG0 : G ≠ 0 := by
    rw [hG, Ne, EuclideanDomain.gcd_eq_zero_iff]
    exact fun h => hP0 h.1
  have key : G.natDegree = 0 ↔ IsUnit G := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hG0]
    exact_mod_cast Iff.rfl
  rw [key, hG, EuclideanDomain.gcd_isUnit_iff, ← Polynomial.separable_def,
    PerfectField.separable_iff_squarefree]

/-! ### Sign-variation correspondence at a dyadic point -/

/-- `Dyadic.toReal` is additive. -/
theorem toReal_add (a b : Dyadic) :
    Dyadic.toReal (a + b) = Dyadic.toReal a + Dyadic.toReal b := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_add]; push_cast; ring

/-- `Dyadic.toReal` is multiplicative. -/
theorem toReal_mul (a b : Dyadic) :
    Dyadic.toReal (a * b) = Dyadic.toReal a * Dyadic.toReal b := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_mul]; push_cast; ring

/-- `Dyadic.toReal` sends `0` to `0`. -/
@[simp] theorem toReal_zero : Dyadic.toReal 0 = 0 := by
  unfold Dyadic.toReal; rw [Dyadic.toRat_zero]; norm_num

/-- The horner polynomial built from a real coefficient list, lowest degree
first. `hornerPoly (c :: cs) = C c + X * hornerPoly cs`. -/
private noncomputable def hornerPoly (cs : List ℝ) : Polynomial ℝ :=
  cs.foldr (fun c p => Polynomial.C c + Polynomial.X * p) 0

private theorem eval_hornerPoly (r : ℝ) : ∀ cs : List ℝ,
    (hornerPoly cs).eval r = cs.foldr (fun c acc => c + r * acc) 0
  | [] => by simp [hornerPoly]
  | c :: cs => by
      show (Polynomial.C c + Polynomial.X * hornerPoly cs).eval r = _
      rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
        eval_hornerPoly r cs]
      rfl

private theorem coeff_hornerPoly : ∀ (cs : List ℝ) (n : Nat),
    (hornerPoly cs).coeff n = cs.getD n 0
  | [], n => by simp [hornerPoly]
  | c :: cs, n => by
      show (Polynomial.C c + Polynomial.X * hornerPoly cs).coeff n = _
      cases n with
      | zero => simp
      | succ m =>
          rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (Nat.succ_ne_zero m),
            Polynomial.coeff_X_mul, coeff_hornerPoly cs m, zero_add, List.getD_cons_succ]

private theorem getD_map_intCast : ∀ (L : List Int) (n : Nat),
    (L.map (Int.cast : ℤ → ℝ)).getD n 0 = ((L.getD n 0 : Int) : ℝ)
  | [], n => by simp
  | a :: L, n => by
      cases n with
      | zero => simp
      | succ m => simpa using getD_map_intCast L m

/-- Pushing `Dyadic.toReal` through the `evalDyadic` Horner fold turns it into the
same fold over the real casts of the coefficients. -/
private theorem toReal_horner_foldr (x : Dyadic) : ∀ cs : List Int,
    Dyadic.toReal (cs.foldr (fun c acc => Dyadic.ofInt c + x * acc) 0)
      = (cs.map (Int.cast : ℤ → ℝ)).foldr (fun c acc => c + Dyadic.toReal x * acc) 0
  | [] => by simp
  | c :: cs => by
      show Dyadic.toReal (Dyadic.ofInt c + x * cs.foldr (fun c acc => Dyadic.ofInt c + x * acc) 0)
          = (c : ℝ) + Dyadic.toReal x *
              (cs.map (Int.cast : ℤ → ℝ)).foldr (fun c acc => c + Dyadic.toReal x * acc) 0
      rw [toReal_add, toReal_mul, HexRealRootsMathlib.toReal_ofInt, toReal_horner_foldr x cs]

/-- **Evaluation correspondence.** The exact dyadic Horner evaluation of an
integer polynomial, cast to `ℝ`, agrees with the Mathlib evaluation of its real
cast at the real value of the dyadic point. -/
theorem toReal_evalDyadic (q : Hex.ZPoly) (x : Dyadic) :
    Dyadic.toReal (q.evalDyadic x) = (toPolyℝ q).eval (Dyadic.toReal x) := by
  have hcoeffs : hornerPoly (q.toArray.toList.map (Int.cast : ℤ → ℝ)) = toPolyℝ q := by
    ext n
    rw [coeff_hornerPoly, getD_map_intCast, coeff_toPolyℝ]
    congr 1
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
    have h := Hex.DensePoly.toArray_getD q n
    rw [Array.getD_eq_getD_getElem?] at h
    exact h
  unfold Hex.ZPoly.evalDyadic
  rw [← Array.foldr_toList, toReal_horner_foldr, ← eval_hornerPoly, hcoeffs]

/-- **Sign correspondence.** The exact integer sign of a dyadic value has, as a
real number, the same `SignType.sign` as the real value of the dyadic. -/
theorem sign_dyadicSign (d : Dyadic) :
    SignType.sign ((Hex.dyadicSign d : ℝ)) = SignType.sign (Dyadic.toReal d) := by
  cases d with
  | zero => simp [Hex.dyadicSign]
  | ofOdd n k hn =>
      have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      have h2 : (0 : ℝ) < 2 ^ (-k) := by positivity
      have htr : Dyadic.toReal (Dyadic.ofOdd n k hn) = (n : ℝ) * 2 ^ (-k) := by
        unfold Dyadic.toReal
        rw [Dyadic.toRat_ofOdd_eq_mul_two_pow]; push_cast; ring
      rw [htr, Hex.dyadicSign]
      by_cases hlt : n < 0
      · rw [if_pos hlt]
        rw [show ((-1 : Int) : ℝ) = -1 by norm_num,
          sign_neg (mul_neg_of_neg_of_pos (by exact_mod_cast hlt) h2), sign_neg (by norm_num)]
      · have hpos : 0 < n := lt_of_le_of_ne (by omega) (Ne.symm hn0)
        rw [if_neg hlt]
        rw [show ((1 : Int) : ℝ) = 1 by norm_num,
          sign_pos (mul_pos (by exact_mod_cast hpos) h2), sign_pos (by norm_num)]

/-- Filtering the real casts by nonzero commutes with filtering the integers by
nonzero: casting to `ℝ` neither creates nor destroys zero entries. -/
private theorem filter_map_ne_zero (l : List Int) :
    (l.map (Int.cast : ℤ → ℝ)).filter (fun v => decide (v ≠ 0))
      = (l.filter (· != 0)).map (Int.cast : ℤ → ℝ) := by
  have hp : ((fun v => decide (v ≠ 0)) ∘ (Int.cast : ℤ → ℝ)) = (· != 0) := by
    funext i
    by_cases h : i = 0 <;> simp [Function.comp_apply, h]
  rw [List.filter_map, hp]

/-- Two nonzero leading entries: `signVar` peels one sign-change decision and
recurses. Phrased through the public `Hex.signVar` (the internal `go` recursor is
module-private), using that a nonzero head survives the zero-filter. -/
private theorem signVar_cons_cons {a b : Int} (rest : List Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    Hex.signVar (a :: b :: rest)
      = (if a * b < 0 then 1 else 0) + Hex.signVar (b :: rest) := by
  have fa : (a :: b :: rest).filter (· != 0) = a :: b :: rest.filter (· != 0) := by
    rw [List.filter_cons, if_pos (by simpa using ha), List.filter_cons, if_pos (by simpa using hb)]
  have fb : (b :: rest).filter (· != 0) = b :: rest.filter (· != 0) := by
    rw [List.filter_cons, if_pos (by simpa using hb)]
  unfold Hex.signVar
  rw [fa, fb]
  rfl

/-- On a zero-free integer list, the executable count matches the abstract real
count of the casts. Structural recursion peeling two elements; each retained
entry is nonzero, so the executable and real sign tests agree pairwise. -/
private theorem signVar_zeroFree : ∀ m : List Int, (∀ x ∈ m, x ≠ 0) →
    Hex.signVar m = Sturm.countSignChanges (m.map (Int.cast : ℤ → ℝ))
  | [], _ => rfl
  | [a], ha => by
      have ha0 : a ≠ 0 := ha a (by simp)
      unfold Hex.signVar
      rw [List.filter_cons, if_pos (by simpa using ha0), List.filter_nil]
      rfl
  | a :: b :: rest, hne => by
      have ha : a ≠ 0 := hne a (by simp)
      have hb : b ≠ 0 := hne b (by simp)
      have hbne : ∀ x ∈ b :: rest, x ≠ 0 := fun x hx => hne x (List.mem_cons_of_mem _ hx)
      rw [signVar_cons_cons rest ha hb, signVar_zeroFree (b :: rest) hbne,
        List.map_cons, List.map_cons, List.map_cons, Sturm.countSignChanges_cons_cons]
      congr 1
      have hcast : (a : ℝ) * (b : ℝ) = ((a * b : Int) : ℝ) := by push_cast; ring
      rw [hcast]
      by_cases h : a * b < 0
      · rw [if_pos h, if_pos (by exact_mod_cast h)]
      · rw [if_neg h, if_neg (by exact_mod_cast h)]

/-- `signVar` reads only the zero-filtered list, so it is unchanged by
pre-filtering out zeros. -/
private theorem signVar_filter (l : List Int) :
    Hex.signVar l = Hex.signVar (l.filter (· != 0)) := by
  unfold Hex.signVar
  rw [List.filter_filter]
  simp only [Bool.and_self]

/-- **Sign-variation count correspondence.** The executable integer
sign-variation count of a list equals the abstract real sign-variation count of
the list cast to `ℝ`. -/
theorem signVar_eq (l : List Int) :
    Hex.signVar l = Sturm.signVariations (l.map (Int.cast : ℤ → ℝ)) := by
  rw [Sturm.signVariations, filter_map_ne_zero, signVar_filter]
  exact signVar_zeroFree (l.filter (· != 0))
    (fun x hx => by simpa using (List.mem_filter.mp hx).2)

/-- **Sign-variation correspondence.** The executable Sturm sign-variation count
of a chain at a dyadic point equals the abstract `Sturm.sturmVar` of the mapped
real chain at the real value of the point. Positive scaling of chain elements is
irrelevant: `sturmVar` reads only signs, which the exact dyadic evaluation and
the Mathlib evaluation agree on. -/
theorem sturmVarAt_eq (chain : Array Hex.ZPoly) (x : Dyadic) :
    Hex.sturmVarAt chain x
      = Sturm.sturmVar (chain.toList.map toPolyℝ) (Dyadic.toReal x) := by
  rw [Hex.sturmVarAt, signVar_eq, Sturm.sturmVar]
  apply Sturm.signVariations_congr
  simp only [List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q _
  rw [Function.comp_apply, Function.comp_apply, sign_dyadicSign, toReal_evalDyadic]

end

end HexRealRootsMathlib
