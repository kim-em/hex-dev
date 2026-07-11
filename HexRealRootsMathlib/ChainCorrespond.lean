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

/-! ### `spem` correspondence: the sign-managed pseudo-remainder over `ℝ`

The executable `spem f g` is a **positive integer multiple** of the field
remainder `f mod g`. We prove the underlying Euclidean-division relation over
`ℝ`: there is a positive real `c` and a quotient `Q` with
`C c * toPolyℝ f = Q * toPolyℝ g + toPolyℝ (spem f g)`, together with the
degree drop that makes `toPolyℝ (spem f g)` the genuine remainder. This is the
identity the chain-axiom proofs consume: at a zero `x` of `g`, the relation
collapses to `c * f(x) = (spem f g)(x)`, fixing the sign of the next chain
element against the previous one. -/

/-- `toPolynomial` turns the executable scalar multiply into `C`-multiplication. -/
theorem toPolynomial_scale {R : Type*} [CommRing R] [DecidableEq R]
    (c : R) (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.scale c p)
      = Polynomial.C c * HexPolyMathlib.toPolynomial p := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.DensePoly.coeff_scale c p n (mul_zero c),
    Polynomial.coeff_C_mul, HexPolyMathlib.coeff_toPolynomial]

/-- `toPolynomial` turns the executable `x^k` shift into `X^k`-multiplication. -/
theorem toPolynomial_shift {R : Type*} [CommRing R] [DecidableEq R]
    (k : Nat) (p : Hex.DensePoly R) :
    HexPolyMathlib.toPolynomial (Hex.DensePoly.shift k p)
      = Polynomial.X ^ k * HexPolyMathlib.toPolynomial p := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.DensePoly.coeff_shift, mul_comm,
    Polynomial.coeff_mul_X_pow']
  by_cases h : k ≤ n
  · rw [if_neg (by omega), if_pos h, HexPolyMathlib.coeff_toPolynomial]
  · rw [if_pos (by omega), if_neg h]; rfl

/-- The real cast of a scalar multiple. -/
theorem toPolyℝ_scale (c : Int) (p : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.scale c p) = Polynomial.C (c : ℝ) * toPolyℝ p := by
  ext n
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_scale c p n (mul_zero c),
    Polynomial.coeff_C_mul, coeff_toPolyℝ]
  push_cast; ring

/-- The real cast of an `x^k` shift. -/
theorem toPolyℝ_shift (k : Nat) (p : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.shift k p) = Polynomial.X ^ k * toPolyℝ p := by
  ext n
  rw [coeff_toPolyℝ, Hex.DensePoly.coeff_shift, mul_comm, Polynomial.coeff_mul_X_pow']
  by_cases h : k ≤ n
  · rw [if_neg (show ¬ n < k by omega), if_pos h, coeff_toPolyℝ]
  · rw [if_pos (show n < k by omega), if_neg h]; exact Int.cast_zero

/-- The real cast of a difference. -/
theorem toPolyℝ_sub (p q : Hex.ZPoly) :
    toPolyℝ (p - q) = toPolyℝ p - toPolyℝ q := by
  show (HexPolyMathlib.toPolynomial (p - q)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_sub, Polynomial.map_sub]

/-- The real cast preserves the leading coefficient. -/
theorem leadingCoeff_toPolyℝ (p : Hex.ZPoly) :
    (toPolyℝ p).leadingCoeff = (p.leadingCoeff : ℝ) := by
  rw [toPolyℝ, Polynomial.leadingCoeff_map_of_injective
    (RingHom.injective_int (Int.castRingHom ℝ)), HexPolyMathlib.leadingCoeff_toPolynomial]
  simp

/-- **The `spemStep` identity over `ℝ`.** One reduction step is `|lc g|` times
the remainder minus a scaled shift of `g`, so its cast splits as a `C`-multiple
of `toPolyℝ r` minus a `C`-multiple of `X^k · toPolyℝ g`. -/
private theorem toPolyℝ_spemStep (g r : Hex.ZPoly) :
    toPolyℝ (Hex.ZPoly.spemStep g r) =
      Polynomial.C ((if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff : Int) : ℝ)
          * toPolyℝ r
        - Polynomial.C ((if g.leadingCoeff < 0 then -r.leadingCoeff else r.leadingCoeff : Int) : ℝ)
          * (Polynomial.X ^ ((r.degree?).getD 0 - (g.degree?).getD 0) * toPolyℝ g) := by
  have hstep : Hex.ZPoly.spemStep g r =
      Hex.DensePoly.scale (if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff) r
        - Hex.DensePoly.scale (if g.leadingCoeff < 0 then -r.leadingCoeff else r.leadingCoeff)
            (Hex.DensePoly.shift ((r.degree?).getD 0 - (g.degree?).getD 0) g) := rfl
  rw [hstep, toPolyℝ_sub, toPolyℝ_scale, toPolyℝ_scale, toPolyℝ_shift]

/-- **The `spemAux` division relation over `ℝ`.** For a divisor `g` with nonzero
leading coefficient, the reduction loop produces a positive `C`-multiple of the
input `r` differing from a polynomial multiple of `g`: there is `c > 0` and a
quotient `Q` with `C c · toPolyℝ r = Q · toPolyℝ g + toPolyℝ (spemAux g fuel r)`.
Induction on the structural fuel; each `spemStep` peels one `|lc g|` factor. -/
private theorem spemAux_relate (g : Hex.ZPoly) (hg : g.leadingCoeff ≠ 0) :
    ∀ (fuel : ℕ) (r : Hex.ZPoly),
      ∃ (c : ℝ) (Q : Polynomial ℝ), 0 < c ∧
        Polynomial.C c * toPolyℝ r
          = Q * toPolyℝ g + toPolyℝ (Hex.ZPoly.spemAux g fuel r) := by
  have habs : (0:ℝ) <
      ((if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff : Int) : ℝ) := by
    have : (0:Int) < (if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff) := by
      split_ifs with h <;> omega
    exact_mod_cast this
  intro fuel
  induction fuel with
  | zero =>
      intro r
      exact ⟨1, 0, one_pos, by
        rw [show Hex.ZPoly.spemAux g 0 r = r from rfl]; simp⟩
  | succ fuel ih =>
      intro r
      have hunf : Hex.ZPoly.spemAux g (fuel + 1) r =
          (if r.isZero then r
           else if (r.degree?).getD 0 < (g.degree?).getD 0 then r
           else Hex.ZPoly.spemAux g fuel (Hex.ZPoly.spemStep g r)) := rfl
      by_cases h0 : r.isZero
      · exact ⟨1, 0, one_pos, by rw [hunf, if_pos h0]; simp⟩
      · by_cases h1 : (r.degree?).getD 0 < (g.degree?).getD 0
        · exact ⟨1, 0, one_pos, by rw [hunf, if_neg h0, if_pos h1]; simp⟩
        · obtain ⟨c', Q', hc', hrel'⟩ := ih (Hex.ZPoly.spemStep g r)
          refine ⟨c' * ((if g.leadingCoeff < 0 then -g.leadingCoeff
                    else g.leadingCoeff : Int) : ℝ),
              Polynomial.C c' * Polynomial.C ((if g.leadingCoeff < 0 then -r.leadingCoeff
                    else r.leadingCoeff : Int) : ℝ)
                * Polynomial.X ^ ((r.degree?).getD 0 - (g.degree?).getD 0) + Q',
              mul_pos hc' habs, ?_⟩
          rw [hunf, if_neg h0, if_neg h1, Polynomial.C_mul]
          have key : toPolyℝ (Hex.ZPoly.spemAux g fuel (Hex.ZPoly.spemStep g r))
              = Polynomial.C c' * toPolyℝ (Hex.ZPoly.spemStep g r) - Q' * toPolyℝ g := by
            rw [hrel']; ring
          rw [key, toPolyℝ_spemStep]
          ring

/-- **The `spem` correspondence.** For a nonconstant divisor `g` (positive
degree, hence nonzero leading coefficient), the executable sign-managed
pseudo-remainder `spem f g` is a positive real multiple of the field remainder
of `f` by `g`: there is `c > 0` and a quotient `Q` with
`C c · toPolyℝ f = Q · toPolyℝ g + toPolyℝ (spem f g)`. Evaluating at a zero `x`
of `g` collapses this to `c · f(x) = (spem f g)(x)`, the sign-transfer identity
the chain axioms consume. -/
theorem toPolyℝ_spem (f g : Hex.ZPoly) (hg : g.leadingCoeff ≠ 0)
    (hdeg : 1 ≤ (g.degree?).getD 0) :
    ∃ (c : ℝ) (Q : Polynomial ℝ), 0 < c ∧
      Polynomial.C c * toPolyℝ f = Q * toPolyℝ g + toPolyℝ (Hex.ZPoly.spem f g) := by
  obtain ⟨m, hm⟩ : ∃ m, g.degree? = some m := by
    cases h : g.degree? with
    | none => rw [h] at hdeg; simp at hdeg
    | some m => exact ⟨m, rfl⟩
  have hm1 : m ≠ 0 := by rw [hm] at hdeg; simp only [Option.getD_some] at hdeg; omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
  have hspem : Hex.ZPoly.spem f g = Hex.ZPoly.spemAux g f.size f := by
    unfold Hex.ZPoly.spem; rw [hm]; rfl
  rw [hspem]
  exact spemAux_relate g hg f.size f

/-! ### Cast and executable-layer helpers for the chain axioms -/

/-- The real cast of a negation. -/
theorem toPolyℝ_neg (p : Hex.ZPoly) : toPolyℝ (-p) = -(toPolyℝ p) := by
  show (HexPolyMathlib.toPolynomial (-p)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_neg, Polynomial.map_neg]

/-- The real cast of the zero polynomial. -/
@[simp] theorem toPolyℝ_zero : toPolyℝ 0 = 0 := by
  show (HexPolyMathlib.toPolynomial 0).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]

/-- The real cast is zero exactly when the executable polynomial is. -/
theorem toPolyℝ_eq_zero_iff {p : Hex.ZPoly} : toPolyℝ p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h2 : HexPolyMathlib.toPolynomial p = 0 :=
      (Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom ℝ))).mp h
    have := congrArg HexPolyMathlib.ofPolynomial h2
    simpa using this
  · rintro rfl; exact toPolyℝ_zero

/-- A polynomial whose stored size is zero is the zero polynomial. -/
private theorem eq_zero_of_size_eq_zero {p : Hex.ZPoly} (h : p.size = 0) : p = 0 := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_zero]
  exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)

/-- The Boolean zero test decides equality with the zero polynomial. -/
private theorem isZero_iff_eq_zero {p : Hex.ZPoly} : p.isZero = true ↔ p = 0 := by
  rw [Hex.DensePoly.isZero_eq_true_iff]
  exact ⟨fun h => eq_zero_of_size_eq_zero h, fun h => by subst h; rfl⟩

/-- A nonzero executable polynomial has a `some` degree, namely `size - 1`. -/
private theorem degree?_of_ne_zero {p : Hex.ZPoly} (hp : p ≠ 0) :
    p.degree? = some (p.size - 1) := by
  refine Hex.DensePoly.degree?_eq_some_of_pos_size p ?_
  rcases Nat.eq_zero_or_pos p.size with h | h
  · exact absurd (eq_zero_of_size_eq_zero h) hp
  · exact h

/-- The leading coefficient of a nonzero executable polynomial is nonzero. -/
private theorem leadingCoeff_ne_zero {p : Hex.ZPoly} (hp : p ≠ 0) :
    p.leadingCoeff ≠ 0 := by
  refine Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size p ?_
  rcases Nat.eq_zero_or_pos p.size with h | h
  · exact absurd (eq_zero_of_size_eq_zero h) hp
  · exact h

/-- The real value of the content of a nonzero polynomial is positive: the
executable content is a nonnegative integer, nonzero for nonzero input. -/
theorem content_real_pos {p : Hex.ZPoly} (hp : p ≠ 0) :
    (0 : ℝ) < ((Hex.ZPoly.content p : Int) : ℝ) := by
  have hne : Hex.ZPoly.content p ≠ 0 := HexPolyZMathlib.content_ne_zero p hp
  have hnonneg : (0 : Int) ≤ Hex.ZPoly.content p := Int.natCast_nonneg _
  exact_mod_cast lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Gauss decomposition of the real cast: a polynomial is its (positive integer)
content times its primitive part. -/
theorem toPolyℝ_eq_C_content_mul_primitivePart (p : Hex.ZPoly) :
    toPolyℝ p = Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ)
      * toPolyℝ (Hex.ZPoly.primitivePart p) := by
  show (toPolynomial p).map (Int.castRingHom ℝ) = _
  rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart p, Polynomial.map_mul,
    Polynomial.map_C]
  rfl

/-- The primitive part of a nonzero polynomial is nonzero. -/
theorem primitivePart_ne_zero {p : Hex.ZPoly} (hp : p ≠ 0) :
    Hex.ZPoly.primitivePart p ≠ 0 := by
  intro h
  apply hp
  rw [← toPolyℝ_eq_zero_iff, toPolyℝ_eq_C_content_mul_primitivePart p, h, toPolyℝ_zero,
    mul_zero]

/-- The real cast commutes with the derivative. -/
theorem toPolyℝ_derivative (p : Hex.ZPoly) :
    toPolyℝ (Hex.DensePoly.derivative p) = Polynomial.derivative (toPolyℝ p) := by
  show (HexPolyMathlib.toPolynomial (Hex.DensePoly.derivative p)).map (Int.castRingHom ℝ) = _
  rw [HexPolyMathlib.toPolynomial_derivative, Polynomial.derivative_map]

/-- `spem` by a nonzero constant is zero (the junk-value convention). -/
private theorem spem_of_degree_zero (f : Hex.ZPoly) {g : Hex.ZPoly} (hg : g ≠ 0)
    (hdeg : (g.degree?).getD 0 = 0) : Hex.ZPoly.spem f g = 0 := by
  have hsome := degree?_of_ne_zero hg
  have hz : g.size - 1 = 0 := by rw [hsome] at hdeg; simpa using hdeg
  have hg0 : g.degree? = some 0 := by rw [hsome, hz]
  unfold Hex.ZPoly.spem
  rw [hg0]
  rfl

/-! ### Degree control: the reduction loop terminates before its fuel runs out -/

/-- One `spemStep` strictly drops the degree (or reaches zero): the sign
management makes the two leading terms cancel exactly. Proved over `ℝ` via
`Polynomial.degree_sub_lt` and transferred back through `natDegree_toPolyℝ`. -/
private theorem spemStep_degree_lt {g r : Hex.ZPoly} (hg : g ≠ 0) (hr : r ≠ 0)
    (hge : (g.degree?).getD 0 ≤ (r.degree?).getD 0) :
    Hex.ZPoly.spemStep g r = 0 ∨
      ((Hex.ZPoly.spemStep g r).degree?).getD 0 < (r.degree?).getD 0 := by
  by_cases hz : Hex.ZPoly.spemStep g r = 0
  · exact Or.inl hz
  refine Or.inr ?_
  set a : Int := if g.leadingCoeff < 0 then -g.leadingCoeff else g.leadingCoeff with ha
  set b : Int := if g.leadingCoeff < 0 then -r.leadingCoeff else r.leadingCoeff with hb
  set k : ℕ := (r.degree?).getD 0 - (g.degree?).getD 0 with hk
  have hlcg : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hg
  have hlcr : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hr
  have ha0 : (a : ℝ) ≠ 0 := by
    have : a ≠ 0 := by rw [ha]; split_ifs with h <;> omega
    exact_mod_cast this
  have hb0 : (b : ℝ) ≠ 0 := by
    have : b ≠ 0 := by rw [hb]; split_ifs with h <;> omega
    exact_mod_cast this
  have hPr0 : toPolyℝ r ≠ 0 := fun h => hr (toPolyℝ_eq_zero_iff.mp h)
  have hPg0 : toPolyℝ g ≠ 0 := fun h => hg (toPolyℝ_eq_zero_iff.mp h)
  set A := Polynomial.C (a : ℝ) * toPolyℝ r with hA
  set B := Polynomial.C (b : ℝ) * (Polynomial.X ^ k * toPolyℝ g) with hB
  have hstep : toPolyℝ (Hex.ZPoly.spemStep g r) = A - B := toPolyℝ_spemStep g r
  have hdegA : A.degree = (toPolyℝ r).degree := by
    rw [hA, Polynomial.degree_mul, Polynomial.degree_C ha0, zero_add]
  have hdegB : B.degree = (toPolyℝ r).degree := by
    rw [hB, Polynomial.degree_mul, Polynomial.degree_C hb0, zero_add, Polynomial.degree_mul,
      Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hPg0,
      Polynomial.degree_eq_natDegree hPr0, natDegree_toPolyℝ, natDegree_toPolyℝ]
    have hkg : k + (g.degree?).getD 0 = (r.degree?).getD 0 := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) hkg
  have hlcA : A.leadingCoeff = (a : ℝ) * (r.leadingCoeff : ℝ) := by
    rw [hA, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, leadingCoeff_toPolyℝ]
  have hlcB : B.leadingCoeff = (b : ℝ) * (g.leadingCoeff : ℝ) := by
    rw [hB, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_pow, one_mul,
      leadingCoeff_toPolyℝ]
  have hlceq : A.leadingCoeff = B.leadingCoeff := by
    rw [hlcA, hlcB, ha, hb]
    split_ifs with h <;> (push_cast; ring)
  have hA0 : A ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha0) hPr0
  have hlt : (toPolyℝ (Hex.ZPoly.spemStep g r)).degree < (toPolyℝ r).degree := by
    rw [hstep, ← hdegA]
    exact Polynomial.degree_sub_lt (hdegA.trans hdegB.symm) hA0 hlceq
  have hstep0 : toPolyℝ (Hex.ZPoly.spemStep g r) ≠ 0 :=
    fun h => hz (toPolyℝ_eq_zero_iff.mp h)
  have hnat := Polynomial.natDegree_lt_natDegree hstep0 hlt
  rwa [natDegree_toPolyℝ, natDegree_toPolyℝ] at hnat

/-- `spemAux` with sufficient fuel lands strictly below the divisor's degree
(or at zero): the fuel bound `deg r < fuel + deg g` regenerates at each step
because the degree strictly drops. -/
private theorem spemAux_degree {g : Hex.ZPoly} (hg : g ≠ 0)
    (hg1 : 1 ≤ (g.degree?).getD 0) :
    ∀ (fuel : ℕ) (r : Hex.ZPoly), (r.degree?).getD 0 < fuel + (g.degree?).getD 0 →
      Hex.ZPoly.spemAux g fuel r = 0 ∨
        ((Hex.ZPoly.spemAux g fuel r).degree?).getD 0 < (g.degree?).getD 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro r hbound
      right
      rw [show Hex.ZPoly.spemAux g 0 r = r from rfl]
      omega
  | succ fuel ih =>
      intro r hbound
      have hunf : Hex.ZPoly.spemAux g (fuel + 1) r =
          (if r.isZero then r
           else if (r.degree?).getD 0 < (g.degree?).getD 0 then r
           else Hex.ZPoly.spemAux g fuel (Hex.ZPoly.spemStep g r)) := rfl
      by_cases h0 : r.isZero
      · left; rw [hunf, if_pos h0]; exact isZero_iff_eq_zero.mp h0
      · by_cases h1 : (r.degree?).getD 0 < (g.degree?).getD 0
        · right; rw [hunf, if_neg h0, if_pos h1]; exact h1
        · rw [hunf, if_neg h0, if_neg h1]
          have hr : r ≠ 0 := fun h => h0 (isZero_iff_eq_zero.mpr h)
          have hge : (g.degree?).getD 0 ≤ (r.degree?).getD 0 := not_lt.mp h1
          rcases spemStep_degree_lt hg hr hge with hz | hlt
          · apply ih
            rw [hz]
            simp only [Hex.DensePoly.degree?_zero_getD]
            omega
          · apply ih
            omega

/-- The top-level `spem` lands strictly below the divisor's degree (or at zero)
for a nonconstant divisor: the built-in fuel `f.size` always suffices. -/
private theorem spem_degree {f g : Hex.ZPoly} (hg : g ≠ 0)
    (hg1 : 1 ≤ (g.degree?).getD 0) :
    Hex.ZPoly.spem f g = 0 ∨
      ((Hex.ZPoly.spem f g).degree?).getD 0 < (g.degree?).getD 0 := by
  obtain ⟨m, hm⟩ : ∃ m, g.degree? = some m := ⟨g.size - 1, degree?_of_ne_zero hg⟩
  have hm1 : m ≠ 0 := by rw [hm] at hg1; simp only [Option.getD_some] at hg1; omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
  have hspem : Hex.ZPoly.spem f g = Hex.ZPoly.spemAux g f.size f := by
    unfold Hex.ZPoly.spem; rw [hm]; rfl
  rw [hspem]
  apply spemAux_degree hg hg1
  by_cases hf : f = 0
  · subst hf
    simp only [Hex.DensePoly.degree?_zero_getD]
    omega
  · rw [degree?_of_ne_zero hf]
    simp only [Option.getD_some]
    have hpos : 0 < f.size := by
      rcases Nat.eq_zero_or_pos f.size with h | h
      · exact absurd (eq_zero_of_size_eq_zero h) hf
      · exact h
    omega

/-! ### Squarefreeness and root transfers to `ℝ` -/

/-- **Squarefree-to-separable transfer.** If the rational cast `toPolyℚ p` is
squarefree, its real cast `toPolyℝ p` is separable. Over the perfect field `ℚ`,
squarefree means separable, and separability is preserved by the field
extension `ℚ → ℝ`. -/
theorem separable_toPolyℝ (p : Hex.ZPoly) (hsq : Squarefree (toPolyℚ p)) :
    (toPolyℝ p).Separable := by
  have hsep : (toPolyℚ p).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext_int _ _
  have hmap : toPolyℝ p = (toPolyℚ p).map (algebraMap ℚ ℝ) := by
    show (toPolynomial p).map (Int.castRingHom ℝ)
      = ((toPolynomial p).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)
    rw [Polynomial.map_map, hcomp]
  rw [hmap]; exact hsep.map

/-- The real cast of a nonzero `p` is the positive-content multiple of the cast
of its primitive part, so the two share exactly the same real roots. -/
theorem roots_toPolyℝ_eq_primitivePart (p : Hex.ZPoly) (hp : p ≠ 0) :
    (toPolyℝ p).roots = (toPolyℝ (Hex.ZPoly.primitivePart p)).roots := by
  rw [toPolyℝ_eq_C_content_mul_primitivePart p,
    Polynomial.roots_C_mul _ (ne_of_gt (content_real_pos hp))]

/-! ### Structure of the executable chain -/

/-- The tail the chain-extension loop appends past its two seeds: pure-list
mirror of `sturmChainAux` (which threads an `Array` accumulator). -/
private def chainList : ℕ → Hex.ZPoly → Hex.ZPoly → List Hex.ZPoly
  | 0, _, _ => []
  | fuel + 1, prev, cur =>
      if (Hex.ZPoly.spem prev cur).isZero then []
      else -(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))
        :: chainList fuel cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))

/-- The chain-extension loop only appends: its result is the accumulator
followed by the pure-list tail `chainList`. -/
private theorem sturmChainAux_toList (fuel : ℕ) (prev cur : Hex.ZPoly)
    (acc : Array Hex.ZPoly) :
    (Hex.ZPoly.sturmChainAux fuel prev cur acc).toList
      = acc.toList ++ chainList fuel prev cur := by
  induction fuel generalizing prev cur acc with
  | zero =>
      rw [show Hex.ZPoly.sturmChainAux 0 prev cur acc = acc from rfl, chainList,
        List.append_nil]
  | succ fuel ih =>
      have hunf : Hex.ZPoly.sturmChainAux (fuel + 1) prev cur acc =
          (if (Hex.ZPoly.spem prev cur).isZero then acc
           else Hex.ZPoly.sturmChainAux fuel cur
                  (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
                  (acc.push (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))))) := rfl
      rw [hunf, chainList]
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [if_pos h, if_pos h, List.append_nil]
      · rw [if_neg h, if_neg h, ih, Array.toList_push, List.append_assoc,
          List.cons_append, List.nil_append]

/-- For a positive-degree `p`, the executable Sturm chain is
`primitivePart p :: primitivePart p' :: chainList …`. -/
private theorem sturmChain_toList (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    (Hex.ZPoly.sturmChain p).toList =
      Hex.ZPoly.primitivePart p
        :: Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)
        :: chainList p.size (Hex.ZPoly.primitivePart p)
             (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)) := by
  obtain ⟨m, hm⟩ : ∃ m, p.degree? = some m := by
    cases h : p.degree? with
    | none => rw [h] at hp; simp at hp
    | some m => exact ⟨m, rfl⟩
  have hm1 : m ≠ 0 := by rw [hm] at hp; simp only [Option.getD_some] at hp; omega
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
  have hchain : Hex.ZPoly.sturmChain p =
      Hex.ZPoly.sturmChainAux p.size (Hex.ZPoly.primitivePart p)
        (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p))
        #[Hex.ZPoly.primitivePart p,
          Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)] := by
    unfold Hex.ZPoly.sturmChain; rw [hm]; rfl
  rw [hchain, sturmChainAux_toList]
  rfl

/-- **Head of the mapped chain.** For a positive-degree `p`, the real-cast Sturm
chain has head `toPolyℝ (primitivePart p)`, matching the `IsSturmChain.head`
field (stated at the primitive part, per the design note: the executable chain's
first element is `primitivePart p`, not `p`, since the content is stripped). -/
theorem sturmChain_map_head? (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    ((Hex.ZPoly.sturmChain p).toList.map toPolyℝ).head?
      = some (toPolyℝ (Hex.ZPoly.primitivePart p)) := by
  rw [sturmChain_toList p hp]; rfl

/-- **Nonemptiness of the mapped chain** for a positive-degree `p`. -/
theorem sturmChain_map_ne_nil (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    (Hex.ZPoly.sturmChain p).toList.map toPolyℝ ≠ [] := by
  rw [sturmChain_toList p hp]; simp

/-! ### The per-step chain relation -/

/-- **One chain step over `ℝ`.** When the loop pushes a new element past the
pair `(prev, cur)` (that is, `spem prev cur ≠ 0`), the three consecutive
elements satisfy `C c · prev = Q · cur − C k · next` with `c, k > 0`, where
`next = −primitivePart (spem prev cur)` is exactly the pushed element. At a
zero `x` of `cur` this collapses to `c · prev(x) = −k · next(x)`: the flanking
neighbours of a vanishing interior element have opposite signs. -/
private theorem chain_step {prev cur : Hex.ZPoly} (hcur : cur ≠ 0)
    (hr : Hex.ZPoly.spem prev cur ≠ 0) :
    ∃ (c k : ℝ) (Q : Polynomial ℝ), 0 < c ∧ 0 < k ∧
      Polynomial.C c * toPolyℝ prev
        = Q * toPolyℝ cur - Polynomial.C k
            * toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))) := by
  have hdeg1 : 1 ≤ (cur.degree?).getD 0 := by
    by_contra h
    exact hr (spem_of_degree_zero prev hcur (by omega))
  obtain ⟨c, Q, hc, hrel⟩ := toPolyℝ_spem prev cur (leadingCoeff_ne_zero hcur) hdeg1
  set r := Hex.ZPoly.spem prev cur with hrdef
  refine ⟨c, ((Hex.ZPoly.content r : Int) : ℝ), Q, hc, content_real_pos hr, ?_⟩
  rw [hrel, toPolyℝ_neg, toPolyℝ_eq_C_content_mul_primitivePart r]
  ring

/-- **Coprimality propagates down the chain.** The three-term relation
`C c · a = Q · b − C k · c'` transports `IsCoprime a b` to `IsCoprime b c'`:
any Bezout combination for `(a, b)` rewrites into one for `(b, c')`. -/
private theorem coprime_step {a b c' : Polynomial ℝ} {c₀ k : ℝ} {Q : Polynomial ℝ}
    (hc₀ : c₀ ≠ 0)
    (hrel : Polynomial.C c₀ * a = Q * b - Polynomial.C k * c')
    (h : IsCoprime a b) : IsCoprime b c' := by
  obtain ⟨u, v, huv⟩ := h
  have hCc : Polynomial.C c₀⁻¹ * Polynomial.C c₀ = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hc₀, Polynomial.C_1]
  refine ⟨u * Polynomial.C c₀⁻¹ * Q + v, -(u * Polynomial.C c₀⁻¹ * Polynomial.C k), ?_⟩
  calc (u * Polynomial.C c₀⁻¹ * Q + v) * b
        + -(u * Polynomial.C c₀⁻¹ * Polynomial.C k) * c'
      = u * Polynomial.C c₀⁻¹ * (Q * b - Polynomial.C k * c') + v * b := by ring
    _ = u * Polynomial.C c₀⁻¹ * (Polynomial.C c₀ * a) + v * b := by rw [← hrel]
    _ = u * ((Polynomial.C c₀⁻¹ * Polynomial.C c₀) * a) + v * b := by ring
    _ = u * a + v * b := by rw [hCc, one_mul]
    _ = 1 := huv

/-- The negated primitive part of a nonzero polynomial is nonzero. -/
private theorem neg_primitivePart_ne_zero {r : Hex.ZPoly} (hr : r ≠ 0) :
    -(Hex.ZPoly.primitivePart r) ≠ 0 := by
  intro hh
  have h2 : toPolyℝ (-(Hex.ZPoly.primitivePart r)) = 0 := by rw [hh, toPolyℝ_zero]
  rw [toPolyℝ_neg, neg_eq_zero, toPolyℝ_eq_zero_iff] at h2
  exact primitivePart_ne_zero hr h2

/-- A nonzero `spem prev cur` forces `cur` to be nonconstant (a constant
divisor returns the junk value `0`). -/
private theorem one_le_degree_of_spem_ne_zero {prev cur : Hex.ZPoly} (hcur : cur ≠ 0)
    (hr : Hex.ZPoly.spem prev cur ≠ 0) : 1 ≤ (cur.degree?).getD 0 := by
  by_contra hh
  exact hr (spem_of_degree_zero prev hcur (by omega))

/-! ### The chain-tail inductions: the four analytic `IsSturmChain` fields -/

/-- Every element of the extended chain is nonzero: the loop pushes only
negated primitive parts of nonzero pseudo-remainders. -/
private theorem chainList_nonzero :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), prev ≠ 0 → cur ≠ 0 →
      ∀ q ∈ prev :: cur :: chainList fuel prev cur, q ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev cur hprev hcur q hq
      rw [chainList] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hprev
      · exact hcur
  | succ fuel ih =>
      intro prev cur hprev hcur q hq
      rw [chainList] at hq
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [if_pos h] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hprev
        · exact hcur
      · rw [if_neg h] at hq
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hprev
        · exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))) hcur
            (neg_primitivePart_ne_zero hr) q hq'

/-- **The three-term chain relation, indexed.** Any three consecutive elements
`a, b, c` of the extended chain satisfy `C c₀ · a = Q · b − C k · c` over `ℝ`
with `c₀, k > 0`. -/
private theorem chainList_triples :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      ∀ (i : ℕ) (a b c : Hex.ZPoly),
        (prev :: cur :: chainList fuel prev cur)[i]? = some a →
        (prev :: cur :: chainList fuel prev cur)[i + 1]? = some b →
        (prev :: cur :: chainList fuel prev cur)[i + 2]? = some c →
        ∃ (c₀ k : ℝ) (Q : Polynomial ℝ), 0 < c₀ ∧ 0 < k ∧
          Polynomial.C c₀ * toPolyℝ a = Q * toPolyℝ b - Polynomial.C k * toPolyℝ c := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev cur _ i a b c _ _ hc
      rw [chainList, List.getElem?_cons_succ, List.getElem?_cons_succ] at hc
      simp at hc
  | succ fuel ih =>
      intro prev cur hcur i a b c ha hb hc
      rw [chainList] at ha hb hc
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [if_pos h, List.getElem?_cons_succ, List.getElem?_cons_succ] at hc
        simp at hc
      · rw [if_neg h] at ha hb hc
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        cases i with
        | zero =>
            obtain rfl : prev = a := by simpa using ha
            obtain rfl : cur = b := by simpa using hb
            obtain rfl : -(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)) = c := by
              simpa using hc
            exact chain_step hcur hr
        | succ j =>
            rw [List.getElem?_cons_succ] at ha hb hc
            exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
              (neg_primitivePart_ne_zero hr) j a b c ha hb hc

/-- **Pairwise coprimality along the chain.** If the two seeds are coprime
over `ℝ`, every pair of consecutive chain elements is: the three-term relation
transports Bezout witnesses down the chain. -/
private theorem chainList_pairs_coprime :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      IsCoprime (toPolyℝ prev) (toPolyℝ cur) →
      ∀ (i : ℕ) (a b : Hex.ZPoly),
        (prev :: cur :: chainList fuel prev cur)[i]? = some a →
        (prev :: cur :: chainList fuel prev cur)[i + 1]? = some b →
        IsCoprime (toPolyℝ a) (toPolyℝ b) := by
  intro fuel
  induction fuel with
  | zero =>
      intro prev cur _ hco i a b ha hb
      rw [chainList] at ha hb
      cases i with
      | zero =>
          obtain rfl : prev = a := by simpa using ha
          obtain rfl : cur = b := by simpa using hb
          exact hco
      | succ j =>
          rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at hb
          simp at hb
  | succ fuel ih =>
      intro prev cur hcur hco i a b ha hb
      rw [chainList] at ha hb
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [if_pos h] at ha hb
        cases i with
        | zero =>
            obtain rfl : prev = a := by simpa using ha
            obtain rfl : cur = b := by simpa using hb
            exact hco
        | succ j =>
            rw [List.getElem?_cons_succ, List.getElem?_cons_succ] at hb
            simp at hb
      · rw [if_neg h] at ha hb
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        obtain ⟨c₀, k, Q, hc₀, _, hrel⟩ := chain_step hcur hr
        have hco' : IsCoprime (toPolyℝ cur)
            (toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))) :=
          coprime_step (ne_of_gt hc₀) hrel hco
        cases i with
        | zero =>
            obtain rfl : prev = a := by simpa using ha
            obtain rfl : cur = b := by simpa using hb
            exact hco
        | succ j =>
            rw [List.getElem?_cons_succ] at ha hb
            exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
              (neg_primitivePart_ne_zero hr) hco' j a b ha hb

/-- **The terminal element is a unit.** With coprime seeds and sufficient fuel
(the degree of `cur` is below the remaining fuel, so the loop stops on a zero
pseudo-remainder, never by truncation), the last chain element is a unit of
`ℝ[X]`: at the stop, it divides its predecessor, and it is coprime to it. -/
private theorem chainList_last_unit :
    ∀ (fuel : ℕ) (prev cur : Hex.ZPoly), cur ≠ 0 →
      (cur.degree?).getD 0 < fuel →
      IsCoprime (toPolyℝ prev) (toPolyℝ cur) →
      ∀ z, (prev :: cur :: chainList fuel prev cur).getLast? = some z →
        IsUnit (toPolyℝ z) := by
  intro fuel
  induction fuel with
  | zero => intro prev cur _ hfuel _ z _; omega
  | succ fuel ih =>
      intro prev cur hcur hfuel hco z hz
      rw [chainList] at hz
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · rw [if_pos h, List.getLast?_cons_cons] at hz
        obtain rfl : cur = z := by simpa using hz
        have hr0 : Hex.ZPoly.spem prev cur = 0 := isZero_iff_eq_zero.mp h
        have hne : toPolyℝ cur ≠ 0 := fun hh => hcur (toPolyℝ_eq_zero_iff.mp hh)
        by_cases hdeg : (cur.degree?).getD 0 = 0
        · -- A nonzero constant is a unit of `ℝ[X]`.
          rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hne,
            natDegree_toPolyℝ, hdeg]
          rfl
        · -- Nonconstant: the terminal division relation plus coprimality.
          have hdeg1 : 1 ≤ (cur.degree?).getD 0 := by omega
          obtain ⟨c, Q, hc, hrel⟩ :=
            toPolyℝ_spem prev cur (leadingCoeff_ne_zero hcur) hdeg1
          rw [hr0, toPolyℝ_zero, add_zero] at hrel
          have hdvd : toPolyℝ cur ∣ toPolyℝ prev := by
            refine ⟨Polynomial.C c⁻¹ * Q, ?_⟩
            calc toPolyℝ prev
                = Polynomial.C c⁻¹ * (Polynomial.C c * toPolyℝ prev) := by
                  rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (ne_of_gt hc),
                    Polynomial.C_1, one_mul]
              _ = Polynomial.C c⁻¹ * (Q * toPolyℝ cur) := by rw [hrel]
              _ = toPolyℝ cur * (Polynomial.C c⁻¹ * Q) := by ring
          exact hco.isUnit_of_dvd' hdvd dvd_rfl
      · rw [if_neg h, List.getLast?_cons_cons] at hz
        have hr : Hex.ZPoly.spem prev cur ≠ 0 := fun hh => h (isZero_iff_eq_zero.mpr hh)
        obtain ⟨c₀, k, Q, hc₀, _, hrel⟩ := chain_step hcur hr
        have hco' : IsCoprime (toPolyℝ cur)
            (toPolyℝ (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))) :=
          coprime_step (ne_of_gt hc₀) hrel hco
        -- Degree bookkeeping: the pushed element's degree strictly drops.
        have hppdeg : ((Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)).degree?).getD 0
            = ((Hex.ZPoly.spem prev cur).degree?).getD 0 := by
          have h2 := congrArg Polynomial.natDegree
            (toPolyℝ_eq_C_content_mul_primitivePart (Hex.ZPoly.spem prev cur))
          rw [Polynomial.natDegree_C_mul (ne_of_gt (content_real_pos hr)),
            natDegree_toPolyℝ, natDegree_toPolyℝ] at h2
          omega
        have hnextdeg :
            (((-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))).degree?).getD 0)
              = ((Hex.ZPoly.spem prev cur).degree?).getD 0 := by
          rw [← natDegree_toPolyℝ, toPolyℝ_neg, Polynomial.natDegree_neg,
            natDegree_toPolyℝ, hppdeg]
        have hdeg1 : 1 ≤ (cur.degree?).getD 0 := one_le_degree_of_spem_ne_zero hcur hr
        have hdr : ((Hex.ZPoly.spem prev cur).degree?).getD 0 < (cur.degree?).getD 0 := by
          rcases spem_degree hcur hdeg1 with h0 | hlt
          · exact absurd h0 hr
          · exact hlt
        exact ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
          (neg_primitivePart_ne_zero hr) (by omega) hco' z hz

end

end HexRealRootsMathlib
