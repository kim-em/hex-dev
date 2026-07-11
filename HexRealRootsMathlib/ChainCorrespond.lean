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
  have hc0 : ((Hex.ZPoly.content p : Int) : ℝ) ≠ 0 := by
    exact_mod_cast HexPolyZMathlib.content_ne_zero p hp
  have hcontent : toPolyℝ p =
      Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ) * toPolyℝ (Hex.ZPoly.primitivePart p) := by
    show (toPolynomial p).map (Int.castRingHom ℝ) = _
    rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart p, Polynomial.map_mul,
      Polynomial.map_C]
    rfl
  rw [hcontent, Polynomial.roots_C_mul _ hc0]

/-! ### Structure of the executable chain: head and nonemptiness -/

/-- The chain-extension loop only appends: the accumulator is a prefix of the
result. This is the invariant behind reading the chain's head off `s₀`. -/
private theorem sturmChainAux_toList_prefix (fuel : ℕ) (prev cur : Hex.ZPoly)
    (acc : Array Hex.ZPoly) :
    ∃ tail, (Hex.ZPoly.sturmChainAux fuel prev cur acc).toList = acc.toList ++ tail := by
  induction fuel generalizing prev cur acc with
  | zero =>
      exact ⟨[], by rw [show Hex.ZPoly.sturmChainAux 0 prev cur acc = acc from rfl,
        List.append_nil]⟩
  | succ fuel ih =>
      have hunf : Hex.ZPoly.sturmChainAux (fuel + 1) prev cur acc =
          (if (Hex.ZPoly.spem prev cur).isZero then acc
           else Hex.ZPoly.sturmChainAux fuel cur
                  (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
                  (acc.push (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))))) := rfl
      by_cases h : (Hex.ZPoly.spem prev cur).isZero
      · exact ⟨[], by rw [hunf, if_pos h, List.append_nil]⟩
      · obtain ⟨tail, ht⟩ := ih cur (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)))
          (acc.push (-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur))))
        refine ⟨-(Hex.ZPoly.primitivePart (Hex.ZPoly.spem prev cur)) :: tail, ?_⟩
        rw [hunf, if_neg h, ht, Array.toList_push, List.append_assoc, List.cons_append,
          List.nil_append]

/-- For a positive-degree `p`, the executable Sturm chain begins with
`s₀ = primitivePart p` and `s₁ = primitivePart p'`, so its list is those two
elements followed by a (possibly empty) tail. -/
private theorem sturmChain_toList_eq (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    ∃ tail, (Hex.ZPoly.sturmChain p).toList =
      Hex.ZPoly.primitivePart p
        :: Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p) :: tail := by
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
  obtain ⟨tail, ht⟩ := sturmChainAux_toList_prefix p.size (Hex.ZPoly.primitivePart p)
    (Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p))
    #[Hex.ZPoly.primitivePart p, Hex.ZPoly.primitivePart (Hex.DensePoly.derivative p)]
  exact ⟨tail, by rw [hchain, ht]; rfl⟩

/-- **Head of the mapped chain.** For a positive-degree `p`, the real-cast Sturm
chain has head `toPolyℝ (primitivePart p)`, matching the `IsSturmChain.head`
field (stated at the primitive part, per the design note: the executable chain's
first element is `primitivePart p`, not `p`, since the content is stripped). -/
theorem sturmChain_map_head? (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    ((Hex.ZPoly.sturmChain p).toList.map toPolyℝ).head?
      = some (toPolyℝ (Hex.ZPoly.primitivePart p)) := by
  obtain ⟨tail, ht⟩ := sturmChain_toList_eq p hp
  rw [ht]; rfl

/-- **Nonemptiness of the mapped chain** for a positive-degree `p`. -/
theorem sturmChain_map_ne_nil (p : Hex.ZPoly) (hp : 1 ≤ (p.degree?).getD 0) :
    (Hex.ZPoly.sturmChain p).toList.map toPolyℝ ≠ [] := by
  obtain ⟨tail, ht⟩ := sturmChain_toList_eq p hp
  rw [ht]; simp

end

end HexRealRootsMathlib
