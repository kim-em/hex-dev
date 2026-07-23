/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Nat.Prime
public import HexBerlekampZassenhaus.IrreducibleCore

public section
set_option backward.proofsInPublic true

/-!
Eisenstein's criterion for `Hex.ZPoly`, plus the translation (Taylor shift)
`f(X) ↦ f(X + s)` needed to certify polynomials that only become Eisenstein
after a shift (e.g. `X⁴ + 1` at shift `1`, prime `2`).

The file provides three layers:

* `ZPoly.translate`, an executable, kernel-reducible Horner fold computing
  `f(X + s)`, with its ring-homomorphism laws (`translate_add`,
  `translate_mul`, `translate_C`) and the inverse identity
  `translate_neg_translate`. Irreducibility transfers backwards through the
  shift via `irreducible_of_translate_irreducible`.
* `ZPoly.irreducible_of_eisenstein`, the elementary coefficient-level
  Eisenstein criterion: a primitive non-constant `g` with a prime `q` not
  dividing the leading coefficient, dividing every lower coefficient, and
  with `q²` not dividing the constant term is irreducible.
* `ZPoly.irreducible_of_eisensteinCert`, the kernel-decidable slot form on
  the shifted polynomial `translate shift f`, consumed by the
  `IrredWitness.eisenstein` arm of `checkIrredWitness`. Primitivity is
  checked on the *shifted* polynomial directly, so no content-preservation
  lemma for `translate` is needed.
-/

namespace Hex
namespace ZPoly

/-! ## The Taylor shift `translate` -/

/-- Horner fold for the Taylor shift: `translateAux s cs` is
`Σᵢ cs[i]·(X + s)^i`. Structural recursion on the coefficient list keeps the
whole reduction closure exposed for the kernel checks in
`checkIrredWitness`. -/
@[expose]
def translateAux (s : Int) : List Int → ZPoly
  | [] => 0
  | c :: cs => translateAux s cs * (X + DensePoly.C s) + DensePoly.C c

/-- The Taylor shift `f(X) ↦ f(X + s)`. -/
@[expose]
def translate (s : Int) (f : ZPoly) : ZPoly :=
  translateAux s f.toArray.toList

private theorem translate_eq_aux (s : Int) (f : ZPoly) :
    translate s f = translateAux s f.toList := rfl

/-- The constant polynomial on `0` is the zero polynomial. -/
private theorem C_zero : DensePoly.C (0 : Int) = (0 : ZPoly) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_zero]
  by_cases hn : n = 0
  · rw [if_pos hn]
  · rw [if_neg hn]
    rfl

/-- `C` is additive on `ZPoly`. -/
private theorem C_add (a b : Int) :
    (DensePoly.C (a + b) : ZPoly) = DensePoly.C a + DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add _ _ n (by decide), DensePoly.coeff_C,
    DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn, if_neg hn]
    rfl

/-- `C` is multiplicative on `ZPoly`. -/
private theorem C_mul (a b : Int) :
    (DensePoly.C (a * b) : ZPoly) = DensePoly.C a * DensePoly.C b := by
  rw [C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) a (DensePoly.C b) n (Int.mul_zero a),
    DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    exact (Int.mul_zero a).symm

/-- A dense polynomial of size zero is the zero polynomial. -/
private theorem eq_zero_of_size_eq_zero {f : ZPoly} (h : f.size = 0) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_eq_zero_of_size_le f (by omega), DensePoly.coeff_zero]
  rfl

/-- The zero polynomial has the empty coefficient list. -/
private theorem toList_zero : (0 : ZPoly).toList = [] := by
  have hlen : (0 : ZPoly).toList.length = 0 := by
    rw [DensePoly.length_toList, DensePoly.size_zero]
  exact List.eq_nil_of_length_eq_zero hlen

@[simp] theorem translate_zero (s : Int) : translate s (0 : ZPoly) = 0 := by
  rw [translate_eq_aux, toList_zero]
  rfl

/-- A Horner fold over an everywhere-zero coefficient list is zero. -/
private theorem translateAux_eq_zero_of_all_zero (s : Int) :
    ∀ xs : List Int, (∀ n, xs.getD n 0 = 0) → translateAux s xs = 0 := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro h
      have hc : c = 0 := by simpa using h 0
      have hcs : ∀ n, cs.getD n 0 = 0 := fun n => by simpa using h (n + 1)
      simp only [translateAux]
      rw [ih hcs, DensePoly.zero_mul, hc, C_zero, DensePoly.add_zero_poly]

/-- `translateAux` only depends on the coefficient reads of the list, so two
lists agreeing under `getD` (in particular a list and its trailing-zero
trimming) produce the same shift. -/
private theorem translateAux_congr (s : Int) :
    ∀ xs ys : List Int, (∀ n, xs.getD n 0 = ys.getD n 0) →
      translateAux s xs = translateAux s ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have hys : ∀ n, ys.getD n 0 = 0 := fun n => by simpa using (h n).symm
      exact (translateAux_eq_zero_of_all_zero s ys hys).symm
  | cons c cs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hxs : ∀ n, (c :: cs).getD n 0 = 0 := fun n => by simpa using h n
          exact translateAux_eq_zero_of_all_zero s (c :: cs) hxs
      | cons b bs =>
          have hc : c = b := by simpa using h 0
          have hcs : ∀ n, cs.getD n 0 = bs.getD n 0 := fun n => by
            simpa using h (n + 1)
          simp only [translateAux]
          rw [ih bs hcs, hc]

/-! ## The `X`-quotient decomposition -/

/-- Drop the constant coefficient and shift down one degree; the structural
recursion handle for `ZPoly` inductions (`f = C f₀ + X · divX f`). -/
private noncomputable def divX (f : ZPoly) : ZPoly :=
  DensePoly.ofList (f.toList.drop 1)

private theorem coeff_divX (f : ZPoly) (n : Nat) :
    (divX f).coeff n = f.coeff (n + 1) := by
  unfold divX
  rw [DensePoly.coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, Nat.add_comm 1 n]
  exact DensePoly.toList_getD_eq_coeff f (n + 1)

private theorem size_divX (f : ZPoly) : (divX f).size = f.size - 1 := by
  have hle : (divX f).size ≤ f.size - 1 := by
    have h := DensePoly.size_ofList_le (f.toList.drop 1)
    have hlen : (f.toList.drop 1).length = f.size - 1 := by
      rw [List.length_drop, DensePoly.length_toList]
    unfold divX
    omega
  rcases Nat.lt_or_ge f.size 2 with hsmall | hbig
  · omega
  · have hne : (divX f).coeff (f.size - 2) ≠ 0 := by
      rw [coeff_divX]
      have harith : f.size - 2 + 1 = f.size - 1 := by omega
      rw [harith]
      exact DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
    have hgt : f.size - 2 < (divX f).size := by
      rcases Nat.lt_or_ge (f.size - 2) (divX f).size with h | h
      · exact h
      · exact absurd (DensePoly.coeff_eq_zero_of_size_le (divX f) h) hne
    omega

/-- The `X`-quotient decomposition `f = C f₀ + X · divX f`. -/
private theorem eq_C_add_X_mul_divX (f : ZPoly) :
    f = DensePoly.C (f.coeff 0) + X * divX f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add _ _ n (by decide)]
  show f.coeff n = _ + (DensePoly.monomial 1 1 * divX f).coeff n
  rw [DensePoly.monomial_one_mul_poly_eq_shift, DensePoly.coeff_shift,
    DensePoly.coeff_C]
  match n with
  | 0 =>
      rw [if_pos rfl, if_pos (by omega)]
      show f.coeff 0 = f.coeff 0 + 0
      omega
  | n + 1 =>
      rw [if_neg (by omega), if_neg (by omega), coeff_divX]
      have harith : n + 1 - 1 = n := by omega
      rw [harith]
      show f.coeff (n + 1) = 0 + f.coeff (n + 1)
      omega

/-- The Horner unfolding of `translate` through the `X`-quotient:
`translate s f = translate s (divX f) · (X + C s) + C f₀`. -/
private theorem translate_divX_unfold (s : Int) (f : ZPoly) :
    translate s f =
      translate s (divX f) * (X + DensePoly.C s) + DensePoly.C (f.coeff 0) := by
  rw [translate_eq_aux s f, translate_eq_aux s (divX f)]
  cases htl : f.toList with
  | nil =>
      have hsize : f.size = 0 := by
        have hlen := DensePoly.length_toList f
        rw [htl] at hlen
        simpa using hlen.symm
      have hcoeff : f.coeff 0 = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f (by omega)
      have hdivX : (divX f).toList = [] := by
        have hdsize : (divX f).size = 0 := by rw [size_divX]; omega
        have hlen : (divX f).toList.length = 0 := by
          rw [DensePoly.length_toList]; omega
        exact List.eq_nil_of_length_eq_zero hlen
      rw [hdivX, hcoeff, C_zero]
      show (0 : ZPoly) = 0 * (X + DensePoly.C s) + 0
      rw [DensePoly.zero_mul, DensePoly.add_zero_poly]
  | cons c cs =>
      have hc : c = f.coeff 0 := by
        have h := DensePoly.toList_getD_eq_coeff f 0
        rw [htl] at h
        simpa using h
      have hcs : translateAux s (divX f).toList = translateAux s cs := by
        apply translateAux_congr
        intro n
        have h1 := DensePoly.toList_getD_eq_coeff (divX f) n
        rw [coeff_divX] at h1
        have h2 := DensePoly.toList_getD_eq_coeff f (n + 1)
        rw [htl, List.getD_cons_succ] at h2
        exact h1.trans h2.symm
      rw [hcs]
      simp only [translateAux]
      rw [hc]

@[simp] theorem translate_C (s c : Int) :
    translate s (DensePoly.C c) = DensePoly.C c := by
  rw [translate_divX_unfold]
  have hdivX : divX (DensePoly.C c) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [coeff_divX, DensePoly.coeff_C, if_neg (by omega), DensePoly.coeff_zero]
    rfl
  have hcoeff : (DensePoly.C c : ZPoly).coeff 0 = c := by
    rw [DensePoly.coeff_C, if_pos rfl]
  rw [hdivX, translate_zero, DensePoly.zero_mul, hcoeff,
    DensePoly.add_comm_poly, DensePoly.add_zero_poly]

@[simp] theorem translate_one (s : Int) : translate s (1 : ZPoly) = 1 :=
  translate_C s 1

theorem translate_X (s : Int) : translate s X = X + DensePoly.C s := by
  rw [translate_divX_unfold]
  have hdivX : divX X = 1 := by
    apply DensePoly.ext_coeff
    intro n
    rw [coeff_divX]
    show (DensePoly.monomial 1 1 : ZPoly).coeff (n + 1) =
      (DensePoly.C 1 : ZPoly).coeff n
    rw [DensePoly.coeff_monomial, DensePoly.coeff_C]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg (by omega), if_neg hn]
  have hcoeff : (X : ZPoly).coeff 0 = 0 := by
    show (DensePoly.monomial 1 1 : ZPoly).coeff 0 = 0
    rw [DensePoly.coeff_monomial, if_neg (by omega)]
    rfl
  rw [hdivX, translate_one, hcoeff, C_zero, DensePoly.add_zero_poly,
    DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]

/-! ## `translate` is a ring homomorphism -/

private theorem divX_add (p q : ZPoly) : divX (p + q) = divX p + divX q := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add _ _ n (by decide), coeff_divX, coeff_divX, coeff_divX,
    DensePoly.coeff_add _ _ (n + 1) (by decide)]

private theorem translate_add_bounded (s : Int) :
    ∀ (n : Nat) (p q : ZPoly), p.size + q.size ≤ n →
      translate s (p + q) = translate s p + translate s q := by
  intro n
  induction n with
  | zero =>
      intro p q hbound
      have hp : p = 0 := eq_zero_of_size_eq_zero (by omega)
      have hq : q = 0 := eq_zero_of_size_eq_zero (by omega)
      subst hp; subst hq
      rw [DensePoly.add_zero_poly, translate_zero, DensePoly.add_zero_poly]
  | succ n ih =>
      intro p q hbound
      by_cases hp0 : p.size = 0
      · have hp : p = 0 := eq_zero_of_size_eq_zero hp0
        subst hp
        rw [DensePoly.add_comm_poly (0 : ZPoly) q, DensePoly.add_zero_poly,
          translate_zero, DensePoly.add_comm_poly (0 : ZPoly) (translate s q),
          DensePoly.add_zero_poly]
      by_cases hq0 : q.size = 0
      · have hq : q = 0 := eq_zero_of_size_eq_zero hq0
        subst hq
        rw [DensePoly.add_zero_poly, translate_zero, DensePoly.add_zero_poly]
      -- Both sizes positive: recurse through the `X`-quotient.
      have hcoeff0 : (p + q).coeff 0 = p.coeff 0 + q.coeff 0 :=
        DensePoly.coeff_add p q 0 (by decide)
      rw [translate_divX_unfold s (p + q), divX_add, hcoeff0,
        ih (divX p) (divX q) (by rw [size_divX, size_divX]; omega),
        translate_divX_unfold s p, translate_divX_unfold s q,
        DensePoly.mul_add_left_poly, C_add]
      -- (A + B) + (Ca + Cb) = (A + Ca) + (B + Cb)
      rw [DensePoly.add_assoc_poly
          (translate s (divX p) * (X + DensePoly.C s))
          (translate s (divX q) * (X + DensePoly.C s)) _,
        ← DensePoly.add_assoc_poly
          (translate s (divX q) * (X + DensePoly.C s))
          (DensePoly.C (p.coeff 0)) (DensePoly.C (q.coeff 0)),
        DensePoly.add_comm_poly
          (translate s (divX q) * (X + DensePoly.C s))
          (DensePoly.C (p.coeff 0)),
        DensePoly.add_assoc_poly (DensePoly.C (p.coeff 0))
          (translate s (divX q) * (X + DensePoly.C s))
          (DensePoly.C (q.coeff 0)),
        ← DensePoly.add_assoc_poly
          (translate s (divX p) * (X + DensePoly.C s))
          (DensePoly.C (p.coeff 0)) _]

/-- `translate` is additive. -/
theorem translate_add (s : Int) (p q : ZPoly) :
    translate s (p + q) = translate s p + translate s q :=
  translate_add_bounded s (p.size + q.size) p q (Nat.le_refl _)

private theorem divX_C_mul (c : Int) (b : ZPoly) :
    divX (DensePoly.C c * b) = DensePoly.C c * divX b := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_divX, C_mul_eq_scale, C_mul_eq_scale,
    DensePoly.coeff_scale (R := Int) c b (n + 1) (Int.mul_zero c),
    DensePoly.coeff_scale (R := Int) c (divX b) n (Int.mul_zero c), coeff_divX]

private theorem coeff0_C_mul (c : Int) (b : ZPoly) :
    (DensePoly.C c * b).coeff 0 = c * b.coeff 0 := by
  rw [C_mul_eq_scale, DensePoly.coeff_scale (R := Int) c b 0 (Int.mul_zero c)]

private theorem translate_C_mul_bounded (s c : Int) :
    ∀ (n : Nat) (b : ZPoly), b.size ≤ n →
      translate s (DensePoly.C c * b) = DensePoly.C c * translate s b := by
  intro n
  induction n with
  | zero =>
      intro b hbound
      have hb : b = 0 := eq_zero_of_size_eq_zero (by omega)
      subst hb
      have hz : DensePoly.C c * (0 : ZPoly) = 0 := by
        rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
      rw [translate_zero, hz, translate_zero]
  | succ n ih =>
      intro b hbound
      by_cases hb0 : b.size = 0
      · have hb : b = 0 := eq_zero_of_size_eq_zero hb0
        subst hb
        have hz : DensePoly.C c * (0 : ZPoly) = 0 := by
          rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
        rw [translate_zero, hz, translate_zero]
      rw [translate_divX_unfold s (DensePoly.C c * b), divX_C_mul, coeff0_C_mul,
        ih (divX b) (by rw [size_divX]; omega), C_mul,
        DensePoly.mul_assoc_poly (S := Int) (DensePoly.C c) (translate s (divX b))
          (X + DensePoly.C s),
        ← DensePoly.mul_add_right_poly, ← translate_divX_unfold]

private theorem divX_X_mul (p : ZPoly) : divX (X * p) = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_divX]
  show (DensePoly.monomial 1 1 * p).coeff (n + 1) = p.coeff n
  rw [DensePoly.monomial_one_mul_poly_eq_shift, DensePoly.coeff_shift,
    if_neg (by omega)]
  have harith : n + 1 - 1 = n := by omega
  rw [harith]

private theorem coeff0_X_mul (p : ZPoly) : (X * p).coeff 0 = 0 := by
  show (DensePoly.monomial 1 1 * p).coeff 0 = 0
  rw [DensePoly.monomial_one_mul_poly_eq_shift, DensePoly.coeff_shift,
    if_pos (by omega)]
  rfl

private theorem translate_X_mul (s : Int) (p : ZPoly) :
    translate s (X * p) = (X + DensePoly.C s) * translate s p := by
  rw [translate_divX_unfold s (X * p), divX_X_mul, coeff0_X_mul, C_zero,
    DensePoly.add_zero_poly, DensePoly.mul_comm_poly]

private theorem translate_mul_bounded (s : Int) :
    ∀ (n : Nat) (a b : ZPoly), a.size ≤ n →
      translate s (a * b) = translate s a * translate s b := by
  intro n
  induction n with
  | zero =>
      intro a b hbound
      have ha : a = 0 := eq_zero_of_size_eq_zero (by omega)
      subst ha
      rw [DensePoly.zero_mul, translate_zero, DensePoly.zero_mul]
  | succ n ih =>
      intro a b hbound
      by_cases ha0 : a.size = 0
      · have ha : a = 0 := eq_zero_of_size_eq_zero ha0
        subst ha
        rw [DensePoly.zero_mul, translate_zero, DensePoly.zero_mul]
      -- Split `a * b` along the `X`-quotient decomposition of `a`.
      have h1 : a * b =
          DensePoly.C (a.coeff 0) * b + X * (divX a * b) := by
        have h0 : a * b = (DensePoly.C (a.coeff 0) + X * divX a) * b := by
          rw [← eq_C_add_X_mul_divX a]
        rw [h0, DensePoly.mul_add_left_poly,
          DensePoly.mul_assoc_poly (S := Int) X (divX a) b]
      rw [h1, translate_add,
        translate_C_mul_bounded s (a.coeff 0) b.size b (Nat.le_refl _),
        translate_X_mul,
        ih (divX a) b (by rw [size_divX]; omega)]
      -- Reassemble: C a₀ · Tb + u · (Ta' · Tb) = (Ta' · u + C a₀) · Tb.
      have hswap : (X + DensePoly.C s) * (translate s (divX a) * translate s b)
          = translate s (divX a) * (X + DensePoly.C s) * translate s b := by
        rw [DensePoly.mul_assoc_poly (S := Int) (translate s (divX a))
            (X + DensePoly.C s) (translate s b),
          DensePoly.mul_comm_poly (X + DensePoly.C s) (translate s b),
          ← DensePoly.mul_assoc_poly (S := Int) (translate s (divX a))
            (translate s b) (X + DensePoly.C s),
          DensePoly.mul_comm_poly (X + DensePoly.C s)
            (translate s (divX a) * translate s b)]
      rw [translate_divX_unfold s a,
        DensePoly.mul_add_left_poly (translate s (divX a) * (X + DensePoly.C s))
          (DensePoly.C (a.coeff 0)) (translate s b),
        DensePoly.add_comm_poly
          (translate s (divX a) * (X + DensePoly.C s) * translate s b)
          (DensePoly.C (a.coeff 0) * translate s b),
        hswap]

/-- `translate` is multiplicative. -/
theorem translate_mul (s : Int) (a b : ZPoly) :
    translate s (a * b) = translate s a * translate s b :=
  translate_mul_bounded s a.size a b (Nat.le_refl _)

/-! ## The inverse shift -/

private theorem translate_neg_translate_bounded (s : Int) :
    ∀ (n : Nat) (f : ZPoly), f.size ≤ n →
      translate (-s) (translate s f) = f := by
  intro n
  induction n with
  | zero =>
      intro f hbound
      have hf : f = 0 := eq_zero_of_size_eq_zero (by omega)
      subst hf
      rw [translate_zero, translate_zero]
  | succ n ih =>
      intro f hbound
      by_cases hf0 : f.size = 0
      · have hf : f = 0 := eq_zero_of_size_eq_zero hf0
        subst hf
        rw [translate_zero, translate_zero]
      have hshift : translate (-s) (X + DensePoly.C s) = X := by
        rw [translate_add, translate_X, translate_C,
          DensePoly.add_assoc_poly, ← C_add]
        have harith : -s + s = 0 := by omega
        rw [harith, C_zero, DensePoly.add_zero_poly]
      rw [translate_divX_unfold s f, translate_add, translate_mul, translate_C,
        hshift, ih (divX f) (by rw [size_divX]; omega),
        DensePoly.mul_comm_poly (divX f) X,
        DensePoly.add_comm_poly (X * divX f) (DensePoly.C (f.coeff 0)),
        ← eq_C_add_X_mul_divX f]

/-- Shifting by `s` then by `-s` is the identity: `f(X + s)(X - s) = f`. -/
theorem translate_neg_translate (s : Int) (f : ZPoly) :
    translate (-s) (translate s f) = f :=
  translate_neg_translate_bounded s f.size f (Nat.le_refl _)

/-! ## Size preservation and unit reflection -/

/-- Addition cannot escape a common size bound. -/
private theorem size_add_le_of_le {p q : ZPoly} {k : Nat}
    (hp : p.size ≤ k) (hq : q.size ≤ k) : (p + q).size ≤ k := by
  rcases Nat.eq_zero_or_pos (p + q).size with h0 | hpos
  · omega
  rcases Nat.lt_or_ge k (p + q).size with hgt | hle
  · exfalso
    have hlast := DensePoly.coeff_last_ne_zero_of_pos_size (p + q) hpos
    apply hlast
    rw [DensePoly.coeff_add p q _ (by decide),
      DensePoly.coeff_eq_zero_of_size_le p (by omega),
      DensePoly.coeff_eq_zero_of_size_le q (by omega)]
    decide
  · exact hle

/-- The shift target `X + C s` has size exactly `2`. -/
private theorem size_X_add_C (s : Int) : (X + DensePoly.C s : ZPoly).size = 2 := by
  have hle : (X + DensePoly.C s : ZPoly).size ≤ 2 := by
    apply size_add_le_of_le
    · show (DensePoly.monomial 1 1 : ZPoly).size ≤ 2
      rw [DensePoly.size_monomial_of_ne_zero (by decide)]
      omega
    · exact Nat.le_trans (DensePoly.size_C_le_one s) (by omega)
  have hcoeff : (X + DensePoly.C s : ZPoly).coeff 1 ≠ 0 := by
    rw [DensePoly.coeff_add _ _ 1 (by decide)]
    show (DensePoly.monomial 1 1 : ZPoly).coeff 1 + (DensePoly.C s).coeff 1 ≠ 0
    rw [DensePoly.coeff_monomial, if_pos rfl, DensePoly.coeff_C,
      if_neg (by omega)]
    decide
  have hgt : 1 < (X + DensePoly.C s : ZPoly).size := by
    rcases Nat.lt_or_ge 1 (X + DensePoly.C s : ZPoly).size with h | h
    · exact h
    · exact absurd (DensePoly.coeff_eq_zero_of_size_le _ h) hcoeff
  omega

private theorem size_translate_le_bounded (s : Int) :
    ∀ (n : Nat) (f : ZPoly), f.size ≤ n → (translate s f).size ≤ f.size := by
  intro n
  induction n with
  | zero =>
      intro f hbound
      have hf : f = 0 := eq_zero_of_size_eq_zero (by omega)
      subst hf
      rw [translate_zero]
      exact Nat.le_refl _
  | succ n ih =>
      intro f hbound
      by_cases hf0 : f.size = 0
      · have hf : f = 0 := eq_zero_of_size_eq_zero hf0
        subst hf
        rw [translate_zero]
        exact Nat.le_refl _
      rw [translate_divX_unfold s f]
      apply size_add_le_of_le
      · by_cases hzero : translate s (divX f) = 0
        · rw [hzero, DensePoly.zero_mul, DensePoly.size_zero]
          omega
        · have hsize := ZPoly.mul_size_eq_top_succ_of_nonzero
            (translate s (divX f)) (X + DensePoly.C s)
            (ZPoly.size_pos_of_ne_zero _ hzero) (by rw [size_X_add_C]; omega)
          have hbound' := ih (divX f) (by rw [size_divX]; omega)
          rw [size_X_add_C] at hsize
          rw [size_divX] at hbound'
          omega
      · exact Nat.le_trans (DensePoly.size_C_le_one (f.coeff 0)) (by omega)

/-- The Taylor shift preserves the dense size (hence the degree). -/
theorem size_translate (s : Int) (f : ZPoly) :
    (translate s f).size = f.size := by
  have hle : (translate s f).size ≤ f.size :=
    size_translate_le_bounded s f.size f (Nat.le_refl _)
  have hge : f.size ≤ (translate s f).size := by
    have h := size_translate_le_bounded (-s) (translate s f).size
      (translate s f) (Nat.le_refl _)
    rw [translate_neg_translate] at h
    exact h
  omega

/-- The Taylor shift preserves units (`C 1` and `C (-1)` are fixed points in
both directions). -/
theorem isUnit_translate_iff (s : Int) (f : ZPoly) :
    ZPoly.IsUnit (translate s f) ↔ ZPoly.IsUnit f := by
  constructor
  · rintro (h | h)
    · left
      have := congrArg (translate (-s)) h
      rw [translate_neg_translate, translate_C] at this
      exact this
    · right
      have := congrArg (translate (-s)) h
      rw [translate_neg_translate, translate_C] at this
      exact this
  · rintro (h | h)
    · left; rw [h, translate_C]
    · right; rw [h, translate_C]

/-- Irreducibility transfers backwards through the Taylor shift: any
factorization of `f` shifts to a factorization of `translate s f`, whose unit
factor reflects back through the inverse shift. -/
theorem irreducible_of_translate_irreducible (s : Int) (f : ZPoly)
    (h : ZPoly.Irreducible (translate s f)) : ZPoly.Irreducible f := by
  refine
    { not_zero := ?_
      not_unit := ?_
      no_factors := ?_ }
  · intro h0
    apply h.not_zero
    rw [h0, translate_zero]
  · intro hu
    exact h.not_unit ((isUnit_translate_iff s f).mpr hu)
  · intro a b hab
    have hshift : translate s f = translate s a * translate s b := by
      rw [hab, translate_mul]
    rcases h.no_factors _ _ hshift with ha | hb
    · exact Or.inl ((isUnit_translate_iff s a).mp ha)
    · exact Or.inr ((isUnit_translate_iff s b).mp hb)

/-! ## Eisenstein's criterion -/

private theorem int_dvd_add {d x y : Int} (hx : d ∣ x) (hy : d ∣ y) :
    d ∣ x + y := by
  rcases hx with ⟨u, hu⟩
  rcases hy with ⟨v, hv⟩
  exact ⟨u + v, by rw [hu, hv, Int.mul_add]⟩

private theorem int_dvd_mul_right {d x : Int} (h : d ∣ x) (y : Int) :
    d ∣ x * y := by
  rcases h with ⟨u, hu⟩
  exact ⟨u * y, by rw [hu, Int.mul_assoc]⟩

/-- Euclid's lemma over `Int` for the elementary prime predicate, routed
through `natAbs` and the `Nat`-level `Hex.Nat.Prime.dvd_mul`. -/
private theorem prime_int_dvd_mul {q : Nat} (hq : Hex.Nat.Prime q) {x y : Int}
    (h : (q : Int) ∣ x * y) : (q : Int) ∣ x ∨ (q : Int) ∣ y := by
  have hnat : q ∣ (x * y).natAbs := by
    have habs := Int.natAbs_dvd_natAbs.mpr h
    rwa [Int.natAbs_natCast] at habs
  rw [Int.natAbs_mul] at hnat
  rcases (Hex.Nat.Prime.dvd_mul hq).mp hnat with h1 | h1
  · left
    apply Int.natAbs_dvd_natAbs.mp
    rwa [Int.natAbs_natCast]
  · right
    apply Int.natAbs_dvd_natAbs.mp
    rwa [Int.natAbs_natCast]

/-- Among indices carrying a coefficient not divisible by `d`, there is a
first one. -/
private theorem exists_first_not_dvd (d : Int) (g : Nat → Int) :
    ∀ n, (∃ m, m ≤ n ∧ ¬ d ∣ g m) →
      ∃ k, k ≤ n ∧ ¬ d ∣ g k ∧ ∀ i, i < k → d ∣ g i := by
  intro n
  induction n with
  | zero =>
      rintro ⟨m, hm, hmd⟩
      have hm0 : m = 0 := by omega
      subst hm0
      exact ⟨0, Nat.le_refl 0, hmd, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
      rintro ⟨m, hm, hmd⟩
      by_cases hex : ∃ m', m' ≤ n ∧ ¬ d ∣ g m'
      · rcases ih hex with ⟨k, hk, hkd, hkmin⟩
        exact ⟨k, by omega, hkd, hkmin⟩
      · have hm_eq : m = n + 1 := by
          rcases Nat.lt_or_ge m (n + 1) with hlt | hge
          · exact absurd ⟨m, by omega, hmd⟩ hex
          · omega
        subst hm_eq
        refine ⟨n + 1, Nat.le_refl _, hmd, fun i hi => ?_⟩
        exact Classical.byContradiction fun hnd => hex ⟨i, by omega, hnd⟩

/-- A fold of integer terms that vanish beyond index `0` collapses to the
first term. -/
private theorem foldl_add_int_eq_first (g : Nat → Int) :
    ∀ m, 0 < m → (∀ i, 0 < i → g i = 0) →
      (List.range m).foldl (fun acc i => acc + g i) 0 = g 0 := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
      intro _ hz
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        simp
      · rw [ih hpos hz, hz m hpos]
        omega

/-- A fold of integer terms each divisible by `d` is divisible by `d`. -/
private theorem foldl_add_int_dvd (d : Int) (g : Nat → Int) :
    ∀ m, (∀ i, i < m → d ∣ g i) →
      d ∣ (List.range m).foldl (fun acc i => acc + g i) 0 := by
  intro m
  induction m with
  | zero =>
      intro _
      exact ⟨0, by rw [Int.mul_zero]; rfl⟩
  | succ m ih =>
      intro h
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact int_dvd_add (ih fun i hi => h i (by omega)) (h m (by omega))

/-- Congruence collapse of a diagonal fold: when every term except the one at
index `k` is divisible by `d`, the fold is congruent to that term mod `d`. -/
private theorem foldl_add_int_dvd_sub (d : Int) (g : Nat → Int) :
    ∀ m, ∀ k, k < m → (∀ i, i < m → i ≠ k → d ∣ g i) →
      d ∣ (List.range m).foldl (fun acc i => acc + g i) 0 - g k := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
      intro k hk hdvd
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hkm : k = m
      · subst hkm
        have hSm : d ∣ (List.range k).foldl (fun acc i => acc + g i) 0 :=
          foldl_add_int_dvd d g k fun i hi => hdvd i (by omega) (by omega)
        have harith :
            (List.range k).foldl (fun acc i => acc + g i) 0 + g k - g k =
              (List.range k).foldl (fun acc i => acc + g i) 0 := by omega
        rw [harith]
        exact hSm
      · have h1 := ih k (by omega) fun i hi hne => hdvd i (by omega) hne
        have h2 : d ∣ g m := hdvd m (by omega) fun he => hkm he.symm
        rcases h1 with ⟨u, hu⟩
        rcases h2 with ⟨v, hv⟩
        refine ⟨u + v, ?_⟩
        rw [Int.mul_add, ← hu, ← hv]
        omega

/-- The constant term of a product is the product of constant terms. -/
private theorem coeff_mul_zero_int (p q : ZPoly) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal]
  rcases Nat.eq_zero_or_pos p.size with h0 | hpos
  · rw [h0, DensePoly.coeff_eq_zero_of_size_le p (by omega)]
    show (0 : Int) = 0 * q.coeff 0
    rw [Int.zero_mul]
  · have hterm : ∀ i, 0 < i → DensePoly.diagonalMulCoeffTerm p q 0 i = 0 := by
      intro i hi
      unfold DensePoly.diagonalMulCoeffTerm
      rw [if_pos hi]
    rw [foldl_add_int_eq_first _ p.size hpos hterm]
    unfold DensePoly.diagonalMulCoeffTerm
    rw [if_neg (by omega)]

/-- Below the leading coefficient, the product coefficient at the first
`d`-unbroken index of `p` is congruent to `p_k · q₀` mod `d`. -/
private theorem coeff_mul_congr_first (p q : ZPoly) (k : Nat) (d : Int)
    (hk : k < p.size) (hmin : ∀ i, i < k → d ∣ p.coeff i) :
    d ∣ (p * q).coeff k - p.coeff k * q.coeff 0 := by
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal]
  have hgk : DensePoly.diagonalMulCoeffTerm p q k k = p.coeff k * q.coeff 0 := by
    unfold DensePoly.diagonalMulCoeffTerm
    rw [if_neg (by omega), Nat.sub_self]
  rw [← hgk]
  apply foldl_add_int_dvd_sub d _ p.size k hk
  intro i hi hne
  unfold DensePoly.diagonalMulCoeffTerm
  by_cases hik : k < i
  · rw [if_pos hik]
    exact ⟨0, by rw [Int.mul_zero]⟩
  · rw [if_neg hik]
    exact int_dvd_mul_right (hmin i (by omega)) _

/-- A constant integer factor of a primitive polynomial is a unit: it divides
the content, which is `1`. -/
private theorem isUnit_C_of_const_factor_of_primitive
    (g h : ZPoly) (c : Int) (hg_eq : g = DensePoly.C c * h) (hc_ne : c ≠ 0)
    (hcontent_one : ZPoly.content g = 1) :
    ZPoly.IsUnit (DensePoly.C c) := by
  have hc_dvd_content : ((c.natAbs : Int) : Int) ∣ ZPoly.content g := by
    apply ZPoly.dvd_content_of_nat_dvd_coeff
    intro n
    have hcoeff : g.coeff n = c * h.coeff n := by
      rw [hg_eq, ZPoly.C_mul_eq_scale,
        DensePoly.coeff_scale (R := Int) c h n (Int.mul_zero _)]
    refine Int.natAbs_dvd.mpr ?_
    rw [hcoeff]
    exact ⟨h.coeff n, rfl⟩
  rw [hcontent_one] at hc_dvd_content
  have hnat_dvd : c.natAbs ∣ (1 : Nat) :=
    Int.ofNat_dvd.mp (show (c.natAbs : Int) ∣ ((1 : Nat) : Int) from hc_dvd_content)
  have hnat_le : c.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
  have hnat_pos : 1 ≤ c.natAbs := by
    rcases Nat.eq_zero_or_pos c.natAbs with hzero | hpos
    · exact absurd (Int.natAbs_eq_zero.mp hzero) hc_ne
    · exact hpos
  have hnat_eq : c.natAbs = 1 := by omega
  rcases Int.natAbs_eq c with heq | heq
  · left
    rw [heq, hnat_eq]
    rfl
  · right
    rw [heq, hnat_eq]
    rfl

/-- The one-sided Eisenstein contradiction: if `g = a·b` with `q ∤ b₀`, `b`
non-constant, and the Eisenstein coefficient conditions hold on `g`, we reach
`False` at the first index of `a` whose coefficient escapes `q` (that index
exists because `q` misses the leading coefficient, and it is positive because
`q ∣ g₀ = a₀·b₀` forces `q ∣ a₀`). -/
private theorem eisenstein_aux
    (g a b : ZPoly) (q : Nat) (hq : Hex.Nat.Prime q)
    (hg : g = a * b)
    (ha_pos : 0 < a.size) (hb2 : 2 ≤ b.size)
    (hlead : ¬ (q : Int) ∣ g.coeff (g.size - 1))
    (hlow : ∀ i, i < g.size - 1 → (q : Int) ∣ g.coeff i)
    (hb0 : ¬ (q : Int) ∣ b.coeff 0) :
    False := by
  have hb_pos : 0 < b.size := by omega
  have hsize : g.size = a.size + b.size - 1 := by
    rw [hg]
    exact ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
  -- The leading coefficient of `a` escapes `q`.
  have htop : g.coeff (g.size - 1) =
      a.coeff (a.size - 1) * b.coeff (b.size - 1) := by
    have h := DensePoly.coeff_mul_top_int a b ha_pos hb_pos
    have harith : g.size - 1 = a.size - 1 + (b.size - 1) := by omega
    rw [harith, hg]
    exact h
  have hlead_a : ¬ (q : Int) ∣ a.coeff (a.size - 1) := by
    intro h
    apply hlead
    rw [htop]
    exact int_dvd_mul_right h _
  -- Take the first index of `a` whose coefficient escapes `q`.
  rcases exists_first_not_dvd (q : Int) (fun i => a.coeff i) (a.size - 1)
      ⟨a.size - 1, Nat.le_refl _, hlead_a⟩ with ⟨k, hk_le, hk_not, hk_min⟩
  have hk_lt : k < g.size - 1 := by omega
  have hgk : (q : Int) ∣ g.coeff k := hlow k hk_lt
  have hcong : (q : Int) ∣ g.coeff k - a.coeff k * b.coeff 0 := by
    rw [hg]
    exact coeff_mul_congr_first a b k _ (by omega) hk_min
  have hprod : (q : Int) ∣ a.coeff k * b.coeff 0 := by
    rcases hgk with ⟨u, hu⟩
    rcases hcong with ⟨v, hv⟩
    refine ⟨u - v, ?_⟩
    rw [Int.mul_sub, ← hu, ← hv]
    omega
  rcases prime_int_dvd_mul hq hprod with h | h
  · exact hk_not h
  · exact hb0 h

/-- **Eisenstein's criterion** for integer polynomials, Mathlib-free: a
primitive non-constant `g` is irreducible when some prime `q` divides every
coefficient below the leading one, does not divide the leading coefficient,
and its square does not divide the constant term. -/
theorem irreducible_of_eisenstein
    (g : ZPoly) (q : Nat)
    (hq : Hex.Nat.Prime q)
    (hprim : ZPoly.Primitive g)
    (hsize : 1 < g.size)
    (hlead : ¬ (q : Int) ∣ g.coeff (g.size - 1))
    (hlow : ∀ i, i < g.size - 1 → (q : Int) ∣ g.coeff i)
    (hsq : ¬ ((q : Int) * (q : Int)) ∣ g.coeff 0) :
    ZPoly.Irreducible g := by
  have hg_ne : g ≠ 0 := by
    intro hzero
    rw [hzero] at hsize
    change 1 < (0 : Nat) at hsize
    omega
  refine
    { not_zero := hg_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hsize
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hsize
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hab
    have ha_ne : a ≠ 0 := by
      intro h
      apply hg_ne
      rw [hab, h, DensePoly.zero_mul]
    have hb_ne : b ≠ 0 := by
      intro h
      apply hg_ne
      rw [hab, h, DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_ne
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_ne
    -- Constant factors are units by primitivity.
    by_cases ha1 : a.size = 1
    · left
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha1
      have hac_ne : a.coeff 0 ≠ 0 := by
        intro h
        apply ha_ne
        rw [ha_eq, h]
        rfl
      have hg_eq : g = DensePoly.C (a.coeff 0) * b :=
        hab.trans (congrArg (· * b) ha_eq)
      have hunit := isUnit_C_of_const_factor_of_primitive g b (a.coeff 0)
        hg_eq hac_ne hprim
      rcases hunit with hone | hneg
      · left; rw [ha_eq]; exact hone
      · right; rw [ha_eq]; exact hneg
    by_cases hb1 : b.size = 1
    · right
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb1
      have hbc_ne : b.coeff 0 ≠ 0 := by
        intro h
        apply hb_ne
        rw [hb_eq, h]
        rfl
      have hg_eq : g = DensePoly.C (b.coeff 0) * a :=
        (hab.trans (DensePoly.mul_comm_poly a b)).trans
          (congrArg (· * a) hb_eq)
      have hunit := isUnit_C_of_const_factor_of_primitive g a (b.coeff 0)
        hg_eq hbc_ne hprim
      rcases hunit with hone | hneg
      · left; rw [hb_eq]; exact hone
      · right; rw [hb_eq]; exact hneg
    -- Both factors non-constant: derive the Eisenstein contradiction.
    exfalso
    have ha2 : 2 ≤ a.size := by omega
    have hb2 : 2 ≤ b.size := by omega
    have hg0 : (q : Int) ∣ g.coeff 0 := hlow 0 (by omega)
    have hg0ab : g.coeff 0 = a.coeff 0 * b.coeff 0 := by
      rw [hab]
      exact coeff_mul_zero_int a b
    rw [hg0ab] at hg0
    rcases prime_int_dvd_mul hq hg0 with ha0 | hb0
    · have hb0 : ¬ (q : Int) ∣ b.coeff 0 := by
        intro hb0
        apply hsq
        rw [hg0ab]
        rcases ha0 with ⟨u, hu⟩
        rcases hb0 with ⟨v, hv⟩
        refine ⟨u * v, ?_⟩
        rw [hu, hv]
        grind
      exact eisenstein_aux g a b q hq hab ha_pos hb2 hlead hlow hb0
    · have ha0 : ¬ (q : Int) ∣ a.coeff 0 := by
        intro ha0
        apply hsq
        rw [hg0ab]
        rcases ha0 with ⟨u, hu⟩
        rcases hb0 with ⟨v, hv⟩
        refine ⟨u * v, ?_⟩
        rw [hu, hv]
        grind
      exact eisenstein_aux g b a q hq (hab.trans (DensePoly.mul_comm_poly a b))
        hb_pos ha2 hlead hlow ha0

/-! ## The kernel-decidable certificate form -/

/-- Kernel-decidable Eisenstein-after-shift irreducibility: every hypothesis
is a Boolean check on the literal shifted polynomial `translate shift f`,
whose computation is itself part of the kernel check (the `translate`
reduction closure is exposed). Primitivity is checked on the shifted
polynomial, and the resulting irreducibility transfers back through
`irreducible_of_translate_irreducible`. Divisibility is checked through
`%` because the free layer carries no `Decidable ((q : Int) ∣ x)` instance. -/
theorem irreducible_of_eisensteinCert
    (f : ZPoly) (q : Nat) (shift : Int)
    (hp : Hex.Nat.isPrimeTrial q = true)
    (hcontent : decide (ZPoly.content (translate shift f) = 1) = true)
    (hsize : decide (1 < (translate shift f).size) = true)
    (hlead : decide ((translate shift f).coeff ((translate shift f).size - 1) %
      (q : Int) = 0) = false)
    (hlow : ((List.range ((translate shift f).size - 1)).all fun i =>
      decide ((translate shift f).coeff i % (q : Int) = 0)) = true)
    (hsq : decide ((translate shift f).coeff 0 %
      ((q : Int) * (q : Int)) = 0) = false) :
    ZPoly.Irreducible f := by
  have hq : Hex.Nat.Prime q := Hex.Nat.isPrimeTrial_isPrime hp
  apply irreducible_of_translate_irreducible shift
  apply irreducible_of_eisenstein _ q hq
  · exact of_decide_eq_true (p := ZPoly.content (translate shift f) = 1) hcontent
  · exact of_decide_eq_true hsize
  · intro hdvd
    have hmod := Int.emod_eq_zero_of_dvd hdvd
    rw [decide_eq_true hmod] at hlead
    exact Bool.noConfusion hlead
  · intro i hi
    have hmem := List.mem_range.mpr hi
    have hall := List.all_eq_true.mp hlow i hmem
    exact Int.dvd_of_emod_eq_zero (of_decide_eq_true hall)
  · intro hdvd
    have hmod := Int.emod_eq_zero_of_dvd hdvd
    rw [decide_eq_true hmod] at hsq
    exact Bool.noConfusion hsq

end ZPoly
end Hex
