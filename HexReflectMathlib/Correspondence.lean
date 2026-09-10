/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflectMathlib.Carrier
public import HexMvPolyMathlib

public section

/-!
The `MvPolynomial` form of the conversion theorem.

For a sealed environment of size `n` over a Mathlib ring `R`, applying
`HexMvPolyMathlib.equiv` to the converted `Hex.MvPoly` and evaluating with
`MvPolynomial.eval₂` at the integer cast homomorphism and the atom valuation
gives the Grind denotation of the reflected source. The proof composes the
Mathlib-free soundness theorem with `HexMvPolyMathlib.eval₂MathlibHom_apply`;
it does not reify the source again.
-/

namespace HexReflectMathlib

open Hex Hex.Reflect
open Lean.Grind.CommRing (Expr)

universe u

variable {R : Type u} [CommRing R] {n : Nat}
  {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- The executable evaluation of a converted term list through the integer
cast homomorphism is the Grind denotation. -/
theorem eval₂_intCastRingHom_ofIntTerms (ctx : Lean.RArray R) {e : RingExpr}
    {ts : List (Mono n × Int)} (h : convertTerms? n none e = some ts) :
    MvPoly.eval₂ (Int.castRingHom R) (ctxValuation ctx n) (ofIntTerms (cmp := cmp) id ts) =
      e.denote ctx :=
  eval₂_convertTerms_ctx coeffLaws_intCastRingHom ctx h

/-- Conversion commutes with interpretation through Mathlib's multivariate
polynomials: evaluating the transported converted polynomial at the integer
cast and the atom valuation gives the denotation of the reflected source. -/
theorem eval₂_equiv_ofIntTerms (ctx : Lean.RArray R) {e : RingExpr}
    {ts : List (Mono n × Int)} (h : convertTerms? n none e = some ts) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ctxValuation ctx n)
        (HexMvPolyMathlib.equiv (ofIntTerms (cmp := cmp) id ts)) =
      e.denote ctx := by
  rw [HexMvPolyMathlib.equiv_apply, ← algebraMap_int_eq, ← MvPolynomial.aeval_def,
    ← HexMvPolyMathlib.aevalMathlib_apply, HexMvPolyMathlib.aevalMathlib_eq_eval₂,
    algebraMap_int_eq]
  exact eval₂_intCastRingHom_ofIntTerms ctx h

/-- The characteristic-aware arm through Mathlib's multivariate polynomials,
under Grind characteristic evidence. -/
theorem eval₂_equiv_ofIntTermsC {c : Nat} [Lean.Grind.IsCharP R c] (ctx : Lean.RArray R)
    {e : RingExpr} {ts : List (Mono n × Int)} (h : convertTerms? n (some c) e = some ts) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ctxValuation ctx n)
        (HexMvPolyMathlib.equiv (ofIntTerms (cmp := cmp) id ts)) =
      e.denote ctx := by
  rw [HexMvPolyMathlib.equiv_apply, ← algebraMap_int_eq, ← MvPolynomial.aeval_def,
    ← HexMvPolyMathlib.aevalMathlib_apply, HexMvPolyMathlib.aevalMathlib_eq_eval₂,
    algebraMap_int_eq]
  exact eval₂_convertTermsC_ctx coeffLaws_intCastRingHom ctx h

/-- The algebra form: with `ℤ` acting through `algebraMap`, the transported
converted polynomial evaluates by `MvPolynomial.aeval`. -/
theorem aeval_algEquiv_ofIntTerms (ctx : Lean.RArray R) {e : RingExpr}
    {ts : List (Mono n × Int)} (h : convertTerms? n none e = some ts) :
    MvPolynomial.aeval (R := Int) (ctxValuation ctx n)
        (HexMvPolyMathlib.algEquiv (n := n) (R := Int) (cmp := cmp)
          (ofIntTerms (cmp := cmp) id ts)) =
      e.denote ctx := by
  rw [HexMvPolyMathlib.algEquiv_apply, ← HexMvPolyMathlib.aevalMathlib_apply,
    HexMvPolyMathlib.aevalMathlib_eq_eval₂, algebraMap_int_eq]
  exact eval₂_intCastRingHom_ofIntTerms ctx h

end HexReflectMathlib
