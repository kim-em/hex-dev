/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Structural
public import HexPoly

@[expose] public section

/-!
The recursive univariate view of a multivariate polynomial.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']

/-- Remove coordinate `i` from an exponent vector. This is the explicit
Mathlib-free form of precomposition by `Fin.succAbove i`. -/
def removeVar (i : Fin (n + 1)) (m : Mono (n + 1)) : Mono n :=
  Hex.Vector.ofFn' fun j =>
    if j.val < i.val then
      m[(⟨j.val, by omega⟩ : Fin (n + 1))]
    else
      m[(⟨j.val + 1, by omega⟩ : Fin (n + 1))]

/-- Insert exponent `e` at coordinate `i`. -/
def insertVar (i : Fin (n + 1)) (e : Nat) (m : Mono n) : Mono (n + 1) :=
  Hex.Vector.ofFn' fun j =>
    if hsame : j.val = i.val then e
    else if hlt : j.val < i.val then
      m[(⟨j.val, by omega⟩ : Fin n)]
    else
      m[(⟨j.val - 1, by omega⟩ : Fin n)]

/-- Coefficients of `p` as a dense univariate polynomial in variable `i`.
Each coefficient is a polynomial in the remaining `n` variables. -/
def toUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] [IsMonomialOrder cmp']
    (p : MvPoly (n + 1) R cmp) : DensePoly (MvPoly n R cmp') :=
  let terms := p.termsList
  let size := terms.foldl
    (fun bound term => max bound (Mono.degreeOf i term.1 + 1)) 0
  DensePoly.ofCoeffs <| Id.run do
    let mut coeffs : Array (MvPoly n R cmp') := Array.replicate size 0
    for term in terms do
      let e := Mono.degreeOf i term.1
      let c := monomial (removeVar i term.1) term.2
      coeffs := coeffs.set! e (coeffs[e]! + c)
    return coeffs

/-- Inverse of `toUnivariate`, reinserting variable `i`. -/
def ofUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] [IsMonomialOrder cmp']
    (q : DensePoly (MvPoly n R cmp')) : MvPoly (n + 1) R cmp :=
  (List.range q.size).foldl
    (fun acc e =>
      (q.coeff e).foldTerms
        (fun acc m c => acc.addMonomial (insertVar i e m) c)
        acc)
    0

theorem toUnivariate_coeff [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [IsMonomialOrder cmp']
    (p : MvPoly (n + 1) R cmp) (e : Nat) (m : Mono n) :
    coeff m ((toUnivariate i cmp' p).coeff e) =
      coeff (insertVar i e m) p := by
  sorry

theorem ofUnivariate_coeff [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [IsMonomialOrder cmp']
    (q : DensePoly (MvPoly n R cmp')) (e : Nat) (m : Mono n) :
    coeff (insertVar i e m) (ofUnivariate (cmp := cmp) i cmp' q) =
      coeff m (q.coeff e) := by
  sorry

theorem ofUnivariate_toUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [IsMonomialOrder cmp']
    (p : MvPoly (n + 1) R cmp) :
    ofUnivariate (cmp := cmp) i cmp' (toUnivariate i cmp' p) = p := by
  sorry

theorem toUnivariate_ofUnivariate [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin (n + 1)) [IsMonomialOrder cmp']
    (q : DensePoly (MvPoly n R cmp')) :
    toUnivariate i cmp' (ofUnivariate (cmp := cmp) i cmp' q) = q := by
  sorry

end Hex.MvPoly
