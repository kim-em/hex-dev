/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Operations

@[expose] public section

/-!
Degree, variable, leading-term, and support-restriction queries for
`Hex.MvPoly`.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Maximum total degree of a supported monomial, or zero for the zero
polynomial. -/
def totalDegree [Zero R] (p : MvPoly n R cmp) : Nat :=
  p.foldTerms (fun d m _ => max d m.degree) 0

/-- Maximum exponent of variable `i`, or zero for the zero polynomial. -/
def degreeOf [Zero R] (i : Fin n) (p : MvPoly n R cmp) : Nat :=
  p.foldTerms (fun d m _ => max d (Mono.degreeOf i m)) 0

/-- Coordinatewise maximum of all supported exponent vectors. -/
def degrees [Zero R] (p : MvPoly n R cmp) : Mono n :=
  p.foldTerms (fun d m _ => Mono.lcm d m) Mono.zero

/-- Variables occurring in at least one supported monomial, in increasing
index order. -/
def vars [Zero R] (p : MvPoly n R cmp) : List (Fin n) :=
  Mono.support p.degrees

/-- Greatest supported term in the polynomial's monomial order. -/
def leadingTerm [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n × R) :=
  p.maxTerm?

/-- Greatest supported monomial in the polynomial's monomial order. -/
def leadingMono [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n) :=
  p.leadingTerm.map Prod.fst

/-- Compatibility spelling for `leadingMono`. -/
def leadingMonomial [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n) :=
  p.leadingMono

/-- Coefficient of the greatest supported monomial, or zero for the zero
polynomial. -/
def leadingCoeff [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : R :=
  match p.leadingTerm with
  | none => 0
  | some term => term.2

/-- Retain exactly the terms whose monomials satisfy `keep`. -/
def restrictBy [Zero R]
    (keep : Mono n → Bool) (p : MvPoly n R cmp) : MvPoly n R cmp where
  termsInternal := p.termsInternal.filter fun m _ => keep m
  nonzeroInternal := by
    intro m
    rw [Std.ExtTreeMap.getElem?_filter']
    cases hcoeff : p.termsInternal[m]? with
    | none => simp [Option.filter]
    | some c =>
      cases hkeep : keep m
      · simp [Option.filter]
      · have hc : c ≠ 0 := by
          intro hzero
          apply p.nonzeroInternal m
          rw [hcoeff, hzero]
        simpa [Option.filter] using hc

/-- Retain the terms whose exponent of `i` is at most `bound`. -/
def restrictDegree [Zero R]
    (i : Fin n) (bound : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degreeOf i m ≤ bound)

/-- Retain the terms whose total degree is at most `bound`. -/
def restrictTotalDegree [Zero R]
    (bound : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degree m ≤ bound)

/-- Restriction keeps exactly the coefficients whose monomials satisfy the
predicate. -/
theorem coeff_restrictBy [Zero R]
    (keep : Mono n → Bool) (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (restrictBy keep p) = if keep m then coeff m p else 0 := by
  unfold restrictBy coeff coeff?
  rw [Std.ExtTreeMap.getElem?_filter']
  cases hcoeff : p.termsInternal[m]? <;>
    cases hkeep : keep m <;>
    simp [Option.filter]

end Hex.MvPoly
