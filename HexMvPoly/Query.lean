/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Operations

public section

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

/-- Total degree is the maximum monomial degree in ordered term iteration. -/
theorem totalDegree_eq [Zero R] (p : MvPoly n R cmp) :
    totalDegree p =
      p.foldTerms (fun d m _ => max d (Mono.degree m)) 0 := by
  rfl

/-- Per-variable degree is the maximum exponent in ordered term iteration. -/
theorem degreeOf_eq [Zero R] (i : Fin n) (p : MvPoly n R cmp) :
    degreeOf i p =
      p.foldTerms (fun d m _ => max d (Mono.degreeOf i m)) 0 := by
  rfl

/-- Coordinatewise maximum of all supported exponent vectors. -/
def degrees [Zero R] (p : MvPoly n R cmp) : Mono n :=
  p.foldTerms (fun d m _ => Mono.lcm d m) Mono.zero

/-- The coordinatewise degree vector is a fold over the canonical terms. -/
theorem degrees_eq [Zero R] (p : MvPoly n R cmp) :
    degrees p =
      p.foldTerms (fun d m _ => Mono.lcm d m) Mono.zero := by
  rfl

/-- Variables occurring in at least one supported monomial, in increasing
index order. -/
def vars [Zero R] (p : MvPoly n R cmp) : List (Fin n) :=
  Mono.support p.degrees

/-- Variables are the support of the coordinatewise degree vector. -/
theorem vars_eq [Zero R] (p : MvPoly n R cmp) :
    vars p = Mono.support p.degrees := by
  rfl

/-- Greatest supported term in the polynomial's monomial order. -/
def leadingTerm [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n × R) :=
  p.maxTerm?

/-- The leading term is the maximum entry of the canonical term map. -/
theorem leadingTerm_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingTerm p = p.maxTerm? := by
  rfl

/-- Greatest supported monomial in the polynomial's monomial order. -/
def leadingMono [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n) :=
  p.leadingTerm.map Prod.fst

/-- The leading monomial is the monomial projection of the leading term. -/
theorem leadingMono_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingMono p = p.leadingTerm.map Prod.fst := by
  rfl

/-- Compatibility spelling for `leadingMono`. -/
def leadingMonomial [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Option (Mono n) :=
  p.leadingMono

/-- The compatibility spelling agrees with `leadingMono`. -/
theorem leadingMonomial_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingMonomial p = p.leadingMono := by
  rfl

/-- Coefficient of the greatest supported monomial, or zero for the zero
polynomial. -/
def leadingCoeff [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : R :=
  match p.leadingTerm with
  | none => 0
  | some term => term.2

/-- The leading coefficient is the coefficient projection of the leading
term, defaulting to zero. -/
theorem leadingCoeff_eq [Zero R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    leadingCoeff p = (p.leadingTerm.map Prod.snd).getD 0 := by
  unfold leadingCoeff
  cases p.leadingTerm <;> rfl

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

/-- Per-variable restriction is restriction by the corresponding exponent
bound. -/
theorem restrictDegree_eq [Zero R]
    (i : Fin n) (bound : Nat) (p : MvPoly n R cmp) :
    restrictDegree i bound p =
      p.restrictBy fun m => decide (Mono.degreeOf i m ≤ bound) := by
  rfl

/-- Retain the terms whose total degree is at most `bound`. -/
def restrictTotalDegree [Zero R]
    (bound : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degree m ≤ bound)

/-- Total-degree restriction is restriction by the monomial degree bound. -/
theorem restrictTotalDegree_eq [Zero R]
    (bound : Nat) (p : MvPoly n R cmp) :
    restrictTotalDegree bound p =
      p.restrictBy fun m => decide (Mono.degree m ≤ bound) := by
  rfl

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

/-- The zero polynomial has total degree zero. -/
@[simp] theorem totalDegree_zero [Zero R] :
    totalDegree (0 : MvPoly n R cmp) = 0 := by
  rfl

/-- Every variable has degree zero in the zero polynomial. -/
@[simp] theorem degreeOf_zero [Zero R] (i : Fin n) :
    degreeOf i (0 : MvPoly n R cmp) = 0 := by
  rfl

/-- The coordinatewise degree vector of zero is the zero monomial. -/
@[simp] theorem degrees_zero [Zero R] :
    degrees (0 : MvPoly n R cmp) = Mono.zero := by
  rfl

/-- No variable occurs in the zero polynomial. -/
@[simp] theorem vars_zero [Zero R] :
    vars (0 : MvPoly n R cmp) = [] := by
  simp [vars, degrees_zero, Mono.support, Mono.zero]

/-- The zero polynomial has no leading term. -/
@[simp] theorem leadingTerm_zero [Zero R] [IsMonomialOrder cmp] :
    leadingTerm (0 : MvPoly n R cmp) = none := by
  unfold leadingTerm maxTerm?
  change (∅ : Std.ExtTreeMap (Mono n) R cmp).maxEntry? = none
  exact Std.ExtTreeMap.maxEntry?_empty

/-- The zero polynomial has no leading monomial. -/
@[simp] theorem leadingMono_zero [Zero R] [IsMonomialOrder cmp] :
    leadingMono (0 : MvPoly n R cmp) = none := by
  rw [leadingMono_eq, leadingTerm_zero]
  rfl

/-- The compatibility leading-monomial spelling returns none on zero. -/
@[simp] theorem leadingMonomial_zero [Zero R] [IsMonomialOrder cmp] :
    leadingMonomial (0 : MvPoly n R cmp) = none := by
  rw [leadingMonomial_eq, leadingMono_zero]

/-- The zero polynomial has leading coefficient zero. -/
@[simp] theorem leadingCoeff_zero [Zero R] [IsMonomialOrder cmp] :
    leadingCoeff (0 : MvPoly n R cmp) = 0 := by
  rw [leadingCoeff_eq, leadingTerm_zero]
  rfl

end Hex.MvPoly
