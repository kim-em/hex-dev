/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPoly.Fixtures

/-!
Core executable conformance checks for `hex-mv-poly`.

Oracle: SymPy
Mode: `if_available` locally, required in release CI

Covered operations:
- monomial construction, multiplication, scaling, divisibility, exact
  division, lattice operations, degrees, support, rename, successor, splits,
  products, and the lex/grlex/grevlex comparators;
- polynomial construction (`C`, `X`, `monomial`, `ofTerms`), canonical
  iteration/lookups, all ring operations, powers, degree/support/leading-term
  queries, and support restrictions;
- direct and Horner evaluation, mapped evaluation, and partial evaluation;
- derivative, homogeneous component, reorder, rename, `bind`, `subst`, and
  `bind₁`;
- both recursive-view conversions at every main-variable position.

Covered properties:
- stored terms are nonzero, unique, comparator-ordered, and agree with
  coefficient lookup and every public iteration view;
- additive and multiplicative identities, commutativity, distributivity,
  power recurrence, and cancellation normalize back to canonical form;
- degree, variable, restriction, evaluation, derivative, and transformation
  results agree with independently stated term-level contracts;
- recursive views round-trip in both directions.

Covered edge cases:
- zero, constants, arity zero, duplicate monomials, and zero coefficients;
- cancellation in addition, multiplication, rename, substitution, and partial
  evaluation;
- non-divisible monomials, empty supports, and first/middle/last recursive
  main-variable positions;
- equal-total-degree monomials that distinguish grlex from grevlex.
-/

namespace Hex.MvPolyConformance

open Hex
open Hex.MvPoly
open Hex.MvPolyFixtures

private def absentMono : Mono 3 := #v[9, 9, 9]

private def representationContract (p : P3) : Bool :=
  decide (p.toList = p.termsList) &&
  decide (p.support = p.monomials) &&
  decide (p.monomials = p.termsList.map Prod.fst) &&
  decide (p.termCount = p.termsList.length) &&
  decide
    (p.foldTerms (fun acc _ c => acc + c) 0 =
      p.termsList.foldl (fun acc term => acc + term.2) 0) &&
  p.termsList.all (fun term =>
    decide (term.2 ≠ 0) && decide (coeff term.1 p = term.2)) &&
  decide (coeff absentMono p = 0)

private def queryContract (p : P3) : Bool :=
  let terms := p.termsList
  let expectedTotal :=
    terms.foldl (fun d term => max d (Mono.degree term.1)) 0
  let expectedDegrees :=
    terms.foldl (fun d term => Mono.lcm d term.1) Mono.zero
  let expectedLeading := terms.getLast?
  let evenDegree (m : Mono 3) := decide (Mono.degree m % 2 = 0)
  decide (p.totalDegree = expectedTotal) &&
  (List.finRange 3).all (fun i =>
    decide
      (p.degreeOf i =
        terms.foldl (fun d term => max d (Mono.degreeOf i term.1)) 0)) &&
  decide (p.degrees = expectedDegrees) &&
  decide (p.vars = Mono.support expectedDegrees) &&
  decide (p.leadingTerm = expectedLeading) &&
  decide (p.leadingMono = expectedLeading.map Prod.fst) &&
  decide (p.leadingMonomial = expectedLeading.map Prod.fst) &&
  decide (p.leadingCoeff = (expectedLeading.map Prod.snd).getD 0) &&
  decide
    (p.restrictBy evenDegree =
      ofTerms (terms.filter fun term => evenDegree term.1)) &&
  decide
    (p.restrictDegree 1 2 =
      ofTerms (terms.filter fun term => decide (Mono.degreeOf 1 term.1 ≤ 2))) &&
  decide
    (p.restrictTotalDegree 3 =
      ofTerms (terms.filter fun term => decide (Mono.degree term.1 ≤ 3)))

private def ringContract (p : P3) : Bool :=
  let q := addLeft
  decide (p + 0 = p) &&
  decide (0 + p = p) &&
  decide (p + q = q + p) &&
  decide (p - p = 0) &&
  decide (-(-p) = p) &&
  decide (p * 0 = 0) &&
  decide (0 * p = 0) &&
  decide (p * 1 = p) &&
  decide (1 * p = p) &&
  decide (p * q = q * p) &&
  decide (p * (q + 1) = p * q + p) &&
  decide ((p + q) * q = p * q + q * q) &&
  decide (p ^ 3 = (p * p) * p)

private def evalContract (p : P3) : Bool :=
  let x : Fin 3 → Int := fun i => #[2, -1, 3][i]
  let direct :=
    p.termsList.foldl (fun acc term => acc + term.2 * Mono.prod x term.1) 0
  let mapped :=
    p.termsList.foldl
      (fun acc term => acc + (2 * term.2) * Mono.prod x term.1) 0
  decide (eval x p = direct) &&
  decide (evalHorner x p = direct) &&
  decide (eval₂ (fun c => 2 * c) x p = mapped) &&
  decide (eval₂Horner (fun c => 2 * c) x p = mapped) &&
  decide (partialEval (fun _ => none) p = p)

private def derivativeTerms (i : Fin 3) (p : P3) :
    List (Mono 3 × Int) :=
  p.termsList.filterMap fun term =>
    let e := Mono.degreeOf i term.1
    if e = 0 then none else some (predAt i term.1, (e : Int) * term.2)

private def structuralContract (p : P3) : Bool :=
  let degreeTwo (m : Mono 3) := decide (Mono.degree m = 2)
  decide (derivative 0 p = ofTerms (derivativeTerms 0 p)) &&
  decide
    (homogeneousComponent 2 p =
      ofTerms (p.termsList.filter fun term => degreeTwo term.1)) &&
  decide (reorder Mono.grlex (reorder Mono.lex p) = p) &&
  decide (rename Mono.grlex id p = p) &&
  decide (subst (targetCmp := Mono.grlex) X p = p) &&
  decide (bind id X p = p) &&
  decide (bind₁ (targetCmp := Mono.grlex) X p = p) &&
  decide (sumToIter p = p)

private def recursiveContract (p : P3) : Bool :=
  decide
    (ofUnivariate (cmp := Mono.grlex) 0 Mono.grlex
      (toUnivariate 0 Mono.grlex p) = p) &&
  decide
    (ofUnivariate (cmp := Mono.grlex) 1 Mono.grlex
      (toUnivariate 1 Mono.grlex p) = p) &&
  decide
    (ofUnivariate (cmp := Mono.grlex) 2 Mono.grlex
      (toUnivariate 2 Mono.grlex p) = p)

#guard representationContract viewInput
#guard representationContract (0 : P3)
#guard representationContract duplicateInput

#guard queryContract viewInput
#guard queryContract (0 : P3)
#guard queryContract duplicateInput

#guard ringContract viewInput
#guard ringContract (0 : P3)
#guard ringContract duplicateInput

#guard evalContract viewInput
#guard evalContract (0 : P3)
#guard evalContract duplicateInput

#guard structuralContract viewInput
#guard structuralContract (0 : P3)
#guard structuralContract duplicateInput

#guard recursiveContract viewInput
#guard recursiveContract (0 : P3)
#guard recursiveContract duplicateInput

/-! Constructor coverage: typical, zero/edge, and cancellation/duplicate. -/

#guard (C 7 : P3) = ofTerms [(Mono.zero, 7)]
#guard (C 0 : P3) = 0
#guard (C (-11) : P3) = ofTerms [(Mono.zero, -11)]

#guard (X 0 : P3) = ofTerms [(#v[1, 0, 0], 1)]
#guard (X 1 : P3) = ofTerms [(#v[0, 1, 0], 1)]
#guard (X 2 : P3) = ofTerms [(#v[0, 0, 1], 1)]

#guard (monomial #v[2, 1, 0] 5 : P3) =
  ofTerms [(#v[2, 1, 0], 5)]
#guard (monomial #v[2, 1, 0] 0 : P3) = 0
#guard (monomial #v[7, 0, 9] (-3) : P3) =
  ofTerms [(#v[7, 0, 9], -3)]

#guard (ofTerms viewInput.termsList : P3) = viewInput
#guard (ofTerms [] : P3) = 0
#guard (ofTerms duplicateTerms : P3) = duplicateInput

/-! Monomial API coverage. -/

#guard (Mono.zero : Mono 0) = #v[]
#guard (Mono.zero : Mono 1) = #v[0]
#guard (Mono.zero : Mono 3) = #v[0, 0, 0]

#guard Mono.unit (0 : Fin 3) = #v[1, 0, 0]
#guard Mono.unit (1 : Fin 3) = #v[0, 1, 0]
#guard Mono.unit (2 : Fin 3) = #v[0, 0, 1]

#guard Mono.mul #v[1, 2, 0] #v[3, 0, 4] = #v[4, 2, 4]
#guard Mono.mul (#v[0, 0, 0] : Mono 3) #v[3, 0, 4] = #v[3, 0, 4]
#guard Mono.mul #v[12, 1, 9] #v[8, 7, 11] = #v[20, 8, 20]

#guard Mono.scale 3 #v[1, 2, 0] = #v[3, 6, 0]
#guard Mono.scale 0 (#v[7, 4, 1] : Mono 3) = #v[0, 0, 0]
#guard Mono.scale 9 #v[12, 0, 3] = #v[108, 0, 27]

#guard Mono.dvd #v[1, 2, 0] #v[3, 2, 4]
#guard Mono.dvd (#v[0, 0, 0] : Mono 3) #v[3, 2, 4]
#guard !(Mono.dvd #v[4, 2, 0] #v[3, 2, 4])

#guard Mono.div #v[1, 2, 0] #v[4, 2, 4] = some #v[3, 0, 4]
#guard Mono.div (#v[0, 0, 0] : Mono 3) #v[4, 2, 4] =
  some #v[4, 2, 4]
#guard Mono.div #v[1, 0, 2] #v[2, 0, 1] = none

#guard Mono.lcm #v[1, 4, 2] #v[3, 2, 5] = #v[3, 4, 5]
#guard Mono.lcm (#v[0, 0, 0] : Mono 3) #v[3, 2, 5] = #v[3, 2, 5]
#guard Mono.lcm #v[20, 1, 0] #v[0, 17, 9] = #v[20, 17, 9]

#guard Mono.gcd #v[1, 4, 2] #v[3, 2, 5] = #v[1, 2, 2]
#guard Mono.gcd (#v[0, 0, 0] : Mono 3) #v[3, 2, 5] = #v[0, 0, 0]
#guard Mono.gcd #v[20, 1, 9] #v[8, 17, 9] = #v[8, 1, 9]

#guard Mono.degree #v[1, 4, 2] = 7
#guard Mono.degree (#v[0, 0, 0] : Mono 3) = 0
#guard Mono.degree #v[20, 17, 9] = 46

#guard Mono.degreeOf 1 #v[1, 4, 2] = 4
#guard Mono.degreeOf 0 (#v[0, 0, 0] : Mono 3) = 0
#guard Mono.degreeOf 2 #v[20, 17, 9] = 9

#guard (Mono.support #v[1, 0, 2]).map Fin.val = [0, 2]
#guard (Mono.support (#v[0, 0, 0] : Mono 3)).map Fin.val = []
#guard (Mono.support #v[9, 8, 7]).map Fin.val = [0, 1, 2]

#guard Mono.rename id #v[1, 4, 2] = #v[1, 4, 2]
#guard Mono.rename (fun _ => (0 : Fin 1)) #v[1, 4, 2] = #v[7]
#guard Mono.rename (fun i => if i = 1 then (0 : Fin 2) else 1)
    #v[1, 4, 2] = #v[4, 3]

#guard Mono.succAt 1 #v[1, 4, 2] = #v[1, 5, 2]
#guard Mono.succAt 0 (#v[0, 0, 0] : Mono 3) = #v[1, 0, 0]
#guard Mono.succAt 2 #v[20, 17, 9] = #v[20, 17, 10]

private def splitsContract {n : Nat} (m : Mono n) : Bool :=
  (Mono.splits m).all fun pair => decide (Mono.mul pair.1 pair.2 = m)

#guard splitsContract (#v[2, 1] : Mono 2) &&
  (Mono.splits #v[2, 1]).length == 6
#guard splitsContract (#v[0, 0] : Mono 2) &&
  (Mono.splits #v[0, 0]).length == 1
#guard splitsContract (#v[4, 3] : Mono 2) &&
  (Mono.splits #v[4, 3]).length == 20

#guard Mono.prod (fun i => #[2, -1, 3][i]) #v[2, 1, 3] = -108
#guard Mono.prod (fun i => #[2, -1, 3][i])
    (#v[0, 0, 0] : Mono 3) = 1
#guard Mono.prod (fun i => #[2, 0, 3][i]) #v[9, 2, 1] = 0

/-! Comparator direction and tie-break coverage. -/

#guard Mono.lex #v[1, 5, 0] #v[2, 0, 9] = .lt
#guard Mono.lex (#v[0, 0, 0] : Mono 3) #v[0, 0, 1] = .lt
#guard Mono.lex #v[7, 1, 4] #v[7, 1, 4] = .eq

#guard Mono.grlex #v[4, 0, 0] #v[1, 1, 1] = .gt
#guard Mono.grlex (#v[0, 0, 0] : Mono 3) #v[0, 0, 1] = .lt
#guard Mono.grlex #v[1, 0, 1] #v[0, 2, 0] = .gt

#guard Mono.grevlex #v[1, 0, 1] #v[0, 2, 0] = .lt
#guard Mono.grevlex (#v[0, 0, 0] : Mono 3) #v[0, 0, 1] = .lt
#guard Mono.grevlex #v[7, 1, 4] #v[7, 1, 4] = .eq

#guard duplicateInput =
  ofTerms [(#v[2, 0, 1], 1), (#v[1, 1, 0], 5)]

#guard addLeft + addRight = ofTerms [(#v[0, 1, 0], 5)]
#guard addLeft + (-addLeft) = 0

#guard mulLeft * mulRight =
  ofTerms [(#v[2, 0, 0], 1), (Mono.zero, -1)]
#guard mulLeft * 0 = 0

#guard zero3.totalDegree = 0
#guard zero3.degreeOf 0 = 0
#guard zero3.vars = []
#guard zero3.leadingTerm = none
#guard zero3.leadingCoeff = 0

#guard constant3.totalDegree = 0
#guard constant3.degreeOf 2 = 0
#guard constant3.vars = []
#guard constant3.leadingTerm = some (Mono.zero, -7)
#guard constant3.leadingCoeff = -7

#guard arityZero = C 1
#guard arityZero.totalDegree = 0
#guard arityZero.vars = []
#guard arityZero.leadingTerm = some (Mono.zero, 1)

#guard
  rename Mono.lex (fun _ => (0 : Fin 1)) renameInput = (C 4 : P1)

#guard
  subst (targetCmp := Mono.lex)
      (fun _ => (X 0 : P1)) substInput =
    ofTerms [(#v[1], 2), (#v[2], 2)]

#guard
  partialEval (fun i => if i = 0 then some 2 else none) partialInput =
    0

#guard ofUnivariate 0 Mono.grlex (toUnivariate 0 Mono.grlex viewInput) =
  viewInput
#guard ofUnivariate 1 Mono.grlex (toUnivariate 1 Mono.grlex viewInput) =
  viewInput
#guard ofUnivariate 2 Mono.grlex (toUnivariate 2 Mono.grlex viewInput) =
  viewInput

private def viewCoeffs : DensePoly P2 :=
  DensePoly.ofCoeffs #[
    ofTerms [(#v[1, 0], 2), (Mono.zero, 1)],
    ofTerms [(#v[0, 2], -3)],
    0,
    ofTerms [(#v[1, 1], 4)]]

#guard toUnivariate 0 Mono.grlex
    (ofUnivariate (cmp := Mono.grlex) 0 Mono.grlex viewCoeffs) = viewCoeffs
#guard toUnivariate 1 Mono.grlex
    (ofUnivariate (cmp := Mono.grlex) 1 Mono.grlex viewCoeffs) = viewCoeffs
#guard toUnivariate 2 Mono.grlex
    (ofUnivariate (cmp := Mono.grlex) 2 Mono.grlex viewCoeffs) = viewCoeffs

#guard coeff #v[3, 0, 1] (reorder Mono.lex viewInput) =
  coeff #v[3, 0, 1] viewInput
#guard coeff #v[0, 2, 4] (reorder Mono.grevlex viewInput) =
  coeff #v[0, 2, 4] viewInput
#guard coeff #v[1, 1, 0]
    (reorder Mono.grlex (reorder Mono.grevlex viewInput)) =
  coeff #v[1, 1, 0] viewInput

#guard eval (fun i => #[2, -1, 3][i]) viewInput = -315
#guard evalHorner (fun i => #[2, -1, 3][i]) viewInput = -315

end Hex.MvPolyConformance
