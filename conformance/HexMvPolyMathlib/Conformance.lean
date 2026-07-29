/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvPolyMathlib

/-!
Bridge-import regression checks for `Hex.MvPoly`.

The executable guards ensure that importing the Mathlib companion does not
change the production arithmetic selected by notation. The theorem-level
checks exercise the public transport surface under lex, grlex, and grevlex.
They are API and instance-coherence checks, not an independent randomized
oracle: the independently computed randomized coverage lives in the core
conformance stream and its SymPy oracle.
-/

namespace HexMvPolyMathlib.Conformance

open scoped HexMvPolyMathlib

open Hex
open Hex.MvPoly

private abbrev P := MvPoly 2 Int Mono.lex

private def p : P :=
  ofTerms [(#v[2, 0], 3), (#v[0, 1], -2), (Mono.zero, 5)]

private def q : P :=
  ofTerms [(#v[2, 0], -3), (#v[1, 1], 4), (Mono.zero, 7)]

private def point : Fin 2 → Int := fun i => if i = 0 then 2 else -1

#guard (p + q).termCount = 3
#guard coeff #v[2, 0] (p + q) = 0
#guard coeff #v[1, 1] (p + q) = 4
#guard coeff Mono.zero (p + q) = 12
#guard p ^ 2 == p * p
#guard eval point (p * q) = eval point p * eval point q
#guard derivative 0 p = ofTerms [(#v[1, 0], 6)]
#guard homogeneousComponent 2 p = ofTerms [(#v[2, 0], 3)]

private theorem transportSurface
    (cmp : Mono 3 → Mono 3 → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (a b : MvPoly 3 Int cmp) :
    toMvPolynomial (a + b) =
        toMvPolynomial a + toMvPolynomial b ∧
      toMvPolynomial (a * b) =
        toMvPolynomial a * toMvPolynomial b ∧
      toMvPolynomial (a - b) =
        toMvPolynomial a - toMvPolynomial b ∧
      toMvPolynomial (a ^ 3) = toMvPolynomial a ^ 3 ∧
      eval (fun i => #[2, -1, 3][i]) a =
        MvPolynomial.aeval (fun i => #[2, -1, 3][i])
          (toMvPolynomial a) ∧
      toMvPolynomial (derivative 1 a) =
        MvPolynomial.pderiv 1 (toMvPolynomial a) ∧
      toMvPolynomial (homogeneousComponent 5 a) =
        MvPolynomial.homogeneousComponent 5
          (toMvPolynomial a) ∧
      toMvPolynomial
          (rename (cmp := cmp) Mono.grevlex
            (fun i : Fin 3 =>
              if i = 1 then (1 : Fin 2) else 0) a) =
        MvPolynomial.rename
          (fun i : Fin 3 =>
            if i = 1 then (1 : Fin 2) else 0)
          (toMvPolynomial a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact toMvPolynomial_add a b
  · exact toMvPolynomial_mul a b
  · exact toMvPolynomial_sub a b
  · exact toMvPolynomial_pow a 3
  · rw [← aeval_eq_eval, aeval_apply]
  · exact toMvPolynomial_derivative 1 a
  · exact toMvPolynomial_homogeneousComponent 5 a
  · exact toMvPolynomial_rename
      (fun i : Fin 3 =>
        if i = 1 then (1 : Fin 2) else 0) a

example (a b : MvPoly 3 Int Mono.lex) : True := by
  have _ := transportSurface Mono.lex a b
  trivial

example (a b : MvPoly 3 Int Mono.grlex) : True := by
  have _ := transportSurface Mono.grlex a b
  trivial

example (a b : MvPoly 3 Int Mono.grevlex) : True := by
  have _ := transportSurface Mono.grevlex a b
  trivial

end HexMvPolyMathlib.Conformance
