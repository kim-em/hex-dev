/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSparsePolyMathlib

/-!
Companion-import regression checks for `Hex.SparsePoly`.

The executable guards ensure that importing the Mathlib companion does
not change the production arithmetic selected by notation. The
theorem-level checks exercise the public transport surface at a generic
`CommRing`. They are API and instance-coherence checks, not an
independent randomized oracle: the independently computed randomized
coverage lives in the core conformance stream and its SymPy oracle.
-/

namespace HexSparsePolyMathlib.Conformance

open Hex

private abbrev P := SparsePoly Int
private abbrev Q := SparsePoly Rat

private def p : P := #sp[(0, 5), (1, -2), (3, 4)]

private def q : P := #sp[(1, 2), (3, -4), (6, 1)]

private def rp : Q := #sp[(0, 5), (2, -2), (5, 3)]

private def rq : Q := #sp[(2, 2), (5, -3), (7, 1)]

/- Importing the companion alone must leave the native executable
instances selected, for two ordinary coefficient types. -/
#guard (p + q).numTerms = 2
#guard (p + q).coeff 1 = 0
#guard (p + q).coeff 3 = 0
#guard (p + q).coeff 6 = 1
#guard p ^ 2 == p * p
#guard (p * q).eval 3 = p.eval 3 * q.eval 3
#guard (rp + rq).numTerms = 2
#guard (rp + rq).coeff 5 = 0
#guard rp ^ 2 == rp * rp
#guard Hex.SparsePoly.ofDense p.toDense == p
#guard Hex.SparsePoly.ofDense rq.toDense == rq

private theorem transportSurface {R : Type} [CommRing R] [DecidableEq R]
    (a b : SparsePoly R) (x c : R) (k e : Nat) :
    equiv (a + b) = equiv a + equiv b ∧
      equiv (a * b) = equiv a * equiv b ∧
      equiv.symm (equiv a) = a ∧
      (equiv a).coeff e = a.coeff e ∧
      (equiv a).support = a.support.toList.toFinset ∧
      (equiv a).eval x = a.eval x ∧
      Polynomial.derivative (equiv a) = equiv a.derivative ∧
      (equiv a).comp (equiv b) = equiv (a.compose b) ∧
      (equiv a).comp (Polynomial.X ^ k) = equiv (a.substPow k) ∧
      (equiv a).comp (Polynomial.C c * Polynomial.X) =
        equiv (a.substScale c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact map_add equiv a b
  · exact map_mul equiv a b
  · exact equiv.symm_apply_apply a
  · exact coeff_equiv a e
  · exact equiv_support a
  · exact equiv_eval a x
  · exact equiv_derivative a
  · exact equiv_compose a b
  · exact equiv_substPow a k
  · exact equiv_substScale a c

example (a b : P) (x : Int) : True := by
  have _ := transportSurface a b x 2 3 5
  trivial

example (a b : Q) (x : Rat) : True := by
  have _ := transportSurface a b x 2 3 5
  trivial

end HexSparsePolyMathlib.Conformance
