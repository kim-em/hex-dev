/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealFormula

/-!
Oracle: none for core; independent Python Fraction evaluation for emitted CI fixtures.
Mode: core and the emitted oracle are always enabled.

Covered operations: structural equality, node counts, polynomial collection,
support and degree, rename/lift/drop, selected-coordinate permutation, NNF,
implication/biconditional expansion, exact rational evaluation, checked kernel
and DAG decoding, and prenex views, encoding and adjacent quantifier swaps.

Covered properties: canonical polynomial normalization, preservation under
renaming and NNF, serialization round trips, safe unused-coordinate removal,
and restriction of prefix swaps to adjacent equal quantifiers.

Covered edge cases: zero arity and polynomials, unused variables, colliding
coordinates, cancellation, nonadjacent renaming, negative denominators,
strict/non-strict boundaries, malformed zero terms and unused branches,
self-referencing DAGs, invalid input identifiers, and alternating prefixes.
-/

namespace Hex.RealFormula.Conformance

private def x : Poly 3 := MvPoly.X 0
private def y : Poly 3 := MvPoly.X 1
private def z : Poly 3 := MvPoly.X 2
private def a : QF 3 := .atom ⟨x * x + y - MvPoly.C 2, .le⟩
private def b : QF 3 := .atom ⟨z - x, .gt⟩
private def f : QF 3 := .and a (.not b)
private def zero : QF 0 := .atom ⟨0, .eq⟩
private def cancel : QF 3 := .atom ⟨x - y, .eq⟩
private def sample (i : Fin 3) : Rat := (#[1 / 2, 1, -1] : Array Rat)[i.val]!

#guard a.evalRat sample
#guard f.evalRat sample
#guard zero.evalRat Fin.elim0
#guard !(QF.atom ⟨MvPoly.C (-1), .ge⟩ : QF 0).evalRat Fin.elim0
#guard (QF.atom ⟨x, .lt⟩).evalRat (fun _ => 1 / (-2))
#guard !a.evalRat (fun _ => 2)
#guard ([Cmp.eq, .ne, .lt, .le, .gt, .ge].map (·.evalRat 0)) ==
  [true, false, false, true, false, true]

#guard a.nodeCount == 1
#guard f.nodeCount == 4
#guard (QF.not (.not (.not f))).nodeCount == 7
#guard zero.polys.length == 1
#guard f.polys == [x * x + y - MvPoly.C 2, z - x]
#guard (QF.or f f).polys.length == 4
#guard zero.support == []
#guard a.support == [0, 1]
#guard f.support == [0, 1, 2]
#guard a.degree 0 == 2
#guard a.degree 2 == 0
#guard (QF.atom ⟨x^12 - x^12 + z^9, .ne⟩).degree 0 == 0
#guard (QF.atom ⟨x^12 - x^12 + z^9, .ne⟩).degree 2 == 9

#guard f.nnf.evalRat sample == f.evalRat sample
#guard (QF.not zero).nnf == .atom ⟨0, .ne⟩
#guard (QF.not (.and a (.not b))).nnf == .or (.atom ⟨x*x+y-MvPoly.C 2, .gt⟩) b
#guard (a.imp b).evalRat sample == false
#guard (a.iff a).evalRat sample

#guard (f.rename id) == f
#guard (f.rename (fun i => (#[2, 0, 1] : Array (Fin 3))[i.val]!)).evalRat
  (fun i => (#[1, -1, 1/2] : Array Rat)[i.val]!) == f.evalRat sample
#guard (cancel.rename (fun _ => (0 : Fin 1))) == .atom ⟨0, .eq⟩
#guard (f.moveLast 0).moveLast 0 == f
#guard f.moveLast? 2 == some f
#guard f.moveLast? 3 == none
#guard zero.lift.evalRat (fun _ => 99)
#guard f.lift.degree 3 == 0
#guard (f.lift.drop? 3) == some f
#guard f.drop? 0 == none
#guard a.drop? 2 == some (.atom ⟨MvPoly.X 0 * MvPoly.X 0 + MvPoly.X 1 - MvPoly.C 2, .le⟩)

#guard QF.ofKernel? zero.toKernel == some zero
#guard QF.ofKernel? f.toKernel == some f
#guard QF.ofKernel? (QF.or f f).toKernel == some (.or f f)
#guard (QF.ofKernel? ⟨1, 1, .atom [([1], 2), ([1], -2), ([0], 0)] .eq⟩ : Option (QF 1)) ==
  some (.atom ⟨0, .eq⟩)
#guard (QF.ofKernel? ⟨1, 1, .atom [([0, 0], 0)] .eq⟩ : Option (QF 1)) == none
#guard (QF.ofKernel? ⟨1, 1, .or .tt (.atom [([], 0)] .eq)⟩ : Option (QF 1)) == none
#guard (QF.ofKernel? ⟨2, 0, .tt⟩ : Option (QF 0)) == none
#guard (QF.ofKernel? ⟨1, 2, .ff⟩ : Option (QF 0)) == none
#guard (f.toKernel.validate.map (fun p => p.evalRat sample)) == some true
#guard (Kernel.Dag.decode ⟨1, 0, #[.input 0, .not 0, .or 0 1], 2⟩ #[zero]) ==
  some (.or zero (.not zero))
#guard (Kernel.Dag.decode ⟨1, 0, #[.not 0], 0⟩ #[]) == none
#guard (Kernel.Dag.decode ⟨1, 0, #[.tt, .input 1], 0⟩ #[zero]) == none
#guard (Kernel.Dag.decode ⟨1, 0, #[.tt], 1⟩ #[]) == none

private def quantified : Prenex 1 := .quant .existsReal (.quant .forallReal (.matrix f))
private def same : Prenex 1 := .quant .existsReal (.quant .existsReal (.matrix f))
#guard quantified.toView.prefix == [.existsReal, .forallReal]
#guard quantified.toView.matrix == f
#guard Prenex.ofView quantified.toView == quantified
#guard Prenex.ofKernel? quantified.toKernel == some quantified
#guard quantified.nodeCount == 6
#guard quantified.swap? 0 == none
#guard same.swap? 2 == none
#guard ((same.swap? 0).bind (·.swap? 0)) == some same
#guard (Prenex.matrix zero).toView.prefix == []

#guard (Prenex.matrix zero).nodeCount == 1
#guard (Prenex.quant .existsReal (.matrix .tt) : Prenex 0).nodeCount == 2
#guard (Prenex.matrix zero).rename (id : Fin 0 → Fin 0) == .matrix zero
#guard (quantified.rename (fun _ => (1 : Fin 2))).toView.matrix ==
  f.rename (fun i => (#[1, 2, 3] : Array (Fin 4))[i.val]!)
#guard ((Prenex.quant .existsReal (.matrix cancel) : Prenex 2).rename
  (fun _ => (0 : Fin 1))) == .quant .existsReal (.matrix (.atom ⟨0, .eq⟩))
#guard Prenex.ofView (Prenex.matrix zero).toView == .matrix zero
#guard Prenex.ofView same.toView == same
#guard Prenex.ofKernel? (Prenex.matrix zero).toKernel == some (.matrix zero)
#guard Prenex.ofKernel? same.toKernel == some same
#guard (Prenex.ofKernel? ⟨1, 0, [.existsReal], ⟨1, 0, .tt⟩⟩ : Option (Prenex 0)) == none
#guard (Prenex.ofKernel? ⟨2, 0, [], ⟨1, 0, .tt⟩⟩ : Option (Prenex 0)) == none
#guard (Prenex.ofKernel? ⟨1, 1, [], ⟨1, 1, .tt⟩⟩ : Option (Prenex 0)) == none
#guard (Prenex.quant .forallReal (.quant .forallReal (.matrix zero.lift.lift))).swap? 0 ==
  some (.quant .forallReal (.quant .forallReal (.matrix zero.lift.lift)))

end Hex.RealFormula.Conformance
