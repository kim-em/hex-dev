/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSparsePolyMathlib

/-!
Companion-import instance-coherence checks for `Hex.SparsePoly`.

Importing the Mathlib companion must leave the native executable instances
selected. The independently computed arithmetic coverage remains in the
Mathlib-free `HexSparsePoly` conformance stream and its SymPy oracle.
-/

namespace HexSparsePolyMathlib.KernelTests

open Hex

private abbrev P := SparsePoly Int
private abbrev Q := SparsePoly Rat

private def p : P := #sp[(0, 5), (1, -2), (3, 4)]

private def q : P := #sp[(1, 2), (3, -4), (6, 1)]

private def rp : Q := #sp[(0, 5), (2, -2), (5, 3)]

private def rq : Q := #sp[(2, 2), (5, -3), (7, 1)]

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

end HexSparsePolyMathlib.KernelTests
