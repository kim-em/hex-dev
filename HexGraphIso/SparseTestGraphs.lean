/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraph.Sparse.Build
public import HexGraphIso.Sparse.Colored

@[expose] public section

namespace Hex.GraphIso.SparseTestGraphs

def empty : Sparse.Colored 0 0 :=
  ⟨SparseGraph.ofEdges [], ⟨#v[], fun c => Fin.elim0 c⟩⟩

/-- Native Petersen graph used by the ordered-colour replay campaign. -/
def petersen : SparseGraph 10 := SparseGraph.ofEdges [
  (0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
  (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
  (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

/-- Give the marked pair colour zero and every other vertex colour one. -/
def markPair (a b : Fin 10) : Coloring 10 2 :=
  (Coloring.ofVector? (Hex.Vector.ofFn' fun i =>
    if i = a ∨ i = b then 0 else 1)).getD (Coloring.mod 10 2)

def edgeMarkA : Sparse.Colored 10 2 := ⟨petersen, markPair 0 1⟩
def edgeMarkB : Sparse.Colored 10 2 := ⟨petersen, markPair 2 3⟩
def nonedgeMark : Sparse.Colored 10 2 := ⟨petersen, markPair 0 2⟩

/-- The recorded first order-12 graph under `TestGraphs.perm12`, expressed
directly as native edge literals for imported-module kernel replay. -/
def random12relabeled : Sparse.Colored 12 1 :=
  ⟨SparseGraph.ofEdges [
    (0, 1), (0, 3), (0, 11), (1, 3), (1, 7), (1, 8), (1, 11),
    (2, 4), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6),
    (3, 7), (3, 8), (4, 6), (4, 7), (4, 9), (4, 11), (5, 6),
    (5, 7), (5, 8), (5, 9), (6, 7), (6, 9), (6, 10), (7, 11),
    (8, 10), (9, 10)], Coloring.trivial 12⟩

/-- Native sparse edges of the recorded first order-12 random corpus graph
(`TestGraphs.mask12`). No dense graph is constructed. -/
def random12 : Sparse.Colored 12 1 :=
  ⟨SparseGraph.ofEdges [(0, 1), (0, 2), (0, 3), (0, 10), (0, 11), (1, 2), (1, 3), (1, 6), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 7), (2, 10), (3, 4), (3, 6), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 9), (7, 10), (7, 11), (8, 9), (9, 10), (10, 11)], Coloring.trivial 12⟩

/-- Native sparse edges of the recorded second order-12 corpus graph
(`TestGraphs.mask12b`). -/
def random12b : Sparse.Colored 12 1 :=
  ⟨SparseGraph.ofEdges [(0, 5), (0, 6), (0, 7), (0, 9), (0, 10), (0, 11), (1, 2), (1, 3), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 6), (2, 8), (2, 10), (2, 11), (3, 6), (3, 9), (3, 10), (4, 7), (4, 9), (4, 10), (4, 11), (5, 7), (5, 9), (5, 10), (5, 11), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 9), (7, 10), (7, 11), (8, 11), (9, 11), (10, 11)], Coloring.trivial 12⟩

end Hex.GraphIso.SparseTestGraphs
