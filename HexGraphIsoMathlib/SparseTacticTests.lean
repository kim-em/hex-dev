/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import all HexGraphIsoMathlib.TacticTests
meta import all HexGraphIsoMathlib.TacticTests

open Hex.GraphIso.Mathlib
open HexGraphIsoMathlib.TacticTests

-- Choosing the sparse encoding explicitly selects native sparse search and
-- literal replay. The correspondence transports its checked verdict back.
example : Colored.Isomorphic edgeMarkA edgeMarkB := by
  apply (Sparse.encode_iso_iff (G := edgeMarkA) (H := edgeMarkB)
    (Equiv.refl (Fin 6)) (Equiv.refl (Fin 6))).mpr
  graph_iso

set_option maxRecDepth 100000 in
example : ¬ Colored.Isomorphic edgeMarkA nonedgeMark := by
  rw [Sparse.encode_iso_iff (G := edgeMarkA) (H := nonedgeMark)
    (Equiv.refl (Fin 6)) (Equiv.refl (Fin 6))]
  graph_iso

example : Hex.GraphIso.Sparse.Isomorphic
    (Sparse.encode (Equiv.swap (0 : Fin 6) 5) edgeMarkA)
    (Sparse.encode (Equiv.refl (Fin 6)) edgeMarkB) := by
  graph_iso

private def empty : Colored (Fin 0) 0 :=
  ⟨⊥, Fin.elim0, fun c => Fin.elim0 c⟩

private instance : DecidableRel empty.graph.Adj := fun i => Fin.elim0 i

example : Colored.Isomorphic empty empty := by
  apply (Sparse.encode_iso_iff (Equiv.refl (Fin 0)) (Equiv.refl (Fin 0))).mpr
  graph_iso
