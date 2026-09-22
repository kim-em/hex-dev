/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Full

open Lean in
run_cmd do
  for name in [``Determinant.Full.products, ``Determinant.Full.witness,
      ``Determinant.Full.model, ``Determinant.Full.result] do
    let .thmInfo info ← getConstInfo name | throwError "expected a theorem"
    logInfo m!"PROOF_NODES {name} {Hex.Reflect.proofNodeCount #[info.value] 10000000}"

example {R : Type} [CommRing R] (x y : R) :
    (x + y) * (x + y) = x^2 + 2*x*y + y^2 ∧
    (x + y) * (x - y) = x^2 - y^2 := by
  cached_ring

example (x : Int) (h : x + 1 = x + 2) : x + 1 = x + 2 := by
  fail_if_success cached_ring
  exact h

#print axioms Determinant.Full.result
