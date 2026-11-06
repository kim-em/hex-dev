/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public import Mathlib.Analysis.Real.Pi.Bounds
public meta import HexRCF.ProofEvidence
public meta import Lean
public section

namespace Hex.RCF.PolynomialDirect
open RealCoefficients Hex.OrderedFn.Oracle
set_option Elab.async false
set_option maxHeartbeats 800000

@[expose] def bounds : Bounds := ⟨3, mkRat 63 20, by decide⟩

@[rcf_constant, expose] def registration : Registration Real.pi where
  version := 1
  approximation _ := bounds
  containment _ _ := by
    norm_num [Contains, bounds, mkRat]
    exact ⟨Real.pi_gt_three.le, by linarith [Real.pi_lt_d2]⟩

theorem square : ∀ x : ℝ, x ^ 2 > Real.pi - 4 := by rcf
theorem linear : ∃ x : ℝ, x = Real.pi ∧ 2 < x ∧ x < 4 := by rcf
theorem designatedSquare : ∃ x : ℝ, 0 < x ∧ x ^ 2 = Real.pi ^ 2 := by rcf
theorem designatedBounds : ∃ x : ℝ, x ^ 2 ≥ 9 ∧ x ≥ Real.pi := by rcf

theorem witness : ∃ x : ℝ, x = Real.pi ∧ (x - 63 / 20) ^ 2 ≥ 0 := by rcf

open Lean Meta in
run_meta withoutExporting do
  for root in #[``square, ``linear, ``witness, ``designatedSquare, ``designatedBounds] do
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[root]
    if dependencies.contains ``PolynomialBuild.check_sound then
      throwError "coarse-bound direct regression entered root search: {root}"
    let axioms ← collectAxioms root
    unless axioms.all (fun name => [``propext, ``Classical.choice, ``Quot.sound].contains name) do
      throwError "coarse-bound direct proof has unexpected axioms: {root}: {axioms}"
  logInfo "POLYNOMIAL_DIRECT: coarse-bound universal, linear, explicit and designated nonlinear witnesses retain direct proofs"

end Hex.RCF.PolynomialDirect
