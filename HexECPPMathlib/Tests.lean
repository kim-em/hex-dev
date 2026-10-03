/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib
import HexECPPMathlib.Tests.ModuleReplay
import HexECPPMathlib.Tests.Frozen512
import HexECPPMathlib.Tests.Native512
import HexECPPMathlib.LintTests

/-! # Published companion trust checks

These guards run in the published test target as well as monorepo CI. The
upstream Hasse capstone and unconditional primality theorems must retain only
the three standard Lean axioms. The importing module tests compact replay and
exact native suggestions; the API linter covers all companion modules.
-/

/-- info: 'HasseWeil.WeilPairing.hasse_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasseWeil.WeilPairing.hasse_bound

/-- info: 'Hex.ECPP.hasse_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ECPP.hasse_sq

/-- info: 'Hex.ECPP.hasse_sq_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ECPP.hasse_sq_zmod

/-- info: 'Hex.ECPP.natPrime_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ECPP.natPrime_of_check

/-- info: 'Hex.ECPP.natPrime_of_checkAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.ECPP.natPrime_of_checkAt

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

example (p : Nat) [Fact p.Prime] {K : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod p) K] (W : WeierstrassCurve.Affine (ZMod p)) (P : (W⁄K).Point) :
    Hex.ECPP.oneSubFrobenius p W P = 0 ↔ Hex.ECPP.pointFrobenius p W P = P := by
  simp
