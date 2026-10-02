/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib

public section

namespace Hex.MvPoly.ProofExamples
open Hex
open scoped Hex

abbrev P := MvPoly 2 Int Mono.lex
@[expose] def p : P := C 1 + X 0 + X 1

theorem cancel : p + -p = 0 := by decide +kernel
theorem power : p ^ 3 = p * p * p := by decide +kernel
theorem coefficient : coeff (Mono.unit 0) p = 1 := by decide +kernel

/-- info: 'Hex.MvPoly.ProofExamples.cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cancel
/-- info: 'Hex.MvPoly.ProofExamples.power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms power
/-- info: 'Hex.MvPoly.ProofExamples.coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coefficient

end Hex.MvPoly.ProofExamples
