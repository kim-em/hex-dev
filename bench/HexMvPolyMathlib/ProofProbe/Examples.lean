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

example : p + -p = 0 := by decide +kernel
example : p ^ 3 = p * p * p := by decide +kernel
example : coeff (Mono.unit 0) p = 1 := by decide +kernel

end Hex.MvPoly.ProofExamples
