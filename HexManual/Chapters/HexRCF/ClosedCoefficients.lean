/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRCF.RealCoefficients
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

#doc (Manual) "Closed coefficient arithmetic" =>
%%%
tag := "hex-rcf-closed-coefficients"
%%%

The frontend keeps a whole closed arithmetic expression as one coefficient.
For example, `Real.sqrt 2 + Real.sqrt 3` is one coordinate, as are its square
and its negative; repeated occurrences share that coordinate. The coefficient
interpreter evaluates the expression in the selected common field.
Bare named generators keep their direct handler; arithmetic around them uses
the common-field handler, reusing that same field for a single generator.

Here `√2` is Lean's notation for `Real.sqrt 2`.

```lean
example : ∀ x : ℝ,
    x ^ 2 + (√2 + √3) > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + (√2 + √3) ^ 2 > 0 := by
  rcf

example : ∃ x : ℝ,
    x = -(√2 + √3) ∧ x < -3 := by
  rcf
```

These examples use the real-coefficient certificate checker. Fresh-module
checks verify the corresponding named conformance proofs and their actual
body dependencies.
Extracting a whole coefficient never removes an original divisor condition:
even `0 * (1 / (Real.sqrt 2 - Real.sqrt 2))` retains its zero divisor and is
rejected during source and guard preparation.
