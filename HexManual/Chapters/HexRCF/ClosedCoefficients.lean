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
even `0 * (1 / (Real.sqrt 2 - Real.sqrt 2))` keeps its zero divisor through source
preparation. The handler rejects it when preparing guards.

Nested square roots use the same source preparation. A new root is computed
over the already constructed algebraic field, then checked against its source
equation and selected positive embedding. Closed division inside the radicand
retains its denominator obligation:

```lean
example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt
      (1 / (Real.sqrt 2 + 1)) > 0 := by
  rcf
```

The [automatic selected-root regressions](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/FiniteDefault.lean)
also use a selected real root α of `X⁴ + 4X³ − X² − 7X − 2`, independently of
√2. Ordinary `by rcf` proves `∀ x, x² + α + √2 > 0`,
`∀ x, x² − (α + √2)*x + α*√2 < 0 → 1 < x ∧ x < 2`, and
`∀ x, x² + √(α + √2) > 0`. The constructor's polynomial and selected enclosure
fix α; an arbitrary real parameter with the same name is not recognized as
this coefficient. Its source certificate is retained, while the accepted
proof does not quote a new irreducibility certificate for the combined
degree-eight or nested degree-sixteen presentation.

These automatic searches have explicit finite limits. A false sentence, an
exhausted search or failed replay is terminal. Such failures do not invoke a
different solver, and a zero divisor rejects even in a cancelled expression
or an empty quantified domain. The examples establish the supported successes;
they do not assert completeness for arbitrary algebraic presentations or
caller-registered constants.
