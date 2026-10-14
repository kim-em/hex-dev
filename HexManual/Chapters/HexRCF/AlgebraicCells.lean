/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRCF.CellReplay.Algebraic.Quoted
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Frozen cells over a selected algebraic coefficient" =>
%%%
tag := "hex-rcf-algebraic-cells"
%%%

Fix the coefficient field ℚ(√2), with its positive selected embedding in ℝ.
The polynomial X²−√2 has two real roots. The supplied complete table identifies
both roots, orders them, and supplies ordinary sector points −2, 0 and 2.
Its source matrix repeats the polynomial with opposite non-strict comparisons
and includes a zero atom. The radical certificate checks that the product of
the nonzero atoms has precisely the roots of X²−√2.

These examples import the monorepo fixture `HexRCF.CellReplay.Algebraic.Quoted`.
The original real source is proved by fresh schema preparation, fixed-coefficient
specialization, complete cell replay and quotation:

```lean
open Hex.RCF.RealCoefficients
open CellReplayTests
open Algebraic
example : ∃ x : ℝ,
    x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧
    (0 : ℝ) = 0 := Quote.source
```

The table's exact root set and strict order are proved conclusions of the
supplied replay. The positive and negative fourth roots of 2 have the same
square but different selected identities:

```lean
open Hex.RCF.RealCoefficients
open CellReplayTests
open Algebraic
open Canonical (roots)
open Schema (original)
example (x : ℝ) :
    x ∈ roots.values original ↔
      x = Real.sqrt (Real.sqrt 2) ∨
      x = -Real.sqrt (Real.sqrt 2) :=
  Meaning.roots_eq x

example :
    (roots.values original).Pairwise
      (· < ·) := Meaning.ordered
```

All coefficient signs used by these readers come from 21 distinct frozen
scalar packets. Each packet passes the owner's scalar reader in the ordinary
kernel before entering the initially empty inventory. The complete table,
section rows, sector boundaries, point descriptors and point rows are then
checked using those supplied operations. Equality laws transport the accepted
data to the canonical coefficient operations. No supplier is called during
acceptance. The matrix fold visits every cell for both quantifiers; the true
existential and false universal verdicts are checked separately.

Original divisors still enter preflight when a zero numerator removes their
value from the normalized matrix. This source retains and authenticates −1:

```lean
open Hex.RCF.RealCoefficients
open CellReplayTests
open Algebraic
example : ∃ x : ℝ,
    x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧
    0 / (-1 : ℝ) = 0 := Guards.source
```

A supplied zero divisor is rejected before decoding, including with a malformed
packet. The fresh quotation module rechecks both original proof bodies,
requires the actual frozen readers and carrier acceptance, and excludes earlier
source witnesses. Their only axioms are `propext`, `Classical.choice` and
`Quot.sound`. Kernel reduction diagnostics separately prohibit native root,
sign and scalar production while checking replay acceptance.

This example uses one supplied lawful ordinary-real parent and one fixed
complete packet. It establishes finite replay over a non-rational stored
coefficient. General provider history, automatic common-field certification,
all-live representation changes and complete algebraic construction retain
their separate obligations. The supplied-operation interface remains kernel
assembly: compiled evaluation can use its documented native fallback when
records are missing, so it is not a strict checker for arbitrary compiled
packets. This example installs no tactic handler or numerical provider.
