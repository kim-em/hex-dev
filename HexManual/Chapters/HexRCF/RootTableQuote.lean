/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients
import HexRCF.RootTableQuote.Semantics
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "An ordinary real root over a selected field" =>
%%%
tag := "hex-rcf-root-table-quotation"
%%%

A polynomial over a selected real number field can require a new algebraic
root. For example, if the coefficient is the selected positive square root
of 2, the polynomial `X² − √2` has two real roots. Its positive root lies
strictly between 1 and 2. The monorepo example imports
`HexRCF.RootTableQuote.Semantics` and proves:

```lean
open Hex.RCF.RootTableQuoteTests in
example : ∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 ∧
      1 < x ∧ x < 2 :=
  witness
```

The conformance module reads the complete supplied root table with
{name Hex.RCF.RealCoefficients.RootTable.read}`RootTable.read`.
The polynomial's stored coefficients are first reconstructed with
{name Hex.RCF.RealCoefficients.ScalarQuote.quotePolyWith}`ScalarQuote.quotePolyWith`
and the selected parent's checked sign facts. A proved equality retains that
parent's defining polynomial and reduction operation. The table reader checks
the supplied root data for this exact polynomial and returns two roots.
{name Hex.RCF.RealCoefficients.RootQuote.quote}`RootQuote.quote`
accepts its structured `Replay.Error` result type and emits the checked
original-reader equation. A rejected reader remains terminal.

{name Hex.RCF.RealCoefficients.RootReplay.fromTable}`RootReplay.fromTable`
transports the checked table to the existing real root-coverage theorem.
The coefficient interpretation identifies the exact polynomial with
`X² − C (Real.sqrt 2)`. Taking the absolute value of one interpreted root
provides one ordinary real point satisfying the equation and both bounds.
The proof uses the same selected positive embedding throughout. It does not
assume a root, treat an infinitesimal as a real witness, or use the rational
solver for an irrational coefficient. The complete solution-set regression also
uses the converse coverage direction and absence of duplicate roots: the list
has length two, is duplicate-free, and contains exactly the real numbers whose
square is `Real.sqrt 2`. The witness uses the certified reconstructed data;
`checked_witness` additionally retains both original reader equations. Its
bounds follow from the coefficient's checked bounds and the squared equation.

```lean
open Hex.RCF.RootTableQuoteTests in
open Hex.RCF.SelectedRootTests in
example :
    (roots.values Data.original).length = 2 ∧
    (roots.values Data.original).Nodup ∧
    ∀ y : ℝ, y ^ 2 = Real.sqrt 2 ↔
      y ∈ roots.values Data.original :=
  solutions
```


The fresh importing conformance module checks all 74 reachable example theorem
bodies and 14 definitions under the kernel producer guard, including private
auxiliaries and the final witness. The complete axiom closure contains only
`propext`, `Classical.choice` and `Quot.sound`. The stored polynomial request
accounts for 1,827 proof nodes and the table request for 121,995; these are
request accounting, not physical proof sharing or a speedup measurement.

Source-bound build observations are recorded separately in the linked report.
They include reused dependencies and establish no scaling or matched
performance comparison. The examples raise Lean limits to 12,000,000
heartbeats and recursion depth 32,768. Larger inputs or default limits may
exhaust.

When retaining the quoted data as a definition for compiled consumers, emit
both artifacts: `addDecl` checks the kernel declaration, and `compileDecl`
compiles it. The conformance client explicitly does both for the polynomial
and reconstructed table. Compiled controls check the original reader's success,
the reconstructed table's two roots, and rejection when scalar-decoding facts
are missing.

This is a direct checked API example. It does not install the general
source-to-certificate tactic, authenticate arbitrary provider histories or
prove accepted completeness. The missing-scalar control does not establish
that every omitted arithmetic record prevents native work in a whole reader.
The exact sources, completed diagnostics and proof inventory are retained in
[the root-table quotation record](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-packet-quotation.md).
