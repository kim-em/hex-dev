/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRCF.RealCoefficients
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Complete checked cells in an ordinary real model" =>
%%%
tag := "hex-rcf-checked-cells"
%%%

A complete root table cuts the real line into root sections and open sectors.
{name Hex.RCF.RealCoefficients.CellRead.read}`CellRead.read` checks a supplied
row at every section and sector. It requires the exact number of rows in their
original order. Each section refers to its actual descriptor in the accepted
full table. Every sector supplies one ordinary point, selected signs comparing
that point with its adjacent roots, and a checked linear descriptor for the
same point. An absent infinite boundary uses a literal null marker. The whole
matrix is evaluated at that one point, retaining repeated and zero atoms.

{name Hex.RCF.RealCoefficients.CellReplay.check}`CellReplay.check` first checks
every original divisor. It then checks the supplied radical identities relating
the product of nonzero specialized atoms to the table's head. The accepted table
proves squarefreeness, complete root coverage and strict order. These conclusions
prove that atom signs are constant on each cell. Checked sample membership and
whole-row signs therefore establish the formula throughout each cell. Neither
coverage nor per-cell sign agreement is an assumed field of the certificate.

{name Hex.RCF.RealCoefficients.CellReplay.check_sound}`check_sound` composes
those checked conclusions with the shared strict quantifier fold:

```lean
open Hex Hex.RealClosure
open Hex.RealClosure.Tower
open Hex.RCF.RealCoefficients
example
    {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    {n : Nat}
    (model : Model parent ℝ)
    (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1))
    (guards : List parent.Value)
    (cert : RadicalCert
      parent.Value Tower.Signature)
    (roots : RootReplay.Result
      cert.core .negInf .posInf)
    (rows : CellReplay.Evidence
      roots values formula)
    (quantifier : RealFormula.Quantifier)
    (accepted : CellReplay.check values
      formula guards cert roots rows
      quantifier = .ok true) :
    (RealFormula.Prenex.quant quantifier
      (.matrix formula)).toProp
      (fun i => model.value (values i)) :=
  CellReplay.check_sound model values
    formula guards cert roots rows
    quantifier accepted
```

The companion {name Hex.RCF.RealCoefficients.CellReplay.check_domains}`check_domains`
extracts all original nonzero divisors. Their identities with the freshly
recognized source expressions, their order, the fixed coefficient valuation
and the exact quantified formula are checked by
{name Hex.RCF.RealCoefficients.CellQuote.finish}`CellQuote.finish`. Quotation
checks the ordinary proof against the original target and restores caller
state on failure. Half-open source domains remain inequality atoms in that
formula; they do not change the root queries' open-domain requirements.

The [frozen five-cell regression](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/CellReplay/Check.lean)
uses both roots of X²−2 and ordinary sector points −2, 0 and 2. Its repeated
atom and zero atom survive specialization and strict row evaluation. The
[fresh source proofs](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/CellReplay/Quote.lean)
exercise existential and universal quotation, including the original divisor −1.
True and false verdicts are checked separately; an accepted false result is
only diagnostic. Changed points, swapped sections, a missing sector, a valid
linear descriptor for another point, invalid context indices, cycles and missing basis
evidence are rejected. The reader decodes all rows regardless of the matrix; a later invalid row
remains an evidence error even when the matrix is false. All original guards
precede decoding and Boolean shortcuts.

Further source controls authenticate `Real.sqrt 4` as the stored value 2 and
retain two divisors, −1 and 2. Reversing their identities or using that valuation
for `Real.sqrt 9` fails with caller-state restoration. This exercises a nonempty
frontend valuation over rational stored coefficients. A constant-only regression
has no roots and one sector with both boundaries absent. Both quantifiers check
true and false matrices; a zero divisor still fails before decoding. Boundary
controls reject wrong endpoint presence, swapped bounds and a sample outside
its claimed sector.

The source proofs, their actual dependencies and all new theorem axioms are
audited separately from producer diagnostics. Their axioms are exactly
`propext`, `Classical.choice` and `Quot.sound`. The checked records round-trip
through the owner's codecs. Shared JSON constructor data does not imply that
separate row readers share validation work.

This generic checked-cell interface assumes an actual lawful model of the
parent in ℝ. It neither constructs that model from arbitrary provider history
nor interprets an infinitesimal as a real number. Its frozen rational and fixed algebraic regressions
are evidence for finite complete-cell assembly and source quotation; they do not
establish general algebraic production, accepted completeness, automatic
common-field construction or a strict compiled checker with arbitrary missing
predecessor records. Nested contexts still require their checked arithmetic
and full source authentication. This interface adds no tactic handler.
