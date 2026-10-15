/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRCF.CellReplay.Algebraic.BooleanQuoted
import HexRCF.RealCoefficients.RootBuild
import HexRCF.RealCoefficients.NumberFieldCells
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
example : ∃ x : ℝ,
    x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧
    (0 : ℝ) = 0 := Algebraic.Quote.source
```

The table's exact root set and strict order are proved conclusions of the
supplied replay. The positive and negative fourth roots of 2 have the same
square but different selected identities:

```lean
open Hex.RCF.RealCoefficients
open CellReplayTests
example (x : ℝ) :
    x ∈
      Algebraic.Canonical.roots.values
        Algebraic.Schema.original ↔
      x = Real.sqrt (Real.sqrt 2) ∨
      x = -Real.sqrt (Real.sqrt 2) :=
  Algebraic.Meaning.roots_eq x

example :
    (Algebraic.Canonical.roots.values
      Algebraic.Schema.original).Pairwise
      (· < ·) :=
  Algebraic.Meaning.ordered
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
example : ∃ x : ℝ,
    x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧
    0 / (-1 : ℝ) = 0 :=
  Algebraic.Guards.source
```

A supplied zero divisor is rejected before decoding, including with a malformed
packet. The fresh quotation module rechecks both original proof bodies,
requires the actual frozen readers and carrier acceptance, and excludes earlier
source witnesses. Their only axioms are `propext`, `Classical.choice` and
`Quot.sound`. Kernel reduction diagnostics separately prohibit native root,
sign and scalar production while checking replay acceptance.

The same checked rows can be reused when the entire ordered specialized
polynomial list is unchanged, including repeated and zero atoms. Changing a
comparison or Boolean connective still requires a fresh strict fold and source
quotation. The transfer preserves every stored row; it does not identify the
old and new propositions. These universal and between-root examples reuse the
same packet:

```lean
open Hex.RCF.RealCoefficients
open CellReplayTests
example : ∀ x : ℝ,
    (x ^ 2 - Real.sqrt 2 < 0 ∨
      x ^ 2 - Real.sqrt 2 ≥ 0) ∧
    (0 : ℝ) = 0 :=
  Algebraic.BooleanSources.lt_or_ge

example : ∃ x : ℝ,
    (x ^ 2 - Real.sqrt 2 ≤ 0 ∧
      x ^ 2 - Real.sqrt 2 ≠ 0) ∧
    (0 : ℝ) = 0 :=
  Algebraic.BooleanSources.negative
```

Additional fresh proofs cover equality/non-equality and positive outer
sectors. All six comparisons, conjunction, disjunction and negation are
checked, including incompatible existential and false universal verdicts.
Moving the zero atom changes the ordered polynomial list and the literal row
reader rejects the reused packet. The fresh proof-body audit excludes the
earlier source witnesses and scalar suppliers. Original divisor preflight
and original-goal authentication remain mandatory for every new quotation.

This example uses one supplied lawful ordinary-real parent and one fixed
complete packet. It establishes finite replay over a non-rational stored
coefficient. General provider history, automatic common-field certification,
all-live representation changes and complete algebraic construction retain
their separate obligations. The supplied-operation interface remains kernel
assembly: compiled evaluation can use its documented native fallback when
records are missing, so it is not a strict checker for arbitrary compiled
packets. This example installs no tactic handler or numerical provider.

The native construction API can produce the same complete packet. `RootBuild.build`
retains the owner's full derivative table and its extracted roots. For a lawful
ordinary real model, the owner theorem proves construction succeeds for every
squarefree interpreted head:

```lean
open Hex.RCF.RealCoefficients
open Hex.RealClosure
open HexPolyTheory.Interpret
example
    {r : BaseContext.Registry}
    {c : Tower.Context r}
    (model : Tower.Model c ℝ)
    (p : Hex.DensePoly c.Value)
    (sq : Squarefree
      (interpret model.value
        model.zero_iff p)) :
    ∃ result,
      RootBuild.build p = .ok result :=
  RootBuild.success model p sq
```

`CellBuild.prepare` first checks the original divisors, then specializes the
shared atoms and constructs their radical carrier and complete root table.
`prepare_success` derives progress and the literal radical check from the
ordinary parent model, without assuming squarefreeness or a root list. Zero
and repeated atoms retain their original positions in the source matrix.

`CellBuild.build` constructs every section row and every sector record for that
complete root table and proposed ordinary parent-field points. Strict adjacent
signs check each point; incorrect exterior points are refused. Original divisor
preflight comes first, and production errors retain their structured cause.
The construction conformance produces the radical, roots and all rows for
X²−√2 and verifies their exact match with the frozen packet used above. Native
construction supplies proposals; the quoted proofs continue to consume the
independently checked frozen data.

This explicit-point interface does not discover ordinary sector points in
arbitrary parents, assemble missing scalar/provider histories or prove general
frontend acceptance.
`RowEncode.read_covered` proves the shared row reader recovers an encoded checked
row from finite predecessor-codec coverage. It neither supplies that coverage
nor turns a compiled verdict into proof evidence.

The separate native `CellDiscover.run` API obtains ordinary points from the
owner's complete partition. Its actual collection converts all fixed source
coefficients and original divisors into the same common context before carrier,
root and row construction. It needs no supplied point function. The original
parent's model extends through that collection, so accepted cells prove the
shared sentence at the original coefficient values, and accepted divisor checks
establish the original guards. Those semantic results do not assume that source
and target representations are identical.

```lean
open Hex.RCF.RealCoefficients
open Hex.RealClosure
example
    {r : BaseContext.Registry}
    {c : Tower.Context r}
    {ps : List c.Poly}
    (family : Tower.Sample.Partition c ps)
    (cut : Fin (family.values.length+1)) :
    Tower.Cell.sector
      (SectorRequest.Cut.lower family cut)
      (SectorRequest.Cut.upper family cut)
        ∈ family.cells :=
  SectorRequest.Cut.adjacent family cut
```

`CellAlignment.aligned` derives exact equality between the partition's ordered
real boundaries and the independently checked radical root table. It uses the
source coefficient conversion, complete root coverage and strict ordering;
equality of the two root lists is not an extra premise. Its `dimensions` theorem
also derives the required sector count. Compilation tests construct and replay
X²−√2 with automatically selected points in an enlarged context, reject the
result in the old context, and check true/false formulas, zero atoms and literal
half-open domain guards, including equal and reversed endpoints.

This is native production followed by independent cell replay. The returned
collection retains native conversion history; it is not a frozen certificate of
that history. General frozen history, strict compiled missing-record checks and automatic
source quotation retain their separate obligations. No native verdict is a
proof of a real sentence.

`CellDiscover.run` uses `SectorRequest.points` and the owner's proved
boundary-request API. `Cut.adjacent` establishes the requested endpoints for every sector index,
including both rays and an empty table's whole line. `CellAlignment.sector_vector`
retains the request equation and transports those endpoint inequalities to the independently checked radical
table. The adapter proves this index correspondence using public cell-membership
laws and list identities; no new owner index theorem is needed.

`CellProgress` obtains each selected-sign row and each ordinary-point descriptor
from the owner's actual construction theorems. A checked linear head binds the
point row to its proposed value:

```lean
open Hex Hex.RealClosure
open Hex.RealFormula
open Hex.RCF.RealCoefficients
example
    {r : BaseContext.Registry}
    {c : Tower.Context r} {n : Nat}
    [Hashable c.Value]
    [Hashable Tower.Signature]
    (model : Tower.Model c ℝ)
    (point : c.Value)
    (values : Fin n → c.Value)
    (formula : QF (n + 1)) :
    Nonempty (PointRows.Packet
      point values formula) :=
  CellProgress.point_packet model point
    values formula
```

`CellDecision.complete` composes the actual collection, source conversion,
radical/root preparation, requested sector points and complete typed rows.
Given a lawful ordinary-real parent and nonzero original divisors, it derives
accepted typed evidence and a total diagnostic verdict for each quantifier.
The verdict is true exactly when the shared sentence holds at the original
fixed coefficient values. False verdicts remain diagnostics. The construction
requires no supplied carrier, chosen root table, sector-point function or
successful child-sign assumption. Its ordinary model remains an explicit domain
hypothesis; this does not supply faithful models for arbitrary named constants.

`CellBuild.evidence` now produces those typed rows before freezing them.
The public `CellBuild.build` serializes that same result in the existing packet
layout. `CellDiscover.run_success` proves that the actual native discovery
returns a packet: its cells equal the frozen constructed rows, and those rows
produce exact diagnostic verdicts for both quantifiers at the original fixed
coefficients. The returned vector itself is related to the indexed open cells
by `CellAlignment.sector_vector`.

```lean
open Hex.RealClosure
open Hex.RealFormula
open Hex.RCF.RealCoefficients
example
    {r : BaseContext.Registry}
    {c : Tower.Context r} {n : Nat}
    (model : Tower.Model c ℝ)
    (values : Fin n → c.Value)
    (guards : List c.Value)
    (formula : QF (n+1))
    (nonzero : ∀ d ∈ guards, d ≠ 0) :
    ∃ p,
      CellDiscover.run values guards
        formula = .ok p ∧
      let family := p.family
      let input := family.collection.input
      ∃ data : CellReplay.Evidence
          p.roots (input.value ∘ values)
          formula,
      ∃ verdict,
        CellReplay.check
          (input.value ∘ values)
          formula (guards.map input.value)
          p.radical p.roots data
          .forallReal = .ok verdict := by
  obtain ⟨p, returned, _, _, _, data,
      _, _, answers⟩ :=
    CellDiscover.run_success model
      values guards formula nonzero
  obtain ⟨verdict, accepted, _⟩ :=
    answers .forallReal
  exact ⟨p, returned, data,
    verdict, accepted⟩
```

Original fixed-field inputs can enter this producer through
`NumberField.cells`. The existing number-field factory checks the original
selected generator and supplies its ordinary-real model. Every coordinate
retains its `Coefficients.ofField` interpretation. Original zero divisors are
rejected before this factory runs, even for a constant or empty-domain matrix.
`NumberField.cellsWith` reuses a checked presentation; its progress theorem
retains the same actual vector, typed producer equation and frozen matrix as
`CellDiscover.run_success`. No caller-supplied parent model is needed:

```lean
open Hex
open Hex.RealClosure
open Hex.RealFormula
open Hex.RCF.RealCoefficients
example
    {n : Nat} (g : RealAlgebraicNumber)
    (registry : BaseContext.Registry)
    (values :
      Fin n → QAdjoin g.toAlgebraic)
    (guards :
      List (QAdjoin g.toAlgebraic))
    (formula : QF (n+1))
    (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ source p,
      NumberField.cells g registry
        values guards formula =
          .ok ⟨source,p⟩ ∧
      NumberField.cellsWith source
        values guards formula = .ok p := by
  obtain ⟨source,p,returned,_,built⟩ :=
    NumberField.cells_success g registry
      values guards formula guarded
  exact ⟨source,p,returned,built⟩
```

The native conformance constructs both selected roots of X²−2 and a computed
coordinate in the field generated by the positive root of X³−2. It produces
and reads their complete cell packets, checking both quantifier verdicts and
original zero-guard refusal. These native round trips are diagnostics; the
three generic progress/domain proof bodies receive separate ordinary-kernel
and dependency audits. They do not establish arbitrary finite-codec replay.

Literal-reader acceptance still needs finite coverage of every serialized
coefficient and context. Frozen provider/context histories, strict compiled
missing-record checking and fresh general source-goal quotation retain their
own obligations. The seven-matrix
native regression includes a four-boundary union of the algebraic equation and
half-open guards. Its retained diagnostic trace exposes a substantial cost in
cell-row production; this is a performance limitation, without a scaling or
speedup claim.
