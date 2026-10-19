/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRCF.CellReplay.Algebraic.BooleanQuoted
import HexRCF.CellReplay.Algebraic.CompleteQuoted
import HexRCF.RealCoefficients.RootBuild
import HexRCF.RealCoefficients.NumberFieldCells
import HexRCF.RealCoefficients.GatherCells
import HexRCF.RealCoefficients.AlgebraicCells
import HexRCF.RealCoefficients.AlgebraicPreparation
import HexRCF.RealCoefficients.CellOperations
import HexRCF.RealCoefficients.RealModel
import HexRCF.RealCoefficients.SourceIdentity
import HexRCF.RealCoefficients.SourceBuild
import HexRCF.RealCoefficients.CellQuote
import HexRCF.CellQuoteStages
import HexRCF.CellSourceQuote
import HexRCF.SourceIdentityPacket
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

The complete-packet interface reads the full root table before its cell rows.
`CompleteReplay.check` then checks the radical identities and strict quantifier
fold. Its soundness theorem accepts untrusted root and cell packets and proves
the shared sentence at the supplied fixed real interpretation:

```lean
open Hex Hex.RealClosure Hex.SignDet
open Hex.RealFormula
open Hex.RCF.RealCoefficients
example
    {r : BaseContext.Registry}
    {c : Tower.Context r} {n : Nat}
    (model : Tower.Model c ℝ)
    (codec : ValueCodec c.Value)
    (values : Fin n → c.Value)
    (formula : QF (n + 1))
    (guards : List c.Value)
    (cert : RadicalCert c.Value
      Tower.Signature)
    (quantifier : Quantifier)
    (roots cells : Codec.Json)
    (accepted : CompleteReplay.check
      codec values formula guards
      cert quantifier roots cells =
        .ok true) :
    (Prenex.quant quantifier
      (.matrix formula)).toProp
        (fun i =>
          model.value (values i)) :=
  CompleteReplay.check_sound
    model codec values formula
    guards cert quantifier
    roots cells accepted
```

`CellQuote.finishPacket` additionally binds this checked shared sentence to a
freshly reified original source, its fixed coefficient valuation and all ordered
original divisors. These fresh source proofs use the same algebraic matrix,
including a divisor whose value disappears from the normalized zero atom:

```lean
open Hex.RCF.RealCoefficients
open CellReplayTests.Algebraic
example : ∃ x : ℝ,
    x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧
    0 / (-1 : ℝ) = 0 := by
  exact CompleteQuote.guarded_source
```

The source-boundary checks refuse a false verdict, a different original
formula, missing divisor identities and a cancelled zero divisor. A separate
`CompleteReplay.check_domains` theorem proves every original guard nonzero in
the supplied model. The new source proofs reuse the independently checked
frozen fixture and finite codec laws. They do not claim a fresh reduction of
the serialized readers. The supplied real model and coefficient codec also do
not reconstruct general frozen provider or predecessor histories. In
particular, the compiled supplied-operation fallback described below still
prevents treating this as strict replay with arbitrary missing records.

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

The discovery result emits its full `rootGraph` as well as `cells`.
`Packet.rootGraph_eq` binds the graph to the actual typed root table and native
writer. `CellDiscover.run_complete` proves that independently checking both
emitted fields preserves both quantifier verdicts at the original coefficient
values. It uses the returned native context's codec law; it does not restore
an arbitrary frozen predecessor history.

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
`CellDiscover.run_success`. `cellsWith_complete` further checks both emitted
root/cell fields; `cells_complete` composes that acceptance with the actual
presentation factory. Both verdicts retain the original selected-coordinate
interpretation. No caller-supplied parent model is needed:

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
        values guards formula =
          .ok p := by
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
own obligations. A separate manually run stress target checks a four-boundary
union of the algebraic equation and half-open guards. Its retained diagnostic trace exposes a substantial cost in
cell-row production; this is a performance limitation, without a scaling or
speedup claim.

Independently constructed coefficient contexts can enter complete packet
production through `GatherCells.build`. Each input retains its original owner;
several coefficients can share an owner, and a guard can be absent from the
coefficient tuple. The coefficient order, guard order and schema arity remain
independent. A zero original guard is rejected before gathering, including
for a constant matrix with no coefficient parameters.

`buildWith` reuses the actual owner's gathering result. A compatible ordinary
model proves complete packet production without assuming a successful child
producer or choosing a new primitive common field:

```lean
open Hex Hex.RealClosure
open Hex.RealClosure.Tower
open Hex.RealFormula
open Hex.RCF.RealCoefficients
example
    {r : BaseContext.Registry}
    {b : BaseContext.PackedContext r}
    {os : List (Context r)} {n : Nat}
    (shared : Shared b os)
    (target : Model
      shared.input.context ℝ)
    (models : Inclusions.Models
      target shared.maps)
    (cs : Fin n →
      GatherCells.Source os)
    (gs : List (GatherCells.Source os))
    (f : QF (n+1))
    (nonzero : ∀ g ∈ gs, g.2 ≠ 0) :
    ∃ p, GatherCells.buildWith
      shared cs gs f = .ok p := by
  obtain ⟨p,built,_⟩ :=
    GatherCells.buildWith_complete
      shared target models cs gs f
      nonzero
  exact ⟨p,built⟩
```

`build_complete` additionally derives successful gathering from the original
owners' compatible base signatures and an ordinary base interpretation. Both
quantifier verdicts are proved equivalent to the shared sentence at the
original owner values. `build_domains` establishes every original typed guard
nonzero from successful production. These are native-context results: they
supply neither source-expression identities nor frozen provider/predecessor
histories, and do not discharge strict compiled missing-record admission.

The native conformance combines separate positive √2 and √3 owners, repeats
one source coordinate, and checks a leading cancellation and repeated zero root.
It reads both emitted packets, refuses swapped coefficient
coordinates, and checks a false constant with no coefficient parameters but
retained guards. A late original zero guard still rejects that constant case.
Compiled verdicts remain controls; the generic construction and transport
laws are separate ordinary-kernel proofs.

`AlgebraicCells.build` starts from original `RealAlgebraicNumber` inputs.
It constructs their checked selected presentations and gathers the resulting
owners automatically. Separate finite indices specify the coefficient tuple
and the original guards; repeated indices and guard-only inputs are retained.
An original zero guard rejects before any presentation construction.
Recognized rational inputs use checked points in the rational predecessor,
including guard-only inputs. This avoids adjoining a root of a linear
polynomial just to represent a rational. Other inputs retain the owner's
selected-root factory and its check of the original embedding.
Every declared input is presented and gathered, even when absent from both
index collections. An unused irrational input can enlarge the tower, so a
focused input tuple avoids that additional cost.

The automatic constructor needs only the original nonzero guards for its
progress theorem. The rational interpretation, owner compatibility and
selected coordinate identities are derived:

```lean
open Hex Hex.RealClosure
open Hex.RealFormula
open Hex.RCF.RealCoefficients
example (r : BaseContext.Registry)
    {m n : Nat}
    (vs : Fin m →
      RealAlgebraicNumber)
    (cs : Fin n → Fin m)
    (gs : List (Fin m))
    (f : QF (n+1))
    (nonzero : ∀ i ∈ gs, vs i ≠ 0) :
    ∃ s p,
      AlgebraicCells.build
        r vs cs gs f = .ok ⟨s,p⟩ := by
  obtain ⟨s,shared,packet,built,_⟩ :=
    AlgebraicCells.build_complete
      r vs cs gs f nonzero
  exact ⟨s,⟨shared,packet⟩,built⟩
```

These native-input theorems preserve both emitted quantifier verdicts at the
original selected real values. `build_domains` concludes every original real
divisor nonzero from production success, including for constant formulas.
`build_sound` derives both accepted verdicts from the exact successful build
equation, without assuming guard validity; `GatherCells.build_sound` also derives
compatible owner origins from successful gathering. They do not assemble
frozen provider/predecessor histories or prove general source-goal quotation
and strict compiled missing-record admission.

The complete literal checker can use checked cached arithmetic through
`CellOperations.check`. It takes the owner's existing `Replay.Operations`
dictionary, whose equalities bind every supplied operation to the ordinary
implementation. Root and cut indices remain canonical while section and
sector evidence is read. The result preserves every error and both verdicts:

```lean
open Hex Hex.RealClosure Hex.SignDet
open Hex.RealFormula
open Hex.RCF.RealCoefficients
open Hex.RealClosure.Replay
example {r : BaseContext.Registry}
    {p : Tower.Context r}
    (o : Operations p.sign)
    (v : ValueCodec p.Value)
    {n : Nat} (vs : Fin n → p.Value)
    (f : QF (n+1))
    (gs : List p.Value)
    (c : RadicalCert p.Value
      Tower.Signature)
    (q : Quantifier)
    (graph cells : Codec.Json) :
    CellOperations.check o v vs f gs c q
      graph cells =
      CompleteReplay.check v vs f gs c q
        graph cells :=
  CellOperations.check_eq o v vs f gs c q
    graph cells
```

Original guard preflight, radical identities, complete root/cell coverage and
the strict fold retain their existing soundness and domain theorems.
`CellOperations.accept?` supplies the optional success predicate consumed by
record assembly; only an accepted true verdict yields success. The public
checker retains its typed failures and diagnostic false result. These
interfaces do not authenticate source coefficients, construct general frozen
histories or establish strict compiled rejection of missing intermediate
arithmetic records. The compiled controls and ordinary proofs are separate;
one source regression reuses independently checked fixture acceptance and finite
codec laws as a transport check. A separate assembled-source regression collects
actual reached records, checks complete literal packet acceptance in the ordinary
kernel, and quotes the original statement ∃ x, x² - √2 ≥ 0 ∧ x² - √2 ≤ 0 ∧ 0 = 0.
Its fresh consuming module derives ∃ x, x² = √2 and audits the actual proof
bodies with only the standard three axioms, excluding the older fixture
acceptance and source theorems. This uses a fixed retained field and finite
coefficient codec; it does not reconstruct arbitrary frozen histories.

{name Hex.RCF.RealCoefficients.CellQuote.replayWith}`CellQuote.replayWith`
quotes a supplied `CellOperations.check` expression in three stages. It first
checks the complete root table, then each dependent section and sector record,
then the strict Boolean and quantifier fold. Checked data definitions retain
the exact root and cell indices between stages. Pointwise reader equations
compose through `CellRead.collectWith_eq` and `CellOperations.readCells_of_parts`;
quotation does not normalize the complete finite collector as one expression.
{name Hex.RCF.RealCoefficients.CellOperations.check_of_parts}`CellOperations.check_of_parts`
composes their equations at the original packet. All three stages and their
decoder callbacks consume one reflection budget:

```lean
open Lean Hex.RealFormula
open Hex.Reflect
open Hex.RCF.RealCoefficients
meta def quoteCellPacket
    (program : Expr)
    (decode : RootQuote.DecoderM)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  RootQuote.runWith
    (CellQuote.replayWith
      program decode)
    config used
```

`set_option trace.Hex.RCF.CellQuote true` reports reader and finite-family
boundaries with cumulative proof-node usage. Lean heartbeats remain a separate
elaboration limit.

{name Hex.RCF.RealCoefficients.CellQuote.finishPacketWith}`CellQuote.finishPacketWith`
continues this request through the original source proof. It consumes the
prepared source and the accepted canonical checker, model, coefficient identity
and ordered divisor identities. The source record is checked again: its original
target, divisor inventory and ordinary-kernel equivalence must match. This avoids
starting another reification budget. Invoke quotation and finishing inside the
same `RootQuote.runWith` transaction, seeded with source preparation's usage;
the final usage then includes both stages. A finishing failure restores the
whole attempt, including declarations produced while quoting the packet.

The separate finishing action can also continue already recorded usage:

```lean
open Lean Hex.RealFormula
open Hex.Reflect
open Hex.RCF.RealCoefficients
meta def finishCellPacket
    (source : Reify.Source)
    (target checker accepted : Expr)
    (model identity : Expr)
    (guards : Array Expr)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  RootQuote.runWith
    (CellQuote.finishPacketWith source
      target checker accepted model
      identity guards)
    config used
```

That separate transaction rolls back its own work. Clients needing rollback
of quotation as well must combine both actions in one transaction. Conformance
checks exact and one-node-below cumulative limits, exhaustion of the continued
source budget, tampered source records and wrong goal proofs.

Within this request, row quotation parses each literal sign packet and checks
its exact ordered queries. It validates a graph once for each distinct set of
arithmetic operations, sign function, context, polynomial, endpoints and graph
data. The owner's `SelectedSigns.ofMemo?` extracts each root's row from that
checked graph; `Dag.selectedSigns_memo` identifies it with the original reader.
Every reused equation is kernel checked against the new reader. The cache is
local to one quotation attempt, and every visit consumes the shared budget.
`set_option trace.Hex.RCF.RowQuote true` reports validations and reuse. Supplied
arithmetic operations remain attached to the descriptor, including operations
that are proved equal to canonical arithmetic rather than definitionally equal.

The returned equation retains both Boolean verdicts. `CellQuote.finishPacket`
performs source authentication separately and requires an accepted true result.
The constant example uses independently read literal root and cell packets:

```lean
example : ∀ _x : ℝ, (0 : ℝ) = 0 :=
  Hex.RCF.CellQuoteStages.source
```

Its replay quotation uses 441,039 nodes for true and 441,041 for false. These
counts cover the three replay stages, separately from source reification and
interpretation. Exact and one-node-below limits, wrong-goal proposals,
malformed cells, original zero-divisor preflight, terminal callback failures
and full caller-state restoration are checked.

A separate rational quadratic packet checks two root sections and three
sectors in 5,911,125 proof nodes. Its trace records two graph-memo reuses and
seven independent validations. These are charged quotation counts, rather
than a timing comparison or a measurement of physical sharing. The test supplies
16M proof nodes and a separate 24M heartbeat allowance. Compiled replay and
general algebraic quotation costs need separate evidence.

A fresh importing audit checks 1,247 theorem bodies and 101 definitions, with
1,298 nonempty kernel traces, the unchanged producer guard and only the
standard three axioms. It excludes older fixture acceptance proofs. The
constant example establishes source quotation; the quadratic packet adds
replay coverage with multiple roots. General coefficient and history assembly
remain separate obligations.

The algebraic source regression independently reads the complete frozen packet
over the retained positive square root of 2. It reifies the following original
sentence, authenticates its fixed coefficient from the descriptor and two
scalar packets inside the same request, reconstructs the coefficient polynomial
and composes the checked cell verdict with the original source:

```lean
example : ∃ x : ℝ,
    x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧
    (0 : ℝ) = 0 :=
  Hex.RCF.CellSourceQuote.source
```

The shared reification and quotation budget records 9,330,067 proof nodes
before source finishing and 9,337,314 for the complete original-source attempt.
Source authentication, cell replay and finishing run in one transaction. The test supplies 24M proof nodes and
60M heartbeats. Its trace records two memo reuses and seven validations.
Lake reports 821 seconds for this source module on the recorded shared host;
this remains an expensive fixed-input proof build. These observations do not
measure compiled replay or establish a general tactic running time.

Its importing proof audit checks 1,191 theorem bodies, 202 definitions and
1,351 nonempty kernel traces. It excludes the older complete-packet acceptance
and source proofs, the handwritten coefficient identity and the separately
proved source-selection/coefficient identities. It checks transitive
axiom dependencies, and rejects native
producer and canonical-codec reduction. The fixed
selected parent, original alias/coefficient-map laws and checked arithmetic
seed facts are supplied inputs. This example does not construct arbitrary
predecessor histories or install a
general source-to-certificate tactic backend.

For a closed retained base/root context, `RealModel.build` constructs its
ordinary-real interpretation from a caller-supplied real base model and each
root's actual descriptor, frame and encoding proof. It checks every prefix's
context, rejects a mismatched base model or exhausted depth bound, and restores
elaborator state on failure. This interpretation still needs checked identities
connecting its coefficient and divisor values to the original source statement.

A source equation alone does not distinguish real conjugates.
{name Hex.RCF.RealCoefficients.SourceIdentity.observe}`SourceIdentity.observe`
reads a checked scalar sign at the native descriptor's selected root and binds
every polynomial coefficient to its rational source query.
{name Hex.RCF.RealCoefficients.SourceIdentity.margin}`SourceIdentity.margin`
expresses membership in the source's isolating disc as a positive rational
polynomial value. The equation and margin must hold at the same root;
{name Hex.RCF.RealCoefficients.SourceIdentity.select}`SourceIdentity.select`
then identifies that value with the source's selected embedding. The
[checked source-identity example](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/SourceIdentityCases.lean)
uses independently replayed equation and margin packets for the retained √2
coordinate, with a separate ordinary-kernel body audit. These are source
interpretation lemmas and a fixed-input example; general frozen source-history
reconstruction still needs its own checked assembly.

{name Hex.RCF.RealCoefficients.SourceIdentity.quoteWith}`SourceIdentity.quoteWith`
constructs this identity from two supplied scalar readers. Its `Anchor` retains
the original polynomial, isolating square, witness, precision and selected-value
proof. Its `Packets` supplies the equation and enclosure readers and proofs
binding their polynomial keys to the intended real polynomials. The readers
carry the ordinary-real model. Both facts must belong to the same selected
context: one sign is zero and the square margin is strictly positive.

```lean
open Lean Hex.RealFormula
open Hex.Reflect
open Hex.RCF.RealCoefficients
meta def quoteSourceIdentity
    (anchor : SourceIdentity.Anchor)
    (packets : SourceIdentity.Packets)
    (context same : Expr)
    (decode : RootQuote.DecoderM)
    (config : Reify.Config)
    (used : BudgetUsage) :=
  RootQuote.runWith (do
    let selected ←
      SourceIdentity.quoteWith
        anchor packets context same
        decode
    pure ⟨anchor.value, selected.proof,
      selected.usage⟩)
    config used
```

The result proves that the reader's selected real root equals the original
anchor value. Quotation checks both packets, their keys, signs, supplied value
laws and the final original-source equality. The caller supplies the prepared
context and its checked equality. All work shares the enclosing reflection
budget and transaction. This authenticates a supplied selected source; it does
not construct an arbitrary predecessor history or run missing root/sign searches.

The frozen square-root regression quotes its parent descriptor and both
packets in 673,461 proof nodes. Its coefficient identity supplies the complete
algebraic source example above. A separate negative-window packet has an
accepted literal reader and sign −1; it cannot identify the positive native
root with the negative selected conjugate. Wrong coefficient proofs and
one-node-below exhaustion also restore the complete caller state. The dedicated
fresh audit checks 218 theorem bodies, 179 definitions and 385 nonempty kernel
traces, excludes the handwritten source identities and native fact fixtures,
and retains the producer guard and complete standard-three axiom closure.

The native producer {name Hex.RCF.RealCoefficients.SourceBuild.build}`SourceBuild.build`
can discover a selected source from its defining polynomial and a window
polynomial whose sign is positive at exactly one of its real roots. For an
isolating square, use `SourceIdentity.margin` as that window. The producer
enumerates roots with the existing family algorithm, visits every candidate,
and proposes the equation and window packets for the unique positive match.
Two matches produce `ambiguous`; no match produces `unselected`. A failed
equation or enclosure calculation remains an error.

This direct API example proposes the positive root of X²−2, using its checked
source square:

```lean
open Hex Hex.RealClosure
open Hex.RCF.RealCoefficients

def proposeSquareRoot
    (registry :
      BaseContext.Registry) :=
  Id.run do
    let parent :=
      RealClosure.NumberField.base
        registry
    let polynomial : parent.Poly :=
      DensePoly.ofCoeffs
        #[⟨-2⟩, ⟨0⟩, ⟨1⟩]
    let margin :=
      SourceIdentity.margin
        SquareTwo.square
    let window : parent.Poly :=
      DensePoly.ofCoeffs
        (margin.coeffs.map
          fun coefficient => ⟨coefficient⟩)
    return SourceBuild.build
      polynomial window

#eval
  let proposal :=
    proposeSquareRoot
      (fun _ => none)
  proposal.toOption.isSome
```

The output reports proposal production. Independent frozen replay establishes
the selected real identity. `ScalarPacket.buildParts` retains the proposed
polynomial, sign and graph separately; its `packet` method preserves the
existing three-field scalar format. `SourceIdentity.quoteWith` checks those
fields at the exact restored descriptor and original source alias.

`ScalarPacket.buildParts_success` and `build_success` prove actual packet
production for every query at a validated descriptor with a lawful ordinary-real
parent model. They consume the owner's selected-sign production theorem,
without assuming a successful table or producer result. Acceptance of the
frozen serialized packet remains a separate obligation.

The [enumerated-source controls](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/SourceBuild.lean)
produce both quadratic conjugates and a positive cubic root from X³−2, compare
their complete bytes with frozen constructor literals, and independently
validate all six scalar graphs. They also reject an ambiguous window, empty
and zero windows, a wrong source equation and duplicate roots. The separate
[ordinary quotation](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/EnumeratedSource/Quote.lean)
identifies these roots from the frozen descriptors and packets, with the
rational model, alias selection and coefficient-map laws supplied. Its three
quotation requests charge 6,371,355, 6,442,217 and 8,127,841 proof nodes
respectively; the separate final driver checks and exports are outside those
counts. The combined build
took 624 seconds and peaked at 2.2 GiB on the shared host. These costs describe
three fixed proof constructions. General predecessor-history assembly and
automatic source discovery from a tactic goal remain separate work.

When a source already supplies an isolating square, a bounded proposal avoids
constructing all real roots and their derivative words. The existing
{name Hex.RCF.RealCoefficients.SourceBuild.buildOn}`SourceBuild.buildOn`
checks an open interval with root-free endpoints and exactly one root, then
still produces the equation and original square-margin packets. It rejects
invalid endpoints, absent or ambiguous roots; it does not retry enumeration.
For this rational source, twice the square's half-width supplies candidate
endpoints. The checked count and subsequent source identity establish their
meaning; the producer assumes no unchecked interval-isolation claim.

```lean
def proposeBoundedRoot
    (registry :
      BaseContext.Registry) :=
  Id.run do
    let parent :=
      RealClosure.NumberField.base
        registry
    let square := SquareTwo.square
    let embed (x : Rat) :
        parent.Value := ⟨x⟩
    let polynomial :=
      DensePoly.ofCoeffs
        #[embed (-2), embed 0, embed 1]
    let margin :=
      SourceIdentity.margin square
    let window :=
      DensePoly.ofCoeffs
        (margin.coeffs.map embed)
    let center := square.re.toRat
    let radius :=
      2 * square.halfWidth.toRat
    return SourceBuild.buildOn
      polynomial window
      (.finite (embed (center-radius)))
      (.finite (embed (center+radius)))

#eval
  let proposal :=
    proposeBoundedRoot
      (fun _ => none)
  proposal.toOption.isSome
```

The [bounded-source controls](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/BoundedSource.lean)
produce both quadratic conjugates and the cubic source, retaining 25,477
canonical bytes. Separate ordinary-kernel quotation authenticates their
original identities at 687,781, 690,200 and 731,070 charged proof nodes,
respectively, with the unchanged one-million-node default. Final driver checks
and exports are outside these counts. The first default-budget quotation
module built in 49 seconds. The combined native/proof/fresh-audit build took
83 seconds and peaked at 1.9 GiB. These fixed observations are not a matched
timing comparison. The source alias, rational model and coefficient-map laws are
still supplied. Bounded proposals do not discover a general predecessor
history, prove complete cell coverage or complete the tactic's algebraic
decision procedure.

`CellQuote.finishOperations` takes the supplied-operation acceptance expression
and an ordinary proof that its result is `some ()`. It kernel-checks that exact
equation, transports it to the canonical checker, and performs the original
source, valuation and divisor checks of `CellQuote.finishPacket`. A reduced
conversion proof can retain its original expected equation through this API.
Failure restores both metavariables and auxiliary proof declarations.

Meta clients can prepare these native inputs from the original Lean statement
with `AlgebraicPreparation.prepare`. It reuses the shared source translator and
the checked algebraic interpretation of each coefficient and original divisor.
Its default proof callback, `FieldRuntime.nonnegative`, attempts routine
nonnegativity facts and restores its state on decline. A caller can supply
another callback returning an ordinary proof or `none`; thrown exceptions
remain terminal. Preparation checks each supplied proof and retains one
aggregate reflection budget across the source, coefficients and divisors.
The source equivalence is charged during reification and again when retained
as a private theorem for later composition:

```lean
open Lean Meta Qq
open Hex.RCF.RealCoefficients
run_meta do
  let .ok prepared ←
      AlgebraicPreparation.prepare
        q(∀ x : ℝ,
          x^2 + 1 /
            (Real.sqrt 2 + 1) > 0)
    | throwError "unsupported source"
  let guards := prepared.source.divisors
  unless guards.size == 1 do
    throwError "missing original guard"
```

The resulting environment stores coefficient proposals first and every original
divisor afterward, with separate ordered indices for each role. Its `build`
method runs `AlgebraicCells.build` on those proposals. It does not first require
a primitive common-field irreducibility certificate. The source identities are
ordinary-kernel proofs about the retained algebraic expressions; they do not
authenticate quoted literals for the computed proposals. This preparation API
does not install a new `rcf` handler or close the remaining frozen-context,
literal-authentication and general source-quotation obligations.

For the retained algebraic expressions, `prepared.acceptanceIff` proves an exact
acceptance equivalence. The left side requires the actual algebraic producer
to return a complete packet and that packet's checker to accept `true`. The
right side contains both the original real statement and every original
divisor's nonzero condition. Guard validity is a conclusion of acceptance,
even when cancellation or an empty interval makes the statement trivial.
The helper reconstructs the ordered original guard inventory from the target;
editing both stored guard arrays cannot remove or replace an obligation.
The existing producer completeness and domain laws prove this equivalence;
no successful child calculation is assumed.

```lean
open Hex Lean Meta Qq
open Hex.RCF.RealCoefficients
open Hex.RealClosure.BaseContext
run_meta do
  let target : Q(Prop) :=
    q(∀ x : ℝ, x^2 + Real.sqrt 2 > 0)
  let .ok prepared ←
      AlgebraicPreparation.prepare
        target
    | throwError "unsupported source"
  let before := prepared.usage
  let registry : Q(Registry) :=
    q(fun _ => none)
  let .ok (equivalence, usage) ←
      prepared.acceptanceIff
        target registry
    | throwError
        "source equivalence failed"
  let auxName := mkPrivateName
    (← getEnv)
    (← mkFreshUserName `sourceDoc)
  let _ ←
    withDeclNameForAuxNaming
      auxName do
        Hex.RCF.checkProof
          `sourceAcceptance
          (← inferType equivalence)
          equivalence
  unless usage.proofNodes >
      before.proofNodes do
    throwError
      "proof usage did not increase"
```

This proof uses the checked algebraic expressions and their source identities.
It does not identify separately computed proposals with frozen literals,
reconstruct provider histories, or add a tactic handler. Those authentication
and quotation obligations remain separate. The helper continues the same
aggregate reflection budget, returns its updated usage for later stages, and
restores caller state on exhaustion or failure.
Callers continue with `{prepared with usage}` when constructing further proofs.
Both preparation and acceptance preserve a caller's lowered recursion limit.
Fresh importing regressions check its actual theorem bodies, true and false
sources, retained zero guards and reversed intervals, with exactly the standard
three axioms.

The automatic-input conformance uses both selected signs of √2 alongside an
independent positive √3. It checks simultaneous conditions and a repeated zero
root, both true and false quantified verdicts, an unused zero input, a late
original zero guard, and empty true/false constant inputs. Separate linear
constraints a < x < 1 distinguish the variable's selected coefficient: a = −√2
gives an existential true and universal false verdict; a = √2 gives both false.
Thirteen actual automatic-input proof bodies are separately checked with only
the standard three axioms.

The explicit `HexRCFAlgebraicCellsStress` target retains the stronger condition
x² = √2 with 1 < x < √3 and its negative-conjugate control. A recorded
run was interrupted after 12 min 33 s at 1.4 GiB peak without a final module
result; this is neither a completed timing nor an acceptance result. Stack
samples show nested native inversion, gcd and Sturm sign work below an IR
interpreter call chain, without identifying a particular case or phase. The cost remains a limitation of this
complete native route.
