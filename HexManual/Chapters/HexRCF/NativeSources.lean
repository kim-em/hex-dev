/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Selected coefficient identities at one real reader" =>
%%%
tag := "hex-rcf-native-source-identities"
%%%

An algebraic coefficient in a tower is not necessarily inherited from its base.
A finite reader must identify its selected real conjugate together with the
sample. {name Hex.RCF.RealCoefficients.NativeSources.true_real}`NativeSources.true_real`
adds a coefficient-selection formula in the existing shared syntax to the source
matrix. Both are realized at one reader. A proof that the selection has a unique
real coefficient valuation once inherited identities are fixed identifies the
original source coefficients. The actual provider history retains those
inherited identities at the same reader.
No `Origin.RealValue` premise is required for those algebraic suffix coordinates.

The selection is a formula on the coefficient coordinates; lifting it leaves
the quantified variable unused. Its equations, isolating inequalities and the
source matrix share one native row. This example extracts an ordinary witness
from that row and a supplied uniqueness proof:

```lean
open Hex Hex.RealClosure Hex.RCF.RealCoefficients in
example {registry : BaseContext.Registry}
    (context : Tower.Context registry)
    (following : context.origin.base.Realization)
    (values : Fin n → context.Value)
    (source : Fin n → ℝ)
    (selection : RealFormula.QF n)
    (unique : ∀ coefficients : Fin n → ℝ,
      (∀ i, context.origin.RealValue following
        (values i) (source i) →
          coefficients i = source i) →
      selection.toProp coefficients →
        coefficients = source)
    (sample : context.Value)
    (matrix : RealFormula.QF (n + 1))
    (truth : Samples.Row.eval
      (.and selection.lift matrix)
      (NativeSpecialize.row context values sample
        (.and selection.lift matrix)) = some true) :
    ∃ x : ℝ,
      matrix.toProp (RealFormula.append source x) := by
  obtain ⟨read, domain, closed, negative, fixed,
    present, sizes, meaning, guards, base⟩ :=
    NativeSources.true_real context following
      values source selection unique sample matrix
      [] (by simp) truth
  exact ⟨read sample, meaning⟩
```

The [source-identity regressions](../../../conformance/HexRCF/NativeSourcesConformance.lean)
use the actual selected positive root α of `X²−2` and a further selected root
of `X²−α`. They identify α by `α² = 2` and `1 < α < 2`, then prove
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2` through this joint reader.
The coefficient's real identity is a conclusion of the selection proof, not
an assumed inherited-base identity. Changing α to its negative conjugate at
the same upper sample changes the complete native word from
`[0, 1, -1, 0, 1, -1]` to `[0, -1, -1, 1, 1, -1]`, and the joint formula is false.
These sign words have independent ordinary-kernel proofs and compiled controls.
A second test leaves an inherited coefficient unconstrained by the selection.
Its actual origin/provider identity fixes that coordinate as 2, while the
selection fixes the first coordinate as positive √2 at the same reader.
Its matrix `x·c₀−c₁=0` uses both coordinates, and the reader exports its truth.
The concrete fixture uses non-module imports, which expose private definitions
in this toolchain; the generic library laws use module imports without `import all`.

{name Hex.RCF.RealCoefficients.NativeSources.not_forall}`NativeSources.not_forall`
uses the selection conjoined with the negated matrix for a universal
counterexample. It retains supplied nonzero guards at the same
reader. The regression refutes `∀ x, x² > α` with α authenticated as positive
√2 and retains a supplied nonzero α guard. This fixture has no source division.
A zero difference `α−α` has sign zero
and cannot satisfy the nonzero-guard premise. These are direct API controls;
they do not add automatic guard collection to this point law.

Provider history, the selection's uniqueness proof, native row truth and every
supplied nonzero guard sign remain explicit inputs. `true_real` retains source
polynomial sizes, coefficient domains and
identities, and guards at the same reader. Finite approximation intervals alone do not uniquely identify a
registered π or e; those sources require their authenticated provider identities.
This API does not construct a selection from arbitrary source syntax, read a
complete frozen context certificate, establish cell coverage, or implement
algebraic-only decision completeness. The original `rcf` frontend still needs
that assembly to consume these point laws generally.

A checked rational root descriptor can supply its own selector. The owner's
constraints include its defining polynomial, strict finite endpoint bounds and
ordered derivative signs. {name Hex.RCF.RealCoefficients.NativeSelection.selection}`NativeSelection.selection`
translates those constraints into the existing integer schema using a positive
common denominator. {name Hex.RCF.RealCoefficients.NativeSelection.identity}`identity`
reuses the descriptor's count-one proof to identify the selected root at any
coefficient coordinate. No separate root-uniqueness argument is needed:

```lean
open Hex Hex.RealClosure Hex.RCF.RealCoefficients in
example {version : Nat} (root : Root version)
    (coefficients : Fin 1 → ℝ)
    (meaning : (NativeSelection.selection 0 root.raw).toProp
      coefficients) : coefficients = fun _ => root.real :=
  NativeSelection.unique root coefficients meaning
```

{name Hex.RCF.RealCoefficients.NativeSelection.translate}`translate` also accepts
a proved zero-reflecting rational projection. The
[generated-selector regressions](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/NativeSelectionConformance.lean)
consume the actual wrapped rational predecessor's frozen √2 descriptor. Its
ordered constraints, rather than handwritten quadratic/interval atoms, identify
the source coefficient. The further-root conjunct of row truth uses the existing
`CatalogSource.source` fact. `NativeSources.true_real` then transfers that truth to one finite ordinary
reader; it does not independently discover the witness. The negative conjugate
makes the same native formula false. Invalid requested signs and unequal query/sign
lengths translate to false; no trailing constraint is silently dropped.
A second frozen rational descriptor retains both derivative signs and the
nonintegral bounds 7/5 and 3/2. Kernel proofs check its supplied graph and complete
ordered rational constraints and signs. A separate compiled control checks the
normalized integer atoms
`x²−2=0`, `2*x>0`, `2>0`, `5*x−7>0`, `2*x−3<0`.
{name Hex.RCF.RealCoefficients.NativeSelection.translate_identity}`translate_identity`
reuses the same owner uniqueness law for wrapped rational projections.

{name Hex.RCF.RealCoefficients.NativeSelection.relation}`relation` ties a
coefficient coordinate to a rational polynomial of a selected generator.
{name Hex.RCF.RealCoefficients.NativeSelection.relation_correct}`relation_correct`
proves the exact value equation after positive denominator clearing. The tests
identify `α²−1` as 1 from positive √2, and translate `c₁=c₀²/3−1/5` into exactly
`15*c₁−5*c₀²+3=0`. This uses the existing polynomial representation and arithmetic.
It does not authenticate arbitrary nested context/provider-history records,
collect source divisions, establish cell coverage, or quote a general `rcf`
proof. Concrete fixtures retain their private-import boundary; a generic
conformance module composes the public selector and finite-reader laws with
ordinary public imports in the existing CI target. Kernel inventories and compiled controls remain
separate evidence.

# Frozen selected-section replay

{name Hex.RCF.RealCoefficients.SectionBuild.build}`SectionBuild.build` searches
the native family for a true selected section and freezes its descriptor,
graph and complete ordered row. This producer currently visits selected roots;
point roots and sectors need other producers. No supported witness returns
`none`, which is not a false existential verdict. Producer failures retain the
owner's actual error.

{name Hex.RCF.RealCoefficients.SectionReplay.check}`SectionReplay.check` reads
those supplied records and checks the shared matrix. It checks all supplied
original divisors before parsing any packet. A malformed descriptor, graph or
row is rejected. A true row yields an ordinary real witness; a false row yields
only a counterexample at that section. Domain inequalities remain matrix atoms.

```lean
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet Hex.RCF.RealCoefficients
example {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    (original : Model parent ℝ)
    (codec : ValueCodec parent.Value)
    (values : Fin n → parent.Value)
    (guards : List parent.Value)
    (formula : RealFormula.QF (n+1))
    (subject graph row : Codec.Json)
    (accepted : SectionReplay.check original codec
      values guards formula subject graph row = .ok true) :
    ∃ x : ℝ, formula.toProp
      (Samples.valuation original values x) :=
  SectionReplay.check_sound original codec values guards
    formula subject graph row accepted
```

{name Hex.RCF.RealCoefficients.SectionReplay.checkWith}`checkWith` uses the
owner's eight equal supplied coefficient operations during reconstruction and
row checking. Missing stored literal facts reject decoding; missing
intermediate arithmetic facts remain explicit demands.
{name Hex.RCF.RealCoefficients.ScalarPacket.read}`ScalarPacket.read` validates
each supplied scalar graph; {name Hex.RCF.RealCoefficients.ScalarPacket.restore}`restore`
retains its checked literal key and sign without repeating graph validation
for subsequent lookups.

{name Hex.RCF.RealCoefficients.SectionQuote.finish}`SectionQuote.finish`
reifies the original target again, checks the exact existential matrix, fixed
valuation equality and every original divisor identity, then transports the
checked witness to that target. These identities are ordinary proofs. The
model and fixed coordinates must already be authenticated.

The [fresh-source regression](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/SectionProduceConformance.lean)
reifies `∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2`, produces a new native
section and row, checks seed packets for the stored predecessor coefficients,
and supplies newly reached scalar packets during kernel replay. This is independent of the existing hand-written row's truth theorem.
In particular, the source matrix contains `1-x<0`, while the older row used
`x-1>0`; the new evidence binds to the actual reified polynomial order.
The fixed positive √2 coordinate and its real interpretation use the existing
checked fixture. A [fresh compilation-unit regression](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/SectionOrdinaryConformance.lean)
quotes the source proof again with ordinary imports, audits its complete axioms
and checks that its local proof closure retains replay rather than production.
These concrete fixtures use the pinned toolchain's non-module import closure.
The generic adapter modules use public module imports.

This does not supply arbitrary source coefficient discovery, recursive provider
history restoration, all reached packing/inverse assembly, frozen complete
cell coverage, or accepted algebraic search completeness. It does not register
another `rcf` handler. Existing rational and real-coefficient tactic examples
retain their current behavior.


# Ordinary point replay

{name Hex.RCF.RealCoefficients.PointBuild.build}`PointBuild.build` proposes
ordinary parent-field points using the owner's sorted, deduplicated root
family. It visits sections and sectors with point or linear-head boundaries.
Its linear-head quotient and midpoint calculations are search proposals;
replay does not trust a region label or an identity with a selected root.
Nonlinear boundaries require further conversion certificates and are outside
this helper. Returning `none` means no supported witness was found.

{name Hex.RCF.RealCoefficients.PointReplay.check}`PointReplay.check` restores a
supplied point through a strict coefficient codec, evaluates the complete
ordered source row and folds its Boolean matrix. All original divisors are
checked before decoding. Missing recorded scalar facts reject the point;
missing arithmetic records remain explicit replay demands through
{name Hex.RCF.RealCoefficients.PointReplay.checkWith}`checkWith`.

```lean
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet Hex.RCF.RealCoefficients
example {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    (original : Model parent ℝ)
    (codec : ValueCodec parent.Value)
    (values : Fin n → parent.Value)
    (guards : List parent.Value)
    (formula : RealFormula.QF (n+1))
    (subject : Codec.Json)
    (accepted : PointReplay.check codec values guards
      formula subject = .ok true) :
    ∃ x : ℝ, formula.toProp
      (Samples.valuation original values x) :=
  PointReplay.check_sound original codec values guards
    formula subject accepted
```

{name Hex.RCF.RealCoefficients.PointQuote.finish}`PointQuote.finish` freshly
reifies the original existential goal and authenticates its exact matrix,
fixed valuation and ordered divisor identities through the shared
{name Hex.RCF.RealCoefficients.Quote.finish}`Quote.finish` boundary.
These identities are mandatory input checks. The source equivalence is
unconditional; they are checked separately from the returned proposition.
{name Hex.RCF.RealCoefficients.PointReplay.check_domains}`check_domains`
proves nonzero interpretation of every supplied guard. Failure restores the
saved state. The [source tests](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/PointProduceConformance.lean)
produce and check witnesses equal to √2, above √2, between 1 and √2, and above
√2 with `x/2<1` and `x/3<1`, a zero section and a left ray. The scalar records are independently checked from
new proposals; no old row-truth theorem is used. A separate ordinary import
module quotes the between-roots source again. These fixtures use the already
checked positive √2 parent and the pinned non-module import closure. The
public generic modules have ordinary public imports.

This point path proves individual existential successes and gives point
counterexamples to universal sentences. It does not certify a false
existential, restore general recursive provider histories, or prove complete
frozen cell coverage. It does not register another `rcf` handler.

# Frozen root-table extraction

{name Hex.RCF.RealCoefficients.RootReplay.read}`RootReplay.read` binds a supplied
graph to one parent context, polynomial and open query interval. It derives the
full derivative queries from that polynomial and checks supplied original divisors
before parsing. Graph validation checks every entry, including unreachable
ones; versions, context/domain bindings and earlier-only references remain
mandatory. A rejected graph is evidence failure, not a root-nonexistence verdict.

For positive degree, {name Hex.RCF.RealCoefficients.RootReplay.extract}`extract`
uses the owner's accepted shared table instead of replaying BKR for each root
descriptor. Every table word is retained, each descriptor has the original
head/endpoints/full derivative slots, and the finite comparator sorts the list.
The resulting domain proof establishes a nonzero squarefree head and valid
root-free open endpoints. Repeated input polynomials need the owner's squarefree
decomposition and transport; they cannot be passed unchecked to this reader.
Half-open source domains continue to be shared matrix guard atoms.

```lean
open Hex Hex.RealClosure
open Hex.RealClosure.Tower
open Hex.SignDet
open Hex.RCF.RealCoefficients
example
    {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    (original : Model parent ℝ)
    (p : DensePoly parent.Value)
    (lower upper :
      Endpoint parent.Value)
    (result :
      RootReplay.Result p lower upper) :
    HexSturmMathlib.Domain
      original.value original.zero_iff
      p lower upper :=
  result.domain original
```

{name Hex.RCF.RealCoefficients.RootReplay.Result.root_spec}`Result.root_spec`
proves that every emitted descriptor denotes a root in the original interval.
The [frozen regressions](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/RootReplayConformance.lean)
check both roots of X²−2, an interval with just its positive root, a nonzero
constant and an empty real root set. Acceptance runs under ordinary kernel
diagnostics that forbid native root production and per-descriptor replay.
Changed polynomials/domains/contexts, missing support, cyclic graphs and stale
versions are evidence errors; a zero original guard is a divisor error even
with a zero polynomial and malformed graph.
The predecessor codec and arithmetic remain part of the surrounding assembly;
frozen quotation must supply their checked finite facts and reject native
coefficient production. These fixtures use the rational base, not general
nested arithmetic quotation.
A [fresh module](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/RootReplayOrdinaryConformance.lean)
uses an emitted descriptor and checked domain to prove
`∃ x : ℝ, x²=2 ∧ 1<x ∧ x<2` and a negative conjugate
`∃ x : ℝ, x²=2 ∧ x<0`, both with the standard three axioms.
The negative proof consumes the actual checked derivative word at that root.
These concrete proofs retain the pinned non-module import closure.

This is finite extraction and emitted-root soundness. Complete root coverage,
interpreted-value deduplication and strict mathematical ordering require the
owner's supplied-replay semantic exports. The native producer's coverage
equation is not a frozen certificate premise. This reader does not provide
complete cell replay or another tactic handler.

## Checked predecessor operations

{name Hex.RCF.RealCoefficients.RootReplay.readWith}`RootReplay.readWith` uses
five supplied operations during graph replay and full derivative extraction.
Each operation has an ordinary proof that it equals the parent's canonical
operation. {name Hex.RCF.RealCoefficients.RootTable.changeOps}`RootTable.changeOps`
uses the owner's descriptor transport, retaining literal data and changing
only proof indices. The accepted tree and extraction equation remain available
to the existing domain and emitted-root laws.

```lean
open Hex Hex.RealClosure
open Hex.RealClosure.Tower
open Hex.SignDet
open Hex.RCF.RealCoefficients
example
    {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    (codec : ValueCodec parent.Value)
    (guards : List parent.Value)
    (p : DensePoly parent.Value)
    (lower upper :
      Endpoint parent.Value)
    (graph : Codec.Json) :
    RootReplay.readWith codec guards p
      lower upper
      (Tower.instOneValue parent)
      (Tower.instAddValue parent)
      (Tower.instSubValue parent)
      (Tower.instMulValue parent)
      (Tower.instNatCastValue parent)
      rfl rfl rfl rfl rfl graph =
    RootReplay.read codec guards p
      lower upper graph :=
  RootReplay.readWith_eq _ _ _ _ _
    _ _ _ _ _ rfl rfl rfl rfl rfl _
```

The [nested full-table regression](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/NestedRootProduceConformance.lean)
checks X²−√2 in (1,2) over the already authenticated positive √2 parent.
Five new scalar seed packets and three reached packets are independently
checked and shared. No old row facts or row-truth theorem supply acceptance.
The output cardinality is also checked with native producers forbidden. The
result proves `∃ x : ℝ, x²=√2 ∧ 1<x ∧ x<2` through the actual domain/root
interpretation and coefficient identities. A
[fresh import module](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/NestedRootOrdinaryConformance.lean)
audits the same target and its complete standard three-axiom inventory.
Local body markers consume replay laws; imported declarations remain leaves.

Input construction matters: a closed `1` or negation must use the checked
supplied operation too. Canonical closed constructors can reach native sign
production, which
the kernel guard rejects; acceptance requires checked finite operations.
Missing scalar literals, a same-degree changed head and a changed endpoint
reject as evidence errors. With zero record-collection budget,
the existing quotation collector returns a missing-record result without
running scalar production. This budget concerns quotation assembly, not a
new fallible arithmetic interface.

This is a fixed-parent nested replay example. Recursive context/provider-history
authentication, complete root/cell coverage, all-live transport and general
source quotation still need the owning implementations and exports.

# Frozen selected-root transport

{name Hex.RCF.RealCoefficients.RootTransport.read}`RootTransport.read` checks a
supplied descriptor after coefficient conversion. It preflights supplied source
divisors and matches the context, polynomial, endpoints and derivative word
against the actual map. A valid descriptor for a different root yields `binding`;
invalid or incomplete evidence yields `evidence`. A zero source divisor yields
`divisor` before parsing. The frontend authenticates this guard list against the
original source; this reader does not infer it from a goal.

{name Hex.RCF.RealCoefficients.RootTransport.readWith}`readWith` accepts equal
supplied maps and arithmetic dictionaries. Its result has canonical proof
indices, and `readWith_eq` preserves every result and error. The coefficient
codec must independently restore its finite checked records.

An accepted descriptor gives the next actual context conversion through `step`.
{name Hex.RCF.RealCoefficients.RootTransport.model}`model` consumes the owner's
`Conversion.Model.adjoinWith` law and preserves every old-context value:

```lean
open Hex in
open Hex.RealClosure in
open Hex.RealClosure.Tower in
open Hex.RCF.RealCoefficients in
example {registry :
    BaseContext.Registry}
    {source : Context registry}
    (c : Conversion source)
    (r : SignDet.Descriptor source.Value
      Tower.Signature
      source.sign source.signature)
    (k : RootTransport.Checked c r)
    (m : Model source ℝ)
    (hm : Conversion.Model c m)
    (a :
      (source.adjoin r).context.Value) :
    (RootTransport.model hm r
      k.converted k.binding).target.value
        ((RootTransport.step c r
          k.converted k.binding).value a) =
      (m.adjoin r).value a :=
  (RootTransport.model hm r
    k.converted k.binding).value a
```

No native root-isolation success premise is used. Later scalar packing and
quotation still need their own finite checked assembly. The fixed-parent
regression moves the positive root of X²−2 into an authenticated positive-√2
context using three proved constant-sign records. The converted root still
denotes `Real.sqrt 2`; a separately valid negative-root certificate rejects
with `binding`. Missing records and a stale context yield `evidence`.

This checks one conversion step. Recursive provider/context history,
all-live assembly and complete cell replay remain separate requirements.

The target context retains the supplied descriptor’s evidence. Equivalent roots
with different evidence need not have equal context signatures. `step_native`
agrees with `adjoinChecked` only if native production returns this exact
descriptor; frozen acceptance does not use that premise. Retain the accepted
reader equation when applying `read_domains`, because the returned descriptor
alone does not remember or authenticate a frontend guard list.
