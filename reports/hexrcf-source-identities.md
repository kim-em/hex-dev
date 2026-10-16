# Checked identities for selected source coefficients

A polynomial equation does not identify a real conjugate. A source coefficient
also carries a selected embedding. The optional adapter's
[SourceIdentity](../adapters/HexRCF/RealCoefficients/SourceIdentity.lean) composes
existing native scalar-sign correspondence with the source polynomial and its
isolating square. It uses the existing `DensePoly`, native contexts, ordinary
real models and selected-root uniqueness theorem.

`observe` reads an actual `Algebraic.SignFact` at its original selected root.
Its polynomial must equal the requested stored polynomial, and its interpreted
coefficients must equal the rational source query. `margin` constructs the
rational polynomial

```text
2 w² − b² − a² + 2 a X − X²
```

for a square with real centre coordinate `a`, imaginary coordinate `b` and
half-width `w`. Its positive sign proves strict membership in the square's
circumscribed disc on the real axis. `select` combines that margin with the
source equation and the actual count-one square witness to identify the
source's selected real value. Both observations concern the same value.
Ordinary polynomial transport continues to use the existing operation-only
map/evaluation and model sign laws.

The two selection helpers exposed by
[CommonPresentation](../adapters/HexRCF/RealCoefficients/CommonPresentation.lean)
retain their existing proofs. No decoder, arithmetic implementation, formula
syntax or root-isolation algorithm is copied into this module.

The [source regression](../conformance/HexRCF/SourceIdentityCases.lean)
constructs actual native assembly from the retained selected-root context and
independently checks scalar packets for the source equation and disc margin.
It proves that the retained coefficient denotes `Real.sqrt 2`. The
[fresh consumer](../conformance/HexRCF/SourceIdentityKernel.lean) checks actual
theorem bodies, the exact three-axiom closure and required selection/scalar
bridges. The closure of `source_selected` excludes `Data.selectedFacts`,
`Data.definingPoly`, `Data.lowerData` and both older alias theorems
`Data.alpha_value` and `Data.selectedSqrt`. The final coordinate's representation
still carries its original sign proof, whose closure contains earlier root
facts. Its equality uses the new source-selection proof and excludes the two
alias theorems; it does not claim that its entire type/data closure is free of
those earlier root facts. Native production supplies data; ordinary-kernel
replay supplies the proof.

The [complete-cell source consumer](../conformance/HexRCF/CellReplay/Assembled.lean)
uses this coefficient identity when quoting the original real proposition.
Its independent audit also excludes both older alias theorems. Changed
polynomials, the negative embedding with an unchanged formula, a foreign
coefficient and omitted original divisors retain their existing refusal and
state-restoration controls. The negative-embedding and foreign-coefficient
controls both reject a mismatched fixed-valuation proof; they do not distinguish
conjugates at that boundary. The separate `negative_observed` and `wrong_margin`
controls check the conjugate-specific sign at the reflected selected root.
Its separate fresh consumer requires both the new
coefficient identity and `SourceIdentity.select`. The scalar codec still contains
legitimate checked fixture facts; this work does not remove that finite-input restriction.

The [manual](../HexManual/Chapters/HexRCF/AlgebraicCells.lean) explains this
source-selection boundary alongside complete-cell quotation and real-model
construction. The optional umbrella and default Lake target include the new
module; the published base umbrella remains independent of the family.

This is a fixed-input source-authentication composition, not general frozen
proposal/history reconstruction or a new default tactic backend. General
provider/predecessor histories, all-live transport, strict compiled rejection
of arbitrary missing intermediate records, accepted algebraic completeness,
realization and the remaining stress/performance evidence are still required
by #10358. The separate unrelated-cubic public-decoder experiments do not
establish accepted source reconstruction. No general performance improvement
is claimed. Existing #10633/#10634 implementations and measured limitations
remain unchanged.

## Source-scoped proof observations

The completed source-selection/body-audit selection has 11,084 jobs and takes
59.257s, with 8.3 GiB aggregate peak memory and no swap. Its source-identity
regression module takes 31s and the separate consuming audit 12s. The new
complete-cell source selection has 11,143 jobs and takes 15m14.587s, with
12.8 GiB aggregate peak and no swap; the actual assembly module takes 414s
and its fresh consumer 9.7s. These observations include their respective
incremental dependency rebuilds. They are neither isolated tactic timings nor
a matched before/after comparison. No scaling or speedup follows from them.

Every local Lean/Lake/render/browser command uses one shared systemd unit with
`MemoryMax=34359738368`, `MemorySwapMax=0`, two Lean threads and one own build
invocation across worktrees. The retained active snapshot establishes those
limits; its sampled usage is not the final memory peak. Completed command logs
record their own aggregate peaks, including charged file cache.

## Compatibility and retained evidence

The [retained record](data/hexrcf-source-identities/context.json) binds the
source-selection, actual complete-cell quotation, registered guard and full
compatibility selections to their exact source commits and file hashes.
It includes compressed raw logs, the two all-root manifests, source snapshots,
check exit statuses and the six inspected desktop/narrow captures.

At `4a857a1587`, all 262 HexRCF roots explicitly listed by the authoritative
`HexConformance` globs pass together with `HexRCF`,
`HexRCFRealCoefficients` and the full `HexManual`. The 14,576-job warm selection
takes 12.388s at 2 GiB aggregate peak with no swap. It reuses the earlier
successful artifacts; it is not a cold-build or proof-speed measurement.
The earlier all-root selection is retained as failed: its two guarded fixture
bindings used the older split-coefficient schema. The corrected fixtures
retain their original propositions and both divisor obligations, reusing the
existing one-coordinate schema. Their focused ordinary-kernel/refusal audits
pass in 1m5.375s at 3.1 GiB peak, before the successful full selection.

The full manual render has 14,301 jobs, takes 23.326s and peaks at 4.6 GiB.
The separate browser capture takes 10.916s and peaks at 3 GiB. All six images
were opened; the three inspected paragraphs have zero local overflow at both
1,440px and 390px viewport widths. The whole book and older code blocks are
outside that layout claim. Dependency/umbrella, admission, copyright and
line-count checks pass at the same source commit. The registered guard
regression also checks the exact original-goal equivalence and two actual
terminal tactic refusals. Earlier unsuccessful assertions and unrelated
public-decoder experiments remain excluded from completed validation claims.


## Selection controls and validation scope

The reflected source square has a checked count-one witness and the required
precision. A third actual scalar packet evaluates its margin at the same
positive native root: the observed sign is −1, so it cannot supply the positive
margin needed by `select`. This tests the enclosure's role in distinguishing
real conjugates, independently of a failed fixed-valuation proof.

These scalar queries are requested explicitly by the frontend. Their checked
polynomials are bound to those requested queries. This fixed-input regression
does not authenticate a defining polynomial independently proposed by an
arbitrary native producer, nor reconstruct its source/history.

The [additional validation record](data/hexrcf-source-identities/review/context.json)
binds each tested source to its complete Git tree, including the owner
`FiniteScalars` implementation, and captures commands, script hashes and exit
statuses for metadata checks. Earlier file-hash inventories are source
inventories, not claims that every listed file was executed. In particular,
the earlier selection manifests' “base library/tests” label overstates their
commands: those selected the base umbrella only. The additional selection
explicitly includes all 16 HexRCF base-test modules listed by `HexReleaseTests`,
along with all 262 HexRCF conformance roots, both libraries and the full manual.
The earlier raw records and failed selections remain unchanged.


At `7188977171`, that expanded 14,592-job selection passes in 26m57.749s
at 10.6 GiB aggregate peak with no swap. Fourteen base-test modules rebuild;
`HandlerTests.Support` and `HandlerTests` reuse valid quiet Lake artifacts.
Their selected target arguments, trace snapshots and source bindings are
retained. The rebuilt assembled source takes 441s and its fresh consumer 9s;
the latter requires both the new coefficient identity and selected-root bridge.
These times include different incremental rebuild scopes and do not measure
a change in isolated tactic cost.

## Witness and metadata compatibility

Maximal abstraction retains the whole coefficient while finite supplied-bound
search selects the first named or registered subject as its default witness,
preserving a closed reciprocal or quotient as a whole witness. An explicit
existential equality still takes priority. Universal goals retain no witness
evidence. Identical coefficient/witness evidence is checked once, and a
coefficient's bounds are not added again as witness facts. The selected leaf has
its own frozen containment proof, obtained through the preparation cache;
checking binds its source, observations, request and version without calling
an approximation procedure. Different evidence for an already present subject
still receives its own complete check. Missing, transplanted and malformed witness
evidence is rejected transactionally. This remains a single witness attempt,
not a complete existential search.

Metadata is removed once from the normalized abstraction input. Bare annotated
generators therefore share their coordinate and direct handler with the same
unannotated generator. Named-source detection memoizes closed subexpressions
and excludes type, proof and instance arguments. A nested rational subtree
regression checks the exact source equivalence and coefficient inventory;
it does not establish an asymptotic timing bound.

At source `0da75d3520`, the earlier witness/metadata selection passes
11,184 jobs in 42.299s at
3.1 GiB aggregate peak with no swap. It proves square, interval and nested
existential goals over compound registered coefficients, checks witness
corruption refusals and audits their actual bodies in a fresh module.
It also quotes both bare-metadata and duplicate-metadata goals, checks exact
structural coordinate deduplication and direct-handler eligibility, and audits
the six positive source-packet facts as well as the existing negative controls.
The earlier timing study describes its recorded source trees; it does not
measure these subsequent memoization and witness changes. Full current-source
conformance and hosted CI remain required before merge. The interrupted
selection at `41f1aba4b2` is not a completed validation result.

The direct metadata proof requires `SquareTwo.valuation`, which is emitted only
by the direct frontend. Both frontends use the shared
`FieldBuild.Result.checkForall_sound` theorem; excluding that theorem would
reject the valid direct proof. The fresh audit therefore requires both the
distinct direct valuation and the ordinary field checker.

The [compatibility record](data/hexrcf-source-identities/compatibility/context.json)
binds source `0da75d3520`, all 262 conformance roots, all sixteen base-test
modules, both library targets and the full manual. That selection passes
14,601 jobs in 26m04.380s at 10.9 GiB aggregate peak with no swap. Its raw logs
and the earlier interrupted selection remain distinct.

The subsequent focused witness correction builds 11,784 jobs, including
`HexRCFProofProbe` and the revised caller-bounds manual chapter. It passes in
47.496s at 4.1 GiB with no swap. Closed reciprocal/quotient and compound-equality
witnesses have fresh checked bodies and require their caller registration.
Universal and explicit-equality goals retain no unused default enclosure.
A transplanted witness is checked against its exact subject diagnostic;
altered evidence for a duplicate source is independently rejected.
The first attempt's negative dependency assertion was invalid because the
direct handler itself uses the shared field soundness theorem; the corrected
audit requires its distinct valuation and the shared checker. These focused
results do not replace the required full current-source validation or hosted CI.
