# Complete supplied cells in an ordinary real model

The optional adapter checks a complete matrix of root sections and open
sectors, then quotes acceptance at its original shared one-quantifier source.
The generic checker derives root coverage, cell membership and sign constancy
from checked data. The delivered frozen regression uses rational coefficients
and an ordinary real model; it does not establish general algebraic production,
source/provider history or accepted algebraic completeness.

## Checked composition

[RepresentationCarrier](../adapters/HexRCF/RealCoefficients/RepresentationCarrier.lean)
forms the product of the nonzero specialized atoms using their actual
representation operations. Zero atoms are retained in the formula and handled
separately in the root-coverage proof. Repeated atoms remain repeated factors.
No field instance is introduced on stored tower expressions.

[RootCells](../adapters/HexRCF/RealCoefficients/RootCells.lean) uses the actual
supplied-table coverage and order exports. Its cell indices depend on the
finite descriptor list, independently of the semantic model. An accepted
whole-line table establishes a nonzero squarefree head and covers every root
exactly once.

[RepresentationCells](../adapters/HexRCF/RealCoefficients/RepresentationCells.lean)
composes the actual radical-certificate identities with that root coverage.
It derives coverage for every nonzero source atom, then applies the shared
polynomial sign-constancy theorem on the resulting cells. The strict shared
quantifier folds reuse the existing formula language and its original atom
traversal. Original half-open-domain inequalities remain atoms.

[SectorSamples](../adapters/HexRCF/RealCoefficients/SectorSamples.lean) derives
ordinary sample membership from supplied selected signs against the adjacent
root descriptors. Both finite boundaries are strict; unbounded and empty-root
cases require only the boundaries that exist.
[BoundarySigns](../adapters/HexRCF/RealCoefficients/BoundarySigns.lean) uses the
owner's actual root-minus-point query interpretation.

[PointRows](../adapters/HexRCF/RealCoefficients/PointRows.lean) binds a sample
descriptor's head to the linear polynomial for the requested ordinary point
by a checked zero difference. The descriptor's root is therefore that point.
The whole source row comes from selected-sign replay at that same root and
the actual canonical-specialization evaluation law.

[CellReplay.check](../adapters/HexRCF/RealCoefficients/CellReplay.lean) checks
all original divisors before the radical identities and strict row fold.
Its typed evidence consists of already checked descriptors and selected-sign
packets. It has no semantic coverage, membership or sign-agreement fields.
The actual check_domains and check_sound theorems establish the divisor
conclusions and quantified shared formula from successful acceptance.
Accepted false results remain diagnostic.

## Literal assembly and quotation

[RowReplay](../adapters/HexRCF/RealCoefficients/RowReplay.lean) checks the exact
selected-root subject, original ordered query keys and supplied graph.
[SectorReplay](../adapters/HexRCF/RealCoefficients/SectorReplay.lean) checks
the point, both boundary signs, its linear descriptor and the complete matrix
row. Missing infinite boundaries must have literal null markers; extra claims
are rejected.

[CellRead](../adapters/HexRCF/RealCoefficients/CellRead.lean) checks exact
section and sector counts. A finite dependent collection preserves the original
indices and propagates every child error. Missing entries receive no fallback
record. Original guard preflight precedes any packet decoding.

[CellQuote](../adapters/HexRCF/RealCoefficients/CellQuote.lean) reifies the
original target afresh. It checks the original divisor count, each interpreted
divisor identity in source order, the fixed coefficient valuation and exact
quantified formula. The accepted ordinary proof is composed with that source
equivalence and checked against the original target. Failure restores the
environment and metavariable state. No earlier existential proof is an input.

The APIs use a supplied lawful model of the parent in ℝ. This is an explicit
mathematical interpretation furnished by the existing companion, not an
assertion that arbitrary approximation callbacks form a total field. Nested
parents require supplied checked arithmetic to avoid native lower-level sign
production. The new generic readers do not provide a strict compiled checker
for arbitrary missing predecessor records.

## Frozen regression

The [fixture](../conformance-fixtures/HexRCF/cell-replay.json) contains two
section rows and three sector records. Its source matrix is
p(x) >= 0 and p(x) <= 0 and 0 = 0, where p(x) = x^2 - 2.
The carrier product is p^2; checked radical identities reduce it to the actual
squarefree head p. Both roots are sections. Ordinary sector samples are -2,
0 and 2. Repeated and zero atoms participate in every row.

| Cell | Sample | Sign of p | Matrix verdict |
| --- | --- | --- | --- |
| Left sector | -2 | positive | false |
| Negative root section | negative selected root | zero | true |
| Middle sector | 0 | negative | false |
| Positive root section | positive selected root | zero | true |
| Right sector | 2 | positive | false |

Thus the checked existential is true and the checked universal is false.

The compact fixture has 59,519 bytes. Its twelve graph occurrences contain
51 entries with multiplicity and ten distinct complete graph literals.
These are data inventories, not measurements of shared validation work.
The owner writer emits 118,336 bytes. Every parsed section, sector and nested
graph field round-trips exactly from checked evidence.

[Check](../conformance/HexRCF/CellReplay/Check.lean) exercises both quantifiers'
true and false verdicts. A false matrix and a true disjunction retain the
same actual atom list and checked rows. Original zero guards fail before
malformed decoding or matrix shortcuts.

[Refusals](../conformance/HexRCF/CellReplay/Refusals.lean) rejects swapped
sections, omitted sectors, changed points, an independently valid descriptor
for another point, invalid context indices, cyclic edges and missing basis evidence.
The reader decodes all rows regardless of the matrix; a later cyclic row
is an evidence error even for the false matrix.
The [mutation fixture](../conformance-fixtures/HexRCF/cell-replay-mutations.json)
has 98,779 bytes. The existing constructor renderer verifies each mutation
against its stated field changes.

[Quote](../conformance/HexRCF/CellReplay/Quote.lean) emits fresh original-source
proofs for an existential, a universal and a source retaining division by -1.
[Controls](../conformance/HexRCF/CellReplay/Controls.lean) rejects changed
polynomial sources, changed quantifiers, diagnostic false acceptance, and
omitted, extra or incorrect original divisor identities. Each refusal checks
the expected validation boundary and complete caller-state restoration;
unexpected kernel and resource exceptions propagate.

[Valuation](../conformance/HexRCF/CellReplay/Valuation.lean) authenticates a
nonempty coefficient valuation: the source coefficient `Real.sqrt 4` is
identified with the stored value 2. The source retains both divisors -1 and
2. Reversing their identities or substituting the valuation for `Real.sqrt 9`
is rejected, with caller-state restoration. These tests exercise source
authentication; the polynomial coefficients still lie in the rational base.

[Zero](../conformance/HexRCF/CellReplay/Zero.lean) reads an empty root table
and its single sector with two absent boundaries. Both quantifiers accept
the zero equality and return false for the strict zero inequality. An
original zero divisor fails before constant processing or malformed decoding.
The [two-root boundary controls](../conformance/HexRCF/CellReplay/Refusals.lean) reject non-null infinite endpoints, null finite
endpoints, swapped bounds and a checked sample outside its proposed sector.

[Ordinary](../conformance/HexRCF/CellReplay/Ordinary.lean) checks actual proof
bodies and its imported theorem axioms. Its dependency walk requires the actual
radical, full-root, point-binding, membership and selected-sign laws and
rejects named native root/sign producers and prior root witnesses.
[Quoted](../conformance/HexRCF/CellReplay/Quoted.lean) audits each original
source body separately and excludes the earlier shared-formula witness.
The five quoted sources have exactly propext, Classical.choice and Quot.sound.
The quotation audit also sweeps all theorems in the new valuation and
constant modules. The zero equality is quoted from its original constant-only
source through fresh reification and `CellQuote.finish`. The checked zero
packet also round-trips through the shared emitter. The separate
[outside-boundary fixture](../conformance-fixtures/HexRCF/cell-outside-right.json)
records the negative root's checked sign at point 2. The upper-bound control
keeps the existing point-2 descriptor and full row; only its proposed cell
and boundary packet change. The lower-bound control similarly keeps the
valid point-zero descriptor and row. Thus both tests reach their respective
strict boundary sign checks. They reject before decoding the retained
descriptor and row; the original accepted packets check those fields separately.
A positive replay control pins the new upper packet to the intended root,
point query and negative sign. Both packet round trips are also enforced
during the emitter build, and the axiom sweep requires both source modules.
The public module boundary is exercised by
[ModuleCheck](../conformance/HexRCF/CellReplay/ModuleCheck.lean).

## Scope and evidence

The optional default Lake target, umbrella, existing conformance target and
constructor renderer include the delivered modules. The manual has a runnable
public API example and describes the actual source regressions. There is no
new tactic handler, formula AST, owner algorithm or CI job.

At source `299b0039cd`, the complete optional adapter, conformance and manual
build passes 14,639 jobs. Structural checks include the dependency DAG,
umbrella, 584 admission cones over 1,484 modules, eleven scanner regressions,
copyright, manual split, constructor regeneration, relative links, Lean line
limits and diff checks.

The [validation manifest](data/hexrcf-cell-replay/context.json) binds this source
to the full build, actual forced packet emission, manual rendering, structural
checks and desktop/narrow browser captures. The captures include the runnable
code block; their measured targets have no descendant overflow. This makes no
whole-page overflow claim. The
[previous snapshot](data/hexrcf-cell-replay/before-review/context.json) separately
retains source `091250da98`, its 14,635-job build, 10,980-job forced emitter,
14,204-job render and all eight earlier captures. Each snapshot's manifest
records its own exact file counts and hashes.

These build records are correctness evidence. No matched performance
comparison or scaling claim is made. Shared constructor literals do not
establish that readers reuse validation across rows.

General algebraic construction, accepted completeness, automatic common-field
certification, provider/context histories, all-live transport and the complete
infinitesimal realization path remain required by issue 10358. Complete cell
assembly in this ordinary-model API resolves only the corresponding
previously missing composition. The optional adapter's full acceptance scope
remains open.
