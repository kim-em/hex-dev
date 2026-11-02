# Prepared coefficients and complete source valuations

The complete original-source quotation now consumes `TowerCompile.prepareWith`
inside its existing cumulative request. The leaf callback authenticates the
selected positive square root through the actual descriptor, equation and window
reader before returning its stored coordinate and scalar identity. It does not
reuse the older imported selected-root or coefficient identity. The unchanged
goal is `∃ x : ℝ, x² - Real.sqrt 2 ≥ 0 ∧ x² - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0`.

[`CellQuote.valuationWith`](../adapters/HexRCF/RealCoefficients/CellQuote.lean)
assembles the ordered scalar identities into equality of the entire finite
source valuation. It checks closed inputs, exact coordinate and proof counts,
the dependent family and the final equality in the ordinary kernel. It reuses
the existing finite-family quotation helper. Original divisor obligations remain
separate and are checked by source finishing. The complete example uses the new
helper instead of a source-specific one-coordinate tactic proof.

The [standalone conformance](../conformance/HexRCF/SourceValuationConformance.lean)
constructs zero-, one- and two-coordinate valuations using the actual selected
√2 model and supplied leaf identity. Full-request charged node counts are 7,590,
11,306 and 16,802, including preparation, arithmetic, the zero fallback and finite
function construction. Swapped coordinates, swapped proofs, missing proofs,
wrong coordinate counts and unresolved caller-owned coordinate functions reject.
The unresolved-input control checks that the caller's metavariable remains
unassigned and the declaration inventory is unchanged. The
[fresh importing audit](../conformance/HexRCF/SourceValuationProofs.lean)
rechecks thirteen actual theorem bodies, including private generated proofs,
with twelve nonempty kernel traces. Its complete transitive axiom inventory
is exactly `propext`, `Classical.choice` and `Quot.sound`; copied declarations
are not retained. These standalone proofs intentionally consume an authenticated
leaf; they do not reconstruct it automatically.

The historical source-bound implementation records 705,649 charged nodes after
fresh source authentication, 705,699 after inventory compilation, 707,592 after
polynomial reconstruction, 9,330,130 before finishing, 9,336,963 at the completed
source proof and 9,337,057 for the entire request. The graph memo still reports
two reuses and seven validations. This example explicitly supplies a 24,000,000
proof-node budget and 60,000,000 heartbeats; it does not run within the default
1,000,000-node request budget. Its build passes 11,177 Lake jobs with cached
dependencies reused in 13 min 17.611 s, peak 2.3 GiB/no swap. The separate fresh
full-source audit rechecks 1,192 theorem bodies and 202 definitions, with 1,352
nonempty kernel traces and exactly the standard three axioms. It passes in
3 min 22.868 s, peak 2.7 GiB/no swap. Every earlier required/forbidden dependency
and producer-reduction guard remains active. The retained model, source alias,
coefficient-map identities and seed facts remain supplied inputs.

The final seven-target integration passes 14,417 Lake jobs with cached
dependencies reused: the full source audit, standalone valuation audit,
compiler audit, base handler regressions, existing real-coefficient tactic
checks, optional umbrella and complete manual. It takes 9 min 15.978 s,
with peak 7.6 GiB/no swap. This is an affected-target integration, not a claim
that the entire default conformance suite ran.

The complete manual render passes in 23.489 s, peak 1.7 GiB/no swap.
Browser inspection passes in 10.499 s, peak 2.8 GiB/no swap. All six final
1440-pixel desktop and 390-pixel narrow captures were actually viewed. The
changed API, checked code and provenance blocks have zero local overflow.
These local checks do not attest the layout of every other manual section.
Ten repository checks pass, including twelve DAG-boundary tests, dependency
and umbrella validation, admission checks, deterministic literal regeneration
and whitespace checking. Relative links are checked after packaging the record.

The [source-bound record](data/hexrcf-source-valuations/README.md) distinguishes
the successful final implementation from preliminary attempts. The initial
compiler-only full quotation passed, but its importing audit correctly rejected
the old exact body count; the updated exact inventory then passed. The first
combined valuation build rejected two leftover identifiers before quotation
ran; those redundant lines were removed. Neither failure validates final code.
Earlier proof and numerical records retain their original source pins.

This connects selected-coefficient preparation and general finite valuation
assembly to one complete original source proof. That complete source uses a
bare selected coefficient and no original divisor. Arithmetic and original
divisor compilation are tested separately; this example does not establish
their composition with complete-cell finishing. The separate
[compound-source regression](hexrcf-source-composition.md) now covers that
composition using a supplied checked typed fixture, with a 40/39 compiler audit,
13/12 valuation audit and 30/30 compound-source/domain audit. These current
checks include per-call term sharing and exact rejection diagnostics. They do
not turn the historical literal-reader record into evidence for later source
edits. The adapter does not discover arbitrary
source leaves, providers, predecessor histories, coefficient maps or seed facts.
It does not establish full automatic tactic integration, strict all-depth
missing-record rejection, accepted algebraic completeness or general finite
joint realization/export. The public presentation-model equation and #10377
coverage/order laws are already available; numeric-frame and general-export
integration still require their actual reviewed and merged owner APIs. Full
#10358 remains open. These build observations are operational evidence, not a
new scientific timing comparison or speedup claim. Every own Lean, Lake,
render and browser invocation runs serially under the hard aggregate 32 GiB
cgroup cap, with zero swap and two Lean threads.
