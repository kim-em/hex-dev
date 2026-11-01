# Checked source arithmetic and original-divisor composition

`TowerCompile` shares checked subterms within one `compile` or `prepareWith`
call. A preparation call uses the same temporary expression map for both its
coefficient and original-divisor inventories. The model is fixed and checked
before that map is created. Separate calls do not share entries, even within
one surrounding quotation request. Outer metadata is removed before leaf
recognition and cache lookup. Each occurrence still checks closedness and its
real type and incurs a charged lookup; each newly computed term retains the
existing exact-target, unsafe-dependency, axiom and ordinary-kernel checks.

A declining leaf restores both Meta state and frontend state, retaining its
charged work. The callback follows normal `ReifyM` budget operations; arbitrary
replacement of the budget ledger is outside this trusted Meta callback contract.
The enclosing quotation transaction handles terminal failure.
Conformance checks a selected leaf used by two distinct coefficient expressions
and an original divisor: it runs once in that preparation, runs again in a
separate request, and recognizes a metadata-wrapped source. A separate control
changes frontend inputs, binders and formula size, then declines; the state is
restored and its nine-node charge remains. These observations establish the
specified sharing and rollback behavior, not a general timing improvement.
Full newly visited subexpressions are still checked and charged; deep chains
can have quadratic aggregate work. No shared axiom-admission cache is added.

`CellQuote.valuationWith` checks each scalar identity's type at its exact finite
coordinate before building the dependent family. The final equality still
passes ordinary-kernel proof admission. The model, coordinate function and
source valuation must be closed; scalar proofs may retain caller hypotheses,
which remain assumptions of the generated theorem. Negative controls observe
the intended diagnostics without restoring state on the API's behalf. A wrong
coordinate, missing proof or unresolved coordinate cannot pass merely because
an unrelated exception was raised.

The complete-source regression proves
`∃ x : ℝ, x² - ((Real.sqrt 2 + 1) - 1) ≥ 0 ∧
x² - ((Real.sqrt 2 + 1) - 1) ≤ 0 ∧ 0 / ((-1 : ℝ) + 0) = 0`.
It prepares the original goal, compiles the compound coefficient and the
original divisor, constructs the whole valuation identity, and finishes against
the independently retained goal expression. Its selected leaf identity and
ordinary-real model are supplied. Its complete root/cell acceptance comes from
the already checked typed fixture. This is arithmetic-to-source composition;
it does not freshly reduce the fixture's serialized readers or produce a new
root certificate.

Alignment reinterprets the same arithmetic relative to the model value of the
same stored leaf, checks structural equality between the outputs of those two compiler runs,
and
uses an ordinary real arithmetic proof. It assumes no equality of arbitrary
stored representations from equality of their values. The compiled identities
then bind the fixture's coefficient and guard values to the original source.
The finishing request consumes 32,257 charged nodes within the default budget.

Because real division is total, the final real proposition need not logically
depend on its separately checked nonzero-divisor preflight. The regression also
retains the actual original-divisor theorem emitted by `finishPacketWith`.
The importing audit therefore checks both the source proof and that actual
guard conclusion, rather than constructing a replacement guard proof. It
requires the model's addition, subtraction, division and natural-number laws
and the checker's soundness and domain theorems in their dependency closure.
It rejects the old original-source proofs and the listed root producers.
Per-root checks additionally require direct constant references in the actual
generated local theorem bodies: the source path must use the model's subtraction
law and supplied selected-leaf identity, while the emitted guard path must use
the negation law. Imported checker/model bodies cannot satisfy these checks.
The compiler audit requires each corresponding arithmetic law on its own case's
path; the two-coordinate valuation path must directly use addition, natural
literals and the selected-leaf identity. The decline control compares two
otherwise identical requests and requires exactly nine additional charged nodes.

The fresh importing audits recheck 40 actual compiler theorem bodies with 39
nonempty traces, 13 valuation bodies with 12 traces, and 30 compound-source and
guard bodies with 30 traces. Their complete transitive axiom inventories are
exactly `propext`, `Classical.choice` and `Quot.sound`; copied declarations are
not retained. The zero/one/two-coordinate requests use 7,590/11,306/16,802 charged
nodes. The nine arithmetic cases use 441, 711, 1,111, 540, 826, 742, 1,857, 247
and 276 nodes. These are scoped proof/accounting observations, not scientific
speedup comparisons.

The original large literal-source example remains separate. It uses a bare
selected coefficient and no original divisor, explicitly supplies a
24-million-node budget and 60 million heartbeats, and keeps its independent
literal/producer guards. The [earlier source record](hexrcf-source-valuations.md)
retains its original immutable implementation pin. Its old counts do not
validate later source edits.

The current large literal-source quotation passes with 9,337,150 charged nodes
for the entire request (9,337,056 at the completed source proof), retaining two
graph-memo reuses and seven validations. Its importing audit rechecks 1,192
actual theorem bodies and 202 definitions with 1,352 nonempty kernel traces and
exactly the standard three axioms. All earlier dependency and producer guards
remain. The source module takes 841 seconds; the combined affected build passes
11,172 Lake jobs with cached dependencies reused in 21 min 5.555 s, peak 7.9 GiB
and no swap. These are operational observations, not a scientific comparison.

The nine-target compatibility/manual integration passes 14,421 Lake jobs with
cached dependencies reused, including the full source audit, all three new
proof audits, base handlers, existing tactic regressions, optional umbrella,
public codec consumer and complete manual. It takes 43 min 56.279 s, peak
14.4 GiB/no swap. The restored workspace required compiling broad manual
prerequisites. This validates affected targets and the manual, not the entire
default conformance target or a performance comparison. The first browser
check rejected a six-pixel narrow-code overflow in the fully qualified theorem
name; its failed log, metrics and captures are retained separately.

The formatting correction uses a shorter theorem reference under `open Hex.RCF`.
The final complete manual rebuild passes 14,411 Lake jobs with cached
dependencies reused in 2 min 46.259 s, peak 2.1 GiB/no swap. Final HTML render
passes in 16.094 s, peak 1.6 GiB/no swap; browser capture passes in 10.854 s,
peak 4.9 GiB/no swap. All six final desktop/narrow API, code and provenance
captures were actually inspected. The changed blocks have zero local overflow;
this does not attest the layout of every other manual section.

The [source-bound evidence record](data/hexrcf-source-composition/README.md)
retains both final validation and labelled earlier failures. Its verifier binds
source hashes, unchanged owner artifacts and exact-head owner CI, the actual
private-proof audits, per-root references, original goal accounting, ten
repository checks including twelve DAG tests, and the six final captures.
Earlier records keep their original source pins. Relative links and staged
whitespace are checked after packaging. The independent final source review
found no remaining blockers; its source-only limits and dispositions are
retained with the validation rather than treated as a replacement for builds.

Owner PR #10984 is merged at `0f08a838192fd65e287de2afeb7bef20a214d2f0` and
consumed unchanged. Its public graph, entry and node equations expose outer
encoding fields. They do not supply every nested encoder equation, prove
arbitrary numerical-frame equality or finish the general interleaved exporter.
The presentation-model equation and root coverage/order laws were already
available. Generic source/provider/history discovery, full automatic tactic
integration, strict all-depth replay and accepted algebraic completeness remain
unfinished. Full #10358 stays open. Every own Lean/Lake/render/browser invocation
remains serial under a hard aggregate 32 GiB cap, zero swap and two Lean threads.
