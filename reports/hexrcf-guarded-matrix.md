# Ordered original divisors in finite matrix quotation

The optional adapter's frozen joint replay now has a regression with two
original divisors, `Real.sqrt 2 - 1` and `-1`, in source order. Its
[quoted source](../conformance/HexRCF/FiniteMatrix/Guards/Quote.lean) is
`∃ x : ℝ, x² = Real.sqrt 2 + 0/(Real.sqrt 2-1) + 0/(-1:ℝ) ∧ 1<x ∧ x<2`.
Fresh source preparation retains the first whole zero quotient as a second
coefficient coordinate used by the matrix. The checked source binding uses
the canonical shared specialization's all-valuation theorem.

The [literal packet](../conformance-fixtures/HexRCF/guarded-matrix.json)
contains two upper graphs and one additional stored-sign record. It reuses
the existing 31 scalar facts, 43 packing records and 21 stored signs. Its
five fields have exactly 28,786 bytes including the final newline.
The positive packet's guard prefix is `[1,-1]`; `check_domains` proves both
original real divisors nonzero. A second packet retains zero as the first
guard and rejects with `.divisor`, including for a constant true matrix.
Kernel diagnostics forbid matrix evaluation during these zero-guard checks.

[Quotation controls](../conformance/HexRCF/FiniteMatrix/Guards/Controls.lean)
reverse, omit or append source identities and replace the first denominator
with a cancelled zero difference. Each refusal restores the environment and
metavariable state. [Restoration controls](../conformance/HexRCF/FiniteMatrix/Guards/Refusals.lean)
reject reordered guard queries, a changed context and a cyclic graph under
active ordinary-kernel producer diagnostics. Omitting the additional stored
sign leaves reduction unresolved; only the kernel's typed declaration
mismatch counts as that expected refusal, and resource errors propagate.
The owner's supplied dictionaries remain kernel-assembly interfaces; this
does not establish a strict compiled checker for arbitrary packets.

The [fresh audit](../conformance/HexRCF/FiniteMatrix/Guards/Ordinary.lean)
checks the actual quoted proof body, exact standard three-axiom inventory,
required checker/owner laws, all project type/body dependencies and every
new module theorem's axioms. It excludes named previous existential proofs.
Upstream packages are dependency-scan leaves. Separate kernel diagnostics
require the actual readers and decisions to unfold without native producers;
these diagnostics do not cover previous opaque theorem construction.

The [emitter](../conformance/HexRCF/FiniteMatrix/Guards/Emit.lean) round-trips
the checked packet through owner codecs. It does not independently regenerate
upper graphs or the predecessor inventory. The existing constructor renderer
also checks that each mutation changes only the first two query positions,
context identifier, or root dependency, and reproduces [mutation literals](../conformance-fixtures/HexRCF/guarded-matrix-mutations.json).

```sh
lake build +HexRCF.FiniteMatrix.Guards.Ordinary
python3 scripts/rcf/selected_literals.py --check
HEX_RCF_FINITE_GUARDS_OUTPUT=/tmp/hex-rcf-guards.json \
  lake build +HexRCF.FiniteMatrix.Guards.Emit
```

The emitter writes only when elaborated; reproduce with a fresh target build.
Compare parsed JSON, since whitespace is not certificate identity.

The [nonzero-quotient source](../conformance/HexRCF/FiniteMatrix/Guards/Quotient/Quote.lean)
is `∃ x : ℝ, x²+1=1/(Real.sqrt 2-1)+0/(-1:ℝ) ∧ 1<x ∧ x<2`.
Fresh recognition retains one coefficient, the whole inverse quotient, and
both original divisors. Its value comes from the owner's actual
`Packing.Inverse.Equation.denote_inv` law and the literal reader's exact
operand-binding theorem. The supplied equation identifies an inverse at the
selected root; no equality with the native inverse algorithm's representative
is assumed. This does not install a raw-syntax field instance.

The [13,780-byte packet](../conformance-fixtures/HexRCF/guarded-quotient.json)
contains the checked inverse graph, one extra packing record, an independently
valid graph for `(α+1)*(α-1)=1`, and a context-only mutation. Here α is the fixed
positive √2. The actual shared specialization uses the supplied inverse value;
its checked equality with the old query list reuses the same upper selected-point
packet. No new upper root or upper sign graph is produced. The extra packing
is for `-X-1`; it includes its own scalar evidence and does not add a scalar
fact to the old input list.

[Frozen controls](../conformance/HexRCF/FiniteMatrix/Guards/Quotient/Controls.lean)
reject the other valid pair on the original request, a changed output, stale
context and missing graph. A zero operand rejects before decoding. Omitting the
additional packing leaves kernel reduction unresolved; only the expected
`declTypeMismatch` of the attempted reflexive declaration counts as refusal.
Resource errors propagate. A changed numerator preserves the guard list but
fails source valuation authentication. A zero denominator fails original-divisor binding.
Both quotation failures restore environment and metavariable state.

The [fresh quotient audit](../conformance/HexRCF/FiniteMatrix/Guards/Quotient/Ordinary.lean)
checks actual proof bodies, exact three-axiom inventories for the source and
inverse proofs, all project dependencies and every new theorem's axioms. It
requires the actual inverse law, reader equation, specialization decision and
whole-matrix checker, and excludes previous existential proofs and the actual
named native inverse builders, native candidate binding/meaning and the
native-to-equation conversion. The inverse proof body must directly use the
frozen record and the supplied equation law. The checked four-field packet
round-trips through owner codecs; the stale field is retained literally and rational scalar evidence is
regenerated. This is not independent regeneration of the inverse graphs.

The optional adapter also consumes the merged supplied-replay semantics from
[owner PR #10903](https://github.com/kim-em/hex-dev/pull/10903), commit
`8e5b3e40a69117c84bb6f0c19aaad93a26049ab8`. Its
[`RootReplay.Result.values`, `coverage`, `ordered`](../adapters/HexRCF/RealCoefficients/RootReplay.lean)
interpret the extracted list in any supplied lawful real-closed model. Full
root-set equality, interpreted-value `Nodup` and strict ordering follow from
the actual owner's `Descriptor.rootsFrom_coverage` / `rootsFrom_ordered` laws.
No native producer equation is assumed and no owner proof is duplicated.

The [fresh root-list consumer](../conformance/HexRCF/RootReplayOrdinaryConformance.lean)
characterizes the two-root whole-line result exactly by `x²=2`, proves root
absence for the nonzero constant and `X²+1`, and derives duplicate-free strict
ordering. Actual source bodies and imported adapter wrapper bodies are
rechecked; wrapper bodies must call the specified owner exports. The coverage
audit follows all project declaration types and bodies, stopping at upstream
packages, and rejects native root producers. Local marker scans remain separate.
Complete axiom inventories use
exactly the standard three axioms. Existing acceptance/refusal kernel producer
diagnostics remain separate. This resolves the supplied-root coverage/order
export requirement; general history, all-live transport, complete formula-cell
assembly and accepted algebraic completeness remain.

The guarded matrix and inverse examples use the fixed authenticated positive-√2
parent and one ordinary selected point. The generic root-list laws require a
supplied lawful model. Automatic history restoration, complete formula-cell
assembly, common-field automation and algebraic completeness remain required
by #10358. The #10633/#10634 fixed-field improvements and
their retained measurement limits are unchanged. No timing or scaling claim
is made. No owner library, AGENTS.md/PLAN.md or CI workflow is changed.

Source `6b5a134630` passes the complete optional-adapter, conformance and manual
build (14,601 Lake jobs), including the existing Point/Section quotation and
fresh ordinary-proof consumers. The new standalone guard audit passes 11,211
jobs. Admission scanning covers 544 cones and 1,441 modules; all eleven
scanner tests pass. DAG/umbrella, exact literal generation, copyright, manual
split, relative-link, new-file line-limit and whitespace checks pass. These
are validation records, not scientific timing measurements.

The [guard-only manifest](data/hexrcf-guarded-matrix/before-quotient/context.json) binds each
retained build to its source, selected source hashes, compressed/decoded
logs, the complete round-trip packet and the render/browser drivers. The
final documentation source `a8e6682bf2` passes its 11,684-job chapter build
and 14,192-job full HTML rendering. Six desktop/narrow captures check the
three added paragraphs at 752/343 pixels with zero descendant overflow.
The inspected section fits; no whole-page overflow claim is made.

The full integration at `3552c280f8` passes 14,601 jobs after reconciling
upstream main. At `968836437e`, the added frozen quotient audit passes 11,219
jobs; its emitter and updated source chapter pass 11,812 jobs. All four emitted JSON fields
match the retained fixture exactly. The expanded admission scan covers 554
cones and 1,451 modules without admissions, and all eleven scanner tests pass.
The [combined validation manifest](data/hexrcf-guarded-matrix/context.json)
retains the separate source versions rather than attributing the later
quotient checks to the earlier guard-only build.

The supplied-root consumer, ordinary module boundary and updated manual example
pass in a combined 11,693-job build, including the complete two-root set and
both empty-table cases. The source
proofs and the actual imported wrapper bodies are kernel-checked; local marker
scans keep imported declarations as leaves.

At `88d2e2c12d`, the affected build passes 11,222 jobs for the optional adapter, nested-root
and root-transport consumers, and the frozen quotient audit. These checks
consume the adopted supplied-root exports; the earlier complete 14,601-job
build remains bound to its separate pre-adoption source.

The final source documentation renders successfully in 14,192 Lake jobs.
Desktop/narrow inspection covers the root-coverage explanation and its actual
ordinary-module code block, together with the guarded inverse paragraphs.
The earlier guard-only and inverse-only captures retain their own source
bindings in the separate historical manifests.

At `e49d0f263f`, the complete optional adapter, conformance and manual build
passes 14,610 jobs after the supplied-root adoption. The focused audit build
passes 11,222 jobs at the same Lean source. These later records supplement the
earlier stages without replacing their recorded source identities.
