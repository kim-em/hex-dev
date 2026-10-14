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
also reproduces [mutation literals](../conformance-fixtures/HexRCF/guarded-matrix-mutations.json).

```sh
lake build +HexRCF.FiniteMatrix.Guards.Ordinary
python3 scripts/rcf/selected_literals.py --check
HEX_RCF_FINITE_GUARDS_OUTPUT=/tmp/hex-rcf-guards.json \
  lake build +HexRCF.FiniteMatrix.Guards.Emit
```

The emitter writes only when elaborated; reproduce with a fresh target build.
Compare parsed JSON, since whitespace is not certificate identity.

These regressions extend the existing fixed authenticated parent and ordinary
selected point. They do not supply automatic history restoration, complete
root/cell coverage, common-field automation or algebraic completeness. Those
remain obligations of #10358. The #10633/#10634 fixed-field improvements and
their retained measurement limits are unchanged. No timing or scaling claim
is made. No owner library, AGENTS.md/PLAN.md or CI workflow is changed.
