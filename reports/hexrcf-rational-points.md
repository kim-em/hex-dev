# Rational parent points in algebraic input preparation

[`AlgebraicCells.presentation`](../adapters/HexRCF/RealCoefficients/AlgebraicCells.lean) recognizes an exact rational with the existing
`RealAlgebraicNumber.toRat?` operation and passes a parent point to the owner's
checked `Presentation.ofRoot?` constructor. Other values use the complete
selected-generator factory. A failed checked point is not retried through
isolation. The adapter constructs no new coefficient carrier or root checker.

The load-bearing `presentation_success` proof uses `toRat?_eq_some`,
`Trivial.Map.rational_value` and `Presentation.ofRoot?_isSome`. Tuple
presentation and complete build/soundness proofs compose through that result.
Coefficient order, original guard order and repeated indices are unchanged.
Every declared input remains present, including unused inputs; original zero
guards still reject before any presentation construction.

The frozen diagnostic probe confirms the existing factory represents rational
one with a selected root. Checked parent-point preparation accepts 0, 1, −1
and 7/3. Routine conformance requires those actual returned roots to be parent
points with their original rational values, rejects points offset by one,
and checks repeated tuple and guard coordinates. Existing positive/negative
selected square roots, independent fields, quantified verdicts, linear
constraints, late zero guards and empty constant formulas still pass.
Thirteen actual theorem bodies and their transitive axiom closures are checked;
only `propext`, `Classical.choice` and `Quot.sound` are allowed. Dependency
checks require the actual rational recognizer and checked point factory laws.

The source-bound validation at `53cc610c67d9c1eb2aa6f320a7262ceb4786f716`
builds both RCF libraries, rational handler/reification/decision regressions,
algebraic preparation and its fresh importing audit, algebraic-input
conformance and the manual chapter. The initial command included a nonexistent
`HexRCF.HandlerConformance` target; its only failure was that target lookup,
while the requested source-authentication consumer built successfully. The
corrected command uses `HexRCF.HandlerTests` and passes 11,793 jobs. The source
authentication cases rebuilt in 222 s and their importing audit in 10 s in the
initial command; the corrected command reused them. Its 4.139 s runtime is
therefore not a cold rebuild cost or speedup. All completed observations and
failed attempts are retained separately.

The retained unchanged stress attempt at parent `51420aab0e` was manually
interrupted after 14 min 53.256 s without a trial result, using 14 min 53.079 s
CPU and peak 1.3 GiB/no swap. Its signal15/TERM distinguishes it from a passing
build even though systemd classifies an operator stop as success. The sampled
native GMP/Rat arithmetic, nested polynomial gcd and inverse frames identify
work, not a coefficient-growth theorem. Removing the unnecessary rational
owner does not by itself establish that this stronger case is repaired.

The stronger stress case with the revised rational-point preparation also
reached its 15-minute deadline: exit 1, `result: timeout`, signal15/TERM,
runtime15min71ms, CPU14min58.454s and peak1.2GiB/no swap. No completed module
or trial result was recorded. A sample from that same process still reaches
native rational arithmetic through `xgcdLeftAux`, `xgcdLeft`,
`Algebraic.Element.inversePolynomial` and `Sturm.normalize`, with additional
nested inversions. This preserves the evidence of a remaining owner arithmetic
bottleneck. The adapter change does not discharge this stronger performance
requirement. Neither interrupted run is a completed measurement or a
mathematical false verdict; no relative speedup follows from these deadlines.

These are shared-host operational build observations and a structural
representation change, not adjacent alternating AB/BA samples or a matched
performance claim. All own builds are serial with a hard aggregate 32 GiB
limit, no swap and two Lean threads. The revised stress uses a 15-minute
operational deadline, not a scientific or mathematical search budget.

Full #10358 remains open. These changes do not supply generic frozen
source/provider/predecessor authentication, strict compiled rejection of
missing reached records, a general tactic quotation/completeness result,
or the remaining realization and scaling evidence. Reusable arithmetic and
inverse normalization remain with their existing owners.

The [source-bound record](data/hexrcf-rational-points/context.json) retains exact
source hashes, raw logs, cap settings and the interrupted diagnostic. The
[conformance driver](../conformance/HexRCF/AlgebraicCellsConformance.lean)
contains the executable controls and theorem-body audits.
