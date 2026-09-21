# Real-closure storage and context experiments

## Decisions supported by the experiments

Retain a value-preserving remainder already computed during zero testing when
the defining polynomial is monic and clean. Keep the general unreduced path
for non-monic or non-clean definitions; do not monicize them to impose a storage
degree bound. An available verified irreducibility fact can skip gcd/root
selection, but finding such a fact is not a prerequisite for using squarefree
definitions. The generic zero test remains required.

Use immutable contexts and explicit persistent refinement. Rebuild dependent
polynomials and root selections in predecessor order, transport requested live
values, and give the results fresh full-context certificate bindings. Old
contexts remain valid. This matches the existing family design rather than
requiring mutable global field state or automatic rewriting of all handles.

## Scope and independent checks

[Protocol and sources](../experiments/RealClosureAlgebraic/POLICY-PROTOCOL.md).
E1 uses positive sqrt(2), initially described by `(X²−2)(X²−3)`, and then a
second level defined by `Y²−sqrt(2)`. The policies are:

- 0: generic selected-root zero test, unreduced nonzero representatives;
- 1: same defining polynomial and zero test, retaining its exact remainder;
- 2: same retention, with the smaller definition `X²−2`;
- 3: same smaller definition, with its justified irreducibility fast path.

All use existing `DensePoly` arithmetic, division, gcd and xgcd; no fake field
instance or fallible coefficient-operation interface is introduced. The
prototype enforces literal nonzero storage; semantic zero correctness is a
fixture claim checked independently, not a universal theorem about its type.
The production constructor/companion obligations remain in the revised SPECs.

FLINT factorization confirms irreducibility of `X²−2` and `X⁴−2`. The latter
justifies the second quadratic extension over Q(sqrt(2)). Independent arithmetic
in Q[X]/(X⁴−2) checks 12 base and 8 nested full quotient/remainder/gcd outputs,
28 repeated-squaring values and five refinement values, including an inverse.
This is executable conformance, not Lean irreducibility or transport proofs.
All output hashes agree between policies and between timed and traced execution.

## E1: time, zero tests and representative growth

[Raw harness samples](../experiments/RealClosureAlgebraic/results/policy/timing/samples.jsonl),
[metadata](../experiments/RealClosureAlgebraic/results/policy/timing/metadata.json),
[summary and callback counts](../experiments/RealClosureAlgebraic/results/policy/summary.json).
Ten cases, three adjacent policy pairs and six AB/BA blocks yielded all 360
retained arm samples, with no rerun or activity-based exclusions. lean-bench
owns warmup and adaptive repeats with a 50ms floor. Preparation is outside
timing; full semantic hashing is included in every arm. These fixed comparisons
are not Phase-4 complexity evidence, and output degrees are not peak
intermediate sizes.

Host: chungus2, x86_64, automatically leased CPU 56. Starting load averages: 5.79, 15.58, 39.81. Lean: `leanprover/lean4:v4.34.0`; lean-bench: `8a37daf1074c3bdbd0da479b55538bad4a0022db`. Metadata binds the timed source hashes; the audit checks those sources.

Each cell is the median paired speedup and the full six-pair range. Larger
than one favors the second policy. Pair 1/2 changes the descriptor as well as
its degree; it must not be attributed to storage alone.

| Field / length / operation | Retain remainder (0/1) | Smaller descriptor (1/2) | Irreducible fast path (2/3) |
|---|---:|---:|---:|
| base / 2 / division | 1.20× (1.19–1.21) | 3.01× (2.98–3.09) | 1.39× (1.38–1.40) |
| base / 2 / gcd | 1.15× (1.14–1.16) | 2.72× (2.70–2.74) | 1.33× (1.33–1.34) |
| base / 3 / division | 1.32× (1.31–1.32) | 3.75× (3.68–3.78) | 1.52× (1.52–1.53) |
| base / 3 / gcd | 1.21× (1.21–1.23) | 3.04× (2.99–3.06) | 1.38× (1.38–1.38) |
| base / 4 / division | 1.34× (1.34–1.35) | 4.19× (4.18–4.23) | 1.63× (1.62–1.65) |
| base / 4 / gcd | 1.23× (1.22–1.24) | 3.05× (3.03–3.13) | 1.44× (1.42–1.44) |
| nested / 2 / division | 2.68× (2.66–2.72) | 3.57× (3.53–3.60) | 1.91× (1.90–1.93) |
| nested / 2 / gcd | 2.45× (2.41–2.48) | 3.55× (3.52–3.57) | 1.89× (1.87–1.90) |
| nested / 3 / division | 3.22× (3.18–3.26) | 3.91× (3.86–3.96) | 1.96× (1.94–1.98) |
| nested / 3 / gcd | 2.72× (2.71–2.75) | 3.44× (3.36–3.49) | 1.86× (1.83–1.91) |

Retaining remainders improves the base cases by 1.15–1.34× and nested cases
by 2.45–3.22×. A smaller descriptor adds 2.72–4.19× in these fixtures; this does
not include the one-time cost of discovering or transporting a persistent
split. The irreducibility fast path adds 1.33–1.96×, with its fixture fact
already available. None of these ratios is a claim about arbitrary towers.

The actual zero-test callbacks are traced separately, outside timing.
At nested length 3, division makes 11 upper-level tests in both policies 0/1,
but lower-level calls fall from 227 to 135. Gcd retains 21 upper calls while
lower calls fall from 602 to 450. At the base, counts are unchanged by retention:
11–29 calls over the registered cases. Retention therefore changes operand
sizes and predecessor work, not the need for leading-zero decisions. Modes
4–7 are the diagnostic counterparts of 0–3, and every trace result hash agrees
with the corresponding timed result.

Unreduced output representatives reach base degree 5, and at two levels
upper degree 2/lower degree 13. Retention bounds those output degrees by
3 at the reducible base and by 1/3 at the two levels; the minimal base gives
1/1. Repeated squaring of X stores degrees 1,2,4,8,16,32,64 without retention;
with retention the stored degree stays at 2 after the first square under
the reducible definition, and becomes 0 after the first square under the
minimal definition. Equal values therefore still need not have identical
nonzero representatives under the reducible definition.

The fixtures are small and monic. They do not measure general root isolation,
non-monic clean/eager behavior, bit complexity, or the full paper's tower8.
The non-monic path remains essential for the clean-representation contract.
No batching optimization for division is justified by these results; the
previous multiplication comparison remains limited to ring-operation buffers.

## E2: dependent context refinement

[Refinement source](../experiments/RealClosureAlgebraic/Refinement.lean) and
[retained checks](../experiments/RealClosureAlgebraic/results/policy/refinement.jsonl).
The lower split retains `X²−2` and discards `X²−3`; the reverse choice is rejected
because it loses the selected root. The upper polynomial uses the lower raw
coefficient `X+(X²−2)`, denoting sqrt(2). Its literal changes during transport,
while its interpreted polynomial and positive selected root remain the same.

Transport preserves beta, sqrt(2), their sum, product, and the inverse of their
sum, with beta the positive fourth root of 2. Independent quartic-field checks
validate all five values. Additional runtime checks verify that transport
commutes with addition, multiplication and inversion. Old handles retain their
old meaning, while old tickets fail the new full literal context binding,
including the unchanged literal one. Newly bound tickets pass. These tickets
exercise provenance checks only, not a full replay soundness theorem.

The experiment demonstrates two-level feasibility. General predecessor-DAG
recursion, root re-encoding over arbitrary ordered fields, semantic identity
and composition of transport, and cache/certificate transport are still
specified production implementation and proof obligations. The prototype's
fixed positive-root selection is not a general Thom implementation.

## SPEC and implementation boundary

The shared execution contract and all four computational/companion SPEC pairs
state the selected policy, executable sign/NatCast interface, semantic versus
literal equality, validated construction and full-context transport obligations.
The first proof slice is rational selected-root zero/arithmetic/sign, then
inversion/transport and polynomial correspondence. Existing ℝ Sturm results
support it; they do not prove the general non-Archimedean case.

The existing CI job builds the experiments and checks newly emitted full
results with independent exact arithmetic. It does not run scientific timing.
Generic conditional transfer lemmas and successful fixtures are evidence for
the design, not completion of the real-closure libraries. Implementation issues
follow the merged revised contracts and retain their computational, proof,
conformance and performance gates. No worker queue is started by these experiments.
