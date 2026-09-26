# Compact quotient relations in determinant proofs

The experimental `relations_bird` backend preserves compact quotient monomials
and expands selected terms when their multiplicative signatures indicate a
possible merge. It uses the same cached division-free Bird recurrence and compact
proof constructors as the opaque-quotient control. No matrix-family selection or
call to `norm_det` is part of the candidate.

## Representation and proof boundary

Entries are normalized with numeric denominators as coefficients and symbolic
quotients as atoms. Multiplicative signatures record factors, inverse factors and
natural exponents, ignoring scalar coefficients. A factor and its inverse are
never cancelled: symbolic denominators may be zero. Signatures only select work;
all changes are certified by the existing scalar normalization theorems and
checked in the kernel. False collisions cannot manufacture an equality, while
missed collisions can cause a slower second comparison or failure to close.

When signatures collide, the implementation walks `ExProd` directly. It expands
only the selected terms, caches atom/product certificates, and retains the
unselected sum tail once no selected term remains. It does not simplify inside
opaque atoms just to turn a monomial back into syntax. The determinant and target
share a final signature comparison with separate selections for each side, so partial cancellation does not force them
into incompatible representations. Entries are checked before entering the
recurrence cache, allowing a newly proved zero to enable existing zero pruning.

A sufficient scalar independence check avoids useless search: each compact atom
must have a factor absent from every other atom. Its verdict is invalidated when
the atom table grows. This is a property of scalar representations, not matrix
rank, sparsity or dimensions. Sum-tail indices use persistent trie maps and sets, sharing branches across
adjacent tails instead of copying hash-table bucket arrays. Factor signatures
are cached. The audits check that caches are populated and reused.

A work limit counts distinct sum-tail visits. A separate local heartbeat ceiling
covers the entire backend, including any stronger final scalar comparison; it
never increases the caller's remaining allowance. Exhaustion declines explicitly.
The final comparison is scalar normalization, not a determinant tactic fallback.

## Experimental controls

The [retained corpus](bench-results/determinant-relations/) uses serial fresh
modules and two adjacent AB/BA pairs per completed case. It has a ten-minute
measurement allowance and at most 60 seconds per invocation; actual selected
ceilings are recorded per case. Completed samples and failures are retained.
The phases have separate source snapshots and must not be pooled as unchanged
runs. These exploratory pairs do not satisfy the six-pair shipping bar.

The initial independent-quotient 4×4 comparison lost both pairs: 0.575s versus
Mathlib's 0.496s. The initial product-denominator 4×4 case won both: 1.021s versus
1.450s. Partial-cancellation audits exposed representation gaps not tested by
those two extremes; the revised implementation compares targets jointly and
handles powers, signs and zero entries explicitly.

A 6×6 control against `fresh_bird` (the same opaque-quotient evaluator without
the hook) attributes approximately 0.9s of overhead to signature search: tactic
samples were 1.332/1.379s versus 0.431/0.495s. Kernel and sharing costs did not
show the corresponding increase. A cache integration also bypassed insertion via
early returns; its source and measurements are retained. Corrected insertion,
reuse audits and the scalar independence check eliminate scans on this input.
The final diagnostic reports 30 compact atoms, zero signature visits and zero
expansion proofs, with tactic samples 0.683/0.677s versus 0.704/0.796s for the
opaque control. Host timing variation remains visible and is not filtered.

## Last measured source: paired comparisons

Median complete declaration seconds; all completed pairs are retained in the
`final` directory. These samples precede the persistent-trie, separate-selection
and diagnostic fixes described above. Those fixes have correctness validation
but have not been remeasured; the table is not a speed claim for the final source.

| Input | Relations | Mathlib | Pair directions |
|---|---:|---:|---|
| Identity plus rank one with product denominators, 4×4 | 0.193 | 0.772 | Both favor relations |
| Same construction, 5×5 | 0.306 | 6.182 | Both favor relations |
| Independent quotients, dependent row, 6×6 | 4.355 | 4.524 | Split |
| Same input, permitted unchanged repeat | 4.620 | 5.212 | Split |
| Original integer quadratic 4×4 issue fixture | 2.057 | 2.240 | Both favor relations |
| Rank one with product denominators, 5×5 | 0.245 | 3.095 | Both favor relations |

The independent-quotient result is near parity, not a reliable win. Each of its
two batches contains one slower candidate sample; the unchanged repeat does not
erase the first batch. The partial-cancellation case wins both pairs at each
tested dimension. No larger cases were run after these focused checks.

## Limits and migration

This implements the proposed scalar mechanism, not a complete field normalizer.
The factor parser is conservative around polynomial numerators and symbolic
exponents. Some equivalent quotients still need the bounded second scalar
comparison. The independence test is sufficient, not necessary; failure of the
test says nothing about whether a useful identity exists. Cache memory and
worst-case scan/expansion costs need broader production qualification.

The new rank-one-plus-diagonal fixture exercises partial cancellation and a
nonzero target `det(I + u*vᵀ) = 1 + vᵀ*u`. Quotient expressions in the vectors are
total, including at zero denominators. This target is an explicit algebraic
fixture, not an independently expanded polynomial oracle; both proof arms check
it. Neither generator structure nor its formula is used by the candidate.

Retain compact proof constructors and this scalar mechanism as the experimental
basis for supplied equalities. Production migration still requires the agreed
SPEC/API changes, result-producing and reversed-goal coverage, schedule comparisons
with common scalar representations, and six-pair shipping qualification. The
[replacement proposal](determinant-redesign-proposal.md) remains the migration
contract; fixed-ring value algorithms and numeric certificate routes are unchanged.

## Validation

The measurement corpus contains 13 cases, 52 completed samples and 143 source
snapshots, using 512.4 seconds (8m32s) of the ten-minute allowance. The
[evidence verifier](../experiments/Determinant/verify_relations.py) checks source
digests, AB/BA order, permitted theorem axioms, cleanup and cumulative time.
Each source variant has its own generated inventory in the retained corpus.

The audit suite checks generic rings, rational coefficients, total field division,
false-target rejection, first-pass cancellation, target-driven atom-table growth,
entry-cache zero pruning, cache insertion/reuse and heartbeat limits. Accepted
proofs use only `propext`, `Classical.choice` and `Quot.sound`. Full-build and audit
logs are retained under `validation/`; the full build has existing unrelated
`sorry` warnings, while this change introduces none. Runner guards, DAG, phase-4
and release-manifest checks also pass. The earlier experiment corpus remains
verifiable against its recorded revision `81d4a0e86`.
