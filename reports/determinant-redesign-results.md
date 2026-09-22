# Determinant redesign experiments

These are diagnostic experiments on one fixed input, not a replacement
architecture or a production speedup claim. The broader questions are in
[the design document](determinant-experiments.md).

## Fixed witness: arithmetic proofs

The input is the retained dense 4×4 matrix with quadratic entries in two
variables. `Determinant.Fixture` runs the existing Hex producer and extracts
its ten row-prefix product identities. The exact operands and results are
retained. Producer, witness and mathematical identities are held fixed.

- **Replay:** existing canonical-list dot products and equality checks,
  accepted by `decide +kernel`.
- **Independent:** Mathlib ring arithmetic, with a fresh atom context for
  each scalar equality.
- **Cached:** one atom context and expression-to-normal-form/proof cache
  across the conjunction. Addition and multiplication reuse the scalar
  arithmetic helpers used by Mathlib's Bird evaluator. No determinant
  evaluator is called.

Replay states Boolean list equalities; the other arms state the corresponding
universally quantified integer polynomial identities. These are equivalent
arithmetic obligations, **not the same complete determinant theorem**.
Replay receives canonical lists; arithmetic receives quoted expressions.
Input conversion and witness production are outside both arms' clocks.

Two adjacent AB/BA pairs were collected per comparison on `chungus2`.
Milliseconds below include tactic execution and the final kernel check.
Auxiliary checks inside the tactic are already inside its clock.

| Comparison | Arm | Tactic median | Final kernel median | Total proof work |
|---|---|---:|---:|---:|
| Replay / independent | Replay | 259.9 | <1 | [259.9, 260.9) |
| Replay / independent | Independent | 238.2 | 107.7 | 345.8 |
| Independent / cached | Independent | 209.9 | 73.4 | 283.3 |
| Independent / cached | Cached | 45.2 | 79.1 | 124.3 |

Every sample is retained. The difference between the two independent-arm
medians is visible rather than pooled away. Caching reduces construction cost
substantially here; it does not reduce the observed final kernel check
relative to the adjacent independent arm.

## Complete proof: the arithmetic win does not survive assembly

`full.py` generates four separately checked lemmas from those same operands:

1. The ten identities, now over an arbitrary commutative ring.
2. Assembly of the existing semantic triangular witness, assuming its three
   nontrivial pivots are nonzero in a domain.
3. Specialization to `MvPolynomial (Fin 2) Int`, certifying nonzero pivots
   by evaluation at zero.
4. Evaluation into the user's commutative ring, including matrix entry
   identification and the supplied target.

The final theorem needs no domain hypothesis on the user's ring. Its axioms
are exactly `propext`, `Classical.choice`, and `Quot.sound`. Zero evaluation
certifies nonzeroness for this fixture; a general implementation must find
and certify a suitable evaluation or use coefficient nonzeroness.

The generator spells entries and the target in canonical term order. Both
production controls prove **that same generated statement**, over an abstract
commutative ring. This differs from the integer microbenchmark and from the
historical report's expression order. Absolute times are not comparable
across those experiments.

| Complete proof arm | Samples | Median proof work, ms |
|---|---:|---:|
| Explicit `norm_det` followed by `ring` | 2 | 171.7 |
| Production Hex `det` | 2 | [590.5, 591.5) |
| Cached witness prototype | 4 | 7042.0 |

There are two adjacent AB/BA pairs for Mathlib/prototype and another two for
Hex/prototype. Every prototype sample includes all four lemmas, with fresh
module kernel checks. No lemma is supplied free from an earlier measurement.

| Prototype component | Median tactic, ms | Median kernel, ms | Distinct proof nodes |
|---|---:|---:|---:|
| Generic arithmetic identities | 95.2 | 450.0 | 56,185 |
| Semantic witness assembly | 1182.1 | 31.8 | 22,109 |
| Polynomial model and nonzero pivots | 999.3 | 29.4 | 2,555 |
| Transport and entry identification | 4198.4 | 56.1 | 35,473 |

Component medians need not sum to the median total. Nodes are counted per
declaration; their sum is not a count after sharing across declarations.
Producer/source-generator costs are excluded, so end-to-end prototype cost
would be higher still. Statement elaboration, imports, serialization and Lake
overhead are excluded. External build observations are retained, but are not
presented as matched import-subtracted performance claims.

This rejects the prototype as a competitive complete backend. Most cost is
in elaborator work, but even its arithmetic component alone is slower than
Mathlib's entire proof here. Ordinary generic ring proofs are not yet an
adequate replacement for list replay.

The next discriminating changes should retain this witness and statement:

- Replace repeated tactic-driven matrix transport with a reusable expression
  transport theorem and explicit applications. The existing
  `Hex.Kronecker.Expr.map_denote` is an available building block.
- Compare opaque, separately checked reusable arithmetic certificates with
  the current conjunction proof. Include every auxiliary check; do not
  measure fragments after a whole-proof check.
- Compare schedules under common arithmetic after accounting for construction
  costs. The generic arithmetic kernel gap also questions the witness itself.

No production dispatch or SPEC contract changes. Cached arithmetic remains
an experimental candidate; a replacement architecture is not selected.

## Failures, protocol and verification

Initial generated statements left literal exponent types implicit. Two builds
hit the 60-second ceiling; each batch stopped immediately. A bounded diagnostic
then failed in `synthesize pending MVars`, before the tactic, with extensive
`HPow`/`HAdd` inference. Explicit `Nat` exponent annotations allowed completion.
These are harness failures, not mathematical proof-method failures.

Profiler threshold zero was also replaced with 1 ms. A single-identity
diagnostic changed both heartbeat/profiler settings, so it did not isolate
profiling as the cause. Below-threshold kernel checks are reported as
intervals, never silently as zero cost.

All batches are serial, automatically CPU-leased, limited to 60 seconds per
build and four minutes per batch. The five retained batches, including failed
ones, consume about **230 seconds** total. Small development/diagnostic builds
are retained separately. No larger input followed a timeout, no memory cap
was imposed, and no background service or CI monitor was installed.

The fixture producer is Mathlib-free. Proof experiments are build-only Lean
modules. `Determinant.Audit` builds successfully, checks the complete theorem's
axioms, counts proof nodes, and tests generic-ring arithmetic and rejection
of unequal normal forms. Python generators pass syntax compilation.

[Raw sources, samples, errors, host context and hashes](bench-results/determinant-redesign/)
and [reproduction commands](../experiments/Determinant/README.md) are retained.
