# Initial generator precision and fixed-field proof cost

This experiment asks whether starting with a tighter generator square reduces
full sign queries and whole proof-build cost. It compares eight and sixty-four
bits for the same positive √2, formula and original target. It does not measure
automatic source preparation, general field reconstruction or nested depth.

## Checked inputs and schedule

The defining polynomial is `X² − 2`. The eight-bit center is `181/128`; the
sixty-four-bit center is `13043817825332782212 / 2^63`.
[Inputs](../bench/HexRCF/ProofProbe/Precision/Inputs.lean) checks both constructors
in the ordinary kernel and proves both coordinate values equal `Real.sqrt 2`.
`sameSentence` transports the high-precision sentence to the exact eight-bit
target. That target expresses `∃ x, x² = √2 ∧ 1 < x ∧ x < 2` through the shared
formula semantics. There is one coefficient, three atoms, variable exponent two
and a degree-four carrier over the degree-two field.

Both arms import the same support module. Indexed retrieval, interval signs and
monic carriers are enabled; reduced-coordinate quotation and combined replay
are disabled. Generator refinement is zero. The candidate uses the proved
sentence equivalence after quoting its high-precision certificate. The shared
constructor, selected-root and equivalence lemmas are warmed dependencies:
their initial elaboration is outside the timed region. The transport application,
native certificate production, quotation and kernel checking are included.

The [collector](../scripts/bench/hexrcf_precision_proofs.py) uses four trial-major,
adjacent rounds in `AB`, `BA`, `AB`, `BA` order. All eight completed arms are
retained, including full compiler output and host context. One automatically
leased CPU, 93, was used with one Lean thread; its SMT sibling was 45. There was
no quiet-core gate, sample exclusion or unchanged rerun. The 120-second arm
timeout is an operational safeguard.

The clean measured source is
[`97733103897449e76138246277355ec446662327`](https://github.com/kim-em/hex-dev/commit/97733103897449e76138246277355ec446662327),
retained on an [evidence branch](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-precision-977331038).
Its base is `e3f05f7177acc3261f9f07c60358024570fd60a2`, containing the prepared
API and window integration on upstream `4f8745e64`. Dependency checkout hashes
are recorded in the report. Results are not pooled with the earlier window or
index studies.

## Observations

| Observation | Eight bits | Sixty-four bits |
| --- | ---: | ---: |
| Median fresh-module time (s) | 12.689 | 12.556 |
| Private olean bytes | 528,440 | 521,984 |
| Median peak RSS (KiB) | 4,036,130 | 4,039,770 |
| Quoted interval sign entries | 123 | 126 |
| Quoted full-query sign entries | 3 | 0 |
| Quoted refinement windows | 0 | 0 |

The median **paired** candidate-minus-reference change is −0.169 seconds.
Individual changes are −0.265, −0.073, −0.310 and +0.025 seconds; the slower
candidate remains in the record. The private file decreases by 6,456 bytes,
while median peak memory increases by 3,640 KiB. The runner reports
`no-comparable-control`. These two-point observations establish no asymptotic
precision claim or general speedup, and justify no default precision change.

Every timed proof audits to `propext`, `Classical.choice` and `Quot.sound`.
A separate [quotation audit](../bench/HexRCF/ProofProbe/Precision/Audit.lean)
inspects the final timed proof artifacts and confirms the entry counts above.
The audit follows reachable declarations from each probe's own module; imported
bodies are leaves. Counts describe distinct quoted syntax, not physical sharing
or expanded work. All final artifact hashes remained unchanged during the audit.
These are final retained-artifact hashes, not hashes captured for every arm.

## Consequences and limits

A tighter initial square removes the three full queries in this fixture without
adding a refinement-window certificate. It requires a different typed root
presentation and checked transport to the original target. This example obtains
that transport from the existing selected-positive-root laws; it does not supply
general transport of coefficient vectors, original divisor identities, context
bindings or nested evidence after rebuilding a field presentation.

The [separate window study](hexrcf-window-proofs.md) preserves the original
presentation and instead checks a contained count-one window. Its timings and
byte differences belong to its own measured source. Neither experiment supports
changing the tactic's default precision or enabling refinement by default.
The source examples in that study already use Horner signs throughout their
solver tables. Broad precision scaling, nested depth and common/repeated-root
cost families remain outside these observations.

- [Full retained report](bench-results/hex-rcf-precision-proofs-977331038-chungus2.json)
- [Incremental samples](bench-results/hex-rcf-precision-proofs-977331038-chungus2.json.samples.jsonl)
- [Quoted evidence and final artifact hashes](data/hexrcf-precision-signs/977331038/audit.json)
- [Complete audit compiler output, JSON encoded](data/hexrcf-precision-signs/977331038/compiler-output.json)

Reproduce from the measured source with
`python3 scripts/bench/hexrcf_precision_proofs.py --output <external-json-path>`.
The wrapper leases a CPU and retains completed arms automatically. The
sixty-four-bit proof is a default build-only example; the eight-bit control and
audit are on-demand modules. None is an executable benchmark root.
