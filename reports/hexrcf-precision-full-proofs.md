# Initial precision with construction and transport included

This fixed-field experiment compares 8, 16, 32 and 64 initial generator bits
for the same positive √2 and the exact same existential target. Every fresh
module checks its own square, proves its selected value is √2, proves the
sentence equivalence, produces a certificate and checks the quoted proof in
the ordinary kernel. It asks whether the tighter initial square remains useful
when these arm-specific proofs are included. The mixed, variable observations
justify no default precision change or general speedup.

The [four modules](../bench/HexRCF/ProofProbe/Precision/Full8.lean) use the
same imports, formula, coefficient and options: one coefficient, three atoms,
variable exponent two, degree-four carrier over the degree-two field, monic
carrier, interval signs and indexed lookup; reduced literals, combined replay
and generator-window refinement are disabled. Their centers are respectively
181/2⁷, 46341/2¹⁵, 3037000500/2³¹ and 13043817825332782212/2⁶³. Validity and
positive-root identification are kernel-checked. Each arm proves the original
eight-bit sentence through its own equality to that selected root.

This source explicitly checks the complete inline proof with
`Lean.Meta.checkWithKernel`, then supplies it inline to the outer theorem,
whose declaration checks it again. It does not use the production tactic's
sharing and fresh-auxiliary-theorem acceptance routine. The timings include
both full-term checks, so they are not measurements of the user tactic's
proof-acceptance path.

The common imported baseline is prebuilt, including the original eight-bit
target and generic selected-root laws. Arm-specific constructor checks, selected
identity and equivalence are declared inside each timed module. The timing
includes their elaboration, native proposed certificate production, quotation,
transport application and kernel checking. It still excludes import startup
work in the warmed dependencies and does not implement general coefficient,
context or nested-evidence transport after reconstructing a field.

## Retained source and schedule

The clean measured source is
[`2436b6ab047a33ab10791062edf2935aee1cc53d`](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-precision-full-2436b6ab0),
based on `312e8eff15b718afb6b89e64a15a16d47cdb68bb`. Repository/dependency
identities and source hashes are in the
[complete raw report](bench-results/hex-rcf-precision-full-proofs-2436b6ab0-chungus2.json)
and [incremental samples](bench-results/hex-rcf-precision-full-proofs-2436b6ab0-chungus2.json.samples.jsonl).
The collector rotates the three adjacent pairs in four trial-major rounds,
alternating AB/BA. All 24 completed arms are retained, including complete
compiler output. No sample was excluded and no unchanged rerun was taken.
The shared-host runner automatically leased CPU 14 (SMT sibling 62), with one
Lean thread. Each pair has two AB and two BA rounds, but its positions across the three
pairs are not evenly balanced: rotation offsets are 0/1/2/0. These results
support within-pair observations, not a cross-pair precision ordering.
Host activity is recorded context. The 120-second per-arm timeout
is operational; it is not a mathematical or performance budget.

## Observations

| Pair | Eight-bit median s | Candidate median s | Median paired change s | Private proof bytes | Median peak RSS KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 → 16 | 16.256 | 15.212 | -0.280 | 773320 → 766176 | 3991220 → 3989058 |
| 8 → 32 | 18.560 | 14.701 | -2.804 | 773320 → 766352 | 3969008 → 3993482 |
| 8 → 64 | 13.885 | 16.417 | +0.022 | 773320 → 766728 | 3982194 → 3994218 |

The repeated eight-bit module is rebuilt separately within each adjacent pair;
its marginal median therefore differs across pairs. Paired changes need not
equal differences between marginal medians. The 16-bit candidate is faster in
three pairs and slower by 6.246 seconds in one. All four 32-bit pairs favor the
candidate, including large −7.373 and −5.024 second differences. The 64-bit pair
splits two/two, including a +5.466 second difference. All remain in the report.
No pooling, fitted scaling model or stable magnitude claim is made. The runner
reports `no-comparable-control` for each pair.

Every timed theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`. Native evaluation supplies proposed data; it supplies no proof
premise. Each fresh module kernel-checks the final same-target proof and asserts
that it emits no refinement window. This experiment is separate from the
[prebuilt-setup precision comparison](hexrcf-precision-proofs.md) and the
[window comparison](hexrcf-window-proofs.md); their source pins and samples
are not combined. It does not measure arbitrary source preparation, tower
extension depth or common/repeated-root regimes.

The separate [quoted-proof audit](data/hexrcf-precision-signs/a00574152/audit.json)
at [retained audit source `a005741521`](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-precision-full-audit)
verifies that all four probe source hashes match the timed source. It retains
[complete compiler output](data/hexrcf-precision-signs/a00574152/compiler-output.json)
and final artifact hashes; these are after-audit hashes, not per-arm captures.
The 8-bit arm has 123 interval/3 full-query entries. All three higher-width arms
have 126 interval/0 full-query entries, and none has a refinement window.
All four have 20 reachable local declarations and three distinct conjunction
constructors. Unique expression counts are 15,606 / 15,385 / 15,391 / 15,388.
Expanded local-reference counts are 649,463,932,850 at eight bits and
648,889,962,236 at each other width. Each literal counts as one syntax node,
so expansion does not measure arithmetic cost as its bit width grows.
Expression equality is alpha equivalence with binder annotations ignored;
imported bodies are leaves. Expansion substitutes a local declaration's type
and body at each reference without reductions or let substitution. These are
syntactic counts, not allocation, serialized size, physical sharing or kernel
execution counts. Their scope differs from the prebuilt-setup audit: local
constructor and transport declarations are included here.

Reproduce the fixed comparison on its retained source with:

```sh
python3 scripts/bench/hexrcf_precision_full_proofs.py --timeout 120
```
