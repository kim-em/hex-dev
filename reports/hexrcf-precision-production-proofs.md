# Initial precision through tactic proof acceptance

> The drivers under `scripts/bench/hexrcf_*.py` and the probe modules under
> `bench/HexRCF/ProofProbe/` that this report cites, other than `Examples` and
> `Registered/`, were removed from `main` after commit `45a4e4e9a4`. Check out
> that commit to rerun them.

This experiment asks whether a tighter initial √2 generator interval helps
when its constructor validity, selected-root identification and target
transport are proved inside the fresh measured module. All four arms call
`Hex.RCF.checkProof`, the tactic's actual proof acceptance routine. The
variable observations justify no default precision change or general speedup.

The [four modules](../bench/HexRCF/ProofProbe/Precision/Full8.lean) prove the
exact same eight-bit existential sentence. They use the same imports, formula,
coefficient and options: one coefficient, three atoms, variable exponent two,
a degree-four carrier over the degree-two field, monic carrier, interval signs
and indexed lookup. Reduced literals, combined replay and generator-window
refinement are disabled. The initial centers are 181/2⁷, 46341/2¹⁵,
3037000500/2³¹ and 13043817825332782212/2⁶³. Each module checks its own square,
identifies its selected value as positive √2 and proves its equivalence with
the original target before producing and quoting a certificate.

`checkProof` shares the proposed term, rejects unsafe or nonstandard proof
dependencies, checks its exact target and creates a fresh synchronous auxiliary
theorem for ordinary-kernel acceptance. The outer theorem uses that reference.
There is one axiom print per timed module; the separate audit checks absence
of a refinement window. The collector rejects any arm source difference other
than the initial square and declaration names. This is a focused fixed-field
experiment rather than the entire user-syntax preparation path. Common imported
laws and the original target are prebuilt; arm-specific constructor and
transport proofs are included. Native evaluation produces data, not evidence.

## Retained source and schedule

The clean measured source is
[`ed0697dacbd808ad1c28270d458929e896aeddca`](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-precision-full-ed0697dac).
The [raw report](bench-results/hex-rcf-precision-full-proofs-ed0697dac-chungus2.json)
and [incremental samples](bench-results/hex-rcf-precision-full-proofs-ed0697dac-chungus2.json.samples.jsonl)
retain all 36 arms and their complete compiler output. Repository and dependency
identities remained unchanged. Six trial-major rounds rotate three adjacent
pairs; each pair occupies each position twice and has three AB and three BA
rounds. No observation was excluded and no unchanged rerun was taken.

The shared host is an AMD EPYC 9455. The runner automatically leased CPU 56
(SMT sibling 8), with one Lean thread. Host activity remains recorded context.
The 120-second per-arm timeout is an operational safeguard.

## Observations

| Pair | Eight-bit median s | Candidate median s | Median paired change s | Private proof bytes | Median peak RSS KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 → 16 | 16.904 | 21.275 | +0.178 | 775392 → 768248 | 4001888 → 4006776 |
| 8 → 32 | 13.417 | 14.193 | +0.566 | 775392 → 768424 | 4000374 → 3993892 |
| 8 → 64 | 13.193 | 13.656 | +0.090 | 775392 → 768784 | 4013438 → 4016604 |

The reference is rebuilt inside every pair. Its marginal median differs across
pairs, and paired medians need not equal differences between marginal medians.
The signed differences, in retained round order, are:

| Pair | Candidate minus reference, seconds |
| --- | --- |
| 8 → 16 | -0.058, -2.141, +2.940, +6.008, +0.413, -11.580 |
| 8 → 32 | +0.833, +0.891, +1.046, +0.298, +0.155, -13.048 |
| 8 → 64 | -2.096, +0.056, -4.532, +0.515, +0.708, +0.123 |

All observations remain included. Each paired median is positive, while every
pair also contains faster candidate observations. These data support neither
a stable precision ordering nor a general performance gain. No pooling or
asymptotic model is used; the runner reports `no-comparable-control`.
All 36 theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Quoted proof structure

The separate [audit](data/hexrcf-precision-signs/ad94c82ee/audit.json) and
[complete compiler output](data/hexrcf-precision-signs/ad94c82ee/compiler-output.json)
are bound to
[retained audit source `ad94c82ee`](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-precision-production-audit-ad94c82ee).
All four probe source hashes match the timed source. Their public and private
olean hashes are unchanged across this audit; these are final artifact checks,
not per-arm captures. The traversal observes a known imported proof containing
a window as a positive control before rejecting windows in all four arms.

| Bits | Interval/full-query entries | Unique expressions | Expanded local-reference nodes |
| ---: | ---: | ---: | ---: |
| 8 | 123 / 3 | 15607 | 649463932852 |
| 16 | 126 / 0 | 15386 | 648889962238 |
| 32 | 126 / 0 | 15392 | 648889962238 |
| 64 | 126 / 0 | 15389 | 648889962238 |

Every arm has 21 reachable local declarations and three distinct conjunction
constructors. Expression equality is `Lean.Expr.eqv`, alpha equivalence with
binder annotations ignored. Imported bodies remain leaves. Expansion counts a
local declaration's type and body at every reference, without reductions or
let substitution. Each literal is one syntax node irrespective of its bit
width. These counts do not measure allocation, physical sharing, kernel work
or serialized byte attribution.

The [24-arm inline-check study](hexrcf-precision-full-proofs.md) uses a different
source and acceptance routine. The [prebuilt-setup comparison](hexrcf-precision-proofs.md)
and [window comparison](hexrcf-window-proofs.md) also have different scopes.
Their observations are retained separately. This study does not measure general
field reconstruction, nested transport or extension depth.

Reproduce on the retained measured source with:

```sh
python3 scripts/bench/hexrcf_precision_full_proofs.py --timeout 120
```
