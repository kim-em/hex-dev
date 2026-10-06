# Fixed-field carrier normalization comparison

> The drivers under `scripts/bench/hexrcf_*.py` and the probe modules under
> `bench/HexRCF/ProofProbe/` that this report cites, other than `Examples` and
> `Registered/`, were removed from `main` after commit `45a4e4e9a4`. Check out
> that commit to rerun them.

This experiment tests #10634's carrier-normalization proposal. The candidate
uses the existing `DensePoly.monicize` operation on the derivative-gcd quotient.
It preserves the original polynomial product and checks both radical
identities, including the scalar retained in the quotient. It does not
normalize every intermediate gcd or remainder. Signed Sturm chains retain
their existing positive-scaling convention.

Both arms use the same imports, goals, solver, reduced-coordinate setting,
interval signs, split replay, literal checker and soundness theorem. The
measured source is clean `43fe6690cf3ccafe5055293ab265b143392bcb23` on
`chungus2`, with one Lean thread on automatically leased CPU 58 (SMT sibling
10). Four trial-major rounds rotate the three pairs, measure adjacent arms and
alternate AB/BA. All 24 arms completed and are retained without filtering.

| Goal | Raw median (s) | Monic median (s) | Median paired change (s) |
| --- | ---: | ---: | ---: |
| Further square root | 18.245 | 16.953 | −1.300 |
| Reciprocal coefficient | 17.854 | 16.763 | −1.073 |
| Cubic coefficient | 19.938 | 17.805 | −2.108 |

All twelve paired changes favor normalization on these workloads. There is no
comparable null control, so the harness reports `no-comparable-control`. The
observations are full fresh-module Lake build costs, including construction,
quotation and replay; they do not isolate gcd or kernel time or establish a
general asymptotic improvement.

Private olean sizes decrease from 628,448 to 611,024 bytes (further root),
683,656 to 669,616 (reciprocal), and 610,912 to 594,032 (cubic). Median peak RSS
decreases from 4,822,286 to 4,640,218 KiB, 4,767,354 to 4,602,864 KiB, and
5,126,524 to 4,766,120 KiB respectively. These sizes do not establish physical
sharing or an expanded-work count.

Every fresh-module proof audit contains only `propext`, `Classical.choice` and
`Quot.sound`. Both arms require actual interval entries and the same
`PolyQuot.reduce` quotation constructor. Separate conformance exercises
negative leading coefficients, repeated and common roots, leading cancellation,
zero and constant products, and context/quotient corruption. An exact producer
fixture distinguishes the normalized core from the raw core. The proved
`buildMonic_checked`, `buildMonic_core` and `buildMonic_monic` laws bind successful
proposals to the existing checker and normalized core. `buildMonic_success`
and `buildMonic_success_real` prove actual producer progress for nonzero inputs
under zero-reflecting, operation-preserving characteristic-zero semantics;
`buildMonic_squarefree` proves the interpreted core is squarefree. Fresh ordinary
kernel audits cover these laws and a rational-base instantiation. The measured
comparison and these proofs support `rcf.algebraic.monicCore=true` as the default.
The false arm remains a comparison control. A rejected proposal remains
terminal, without solver fallback. This does not prove total common-field
authentication or bounded root-isolation success for the entire tactic.

The maximum recorded Lean/Lake process count is 6, SMT sibling busy ratio
0.0123, and measurement-CPU foreign ratio 0.00188. These are retained host
context, not exclusion criteria. Absolute times from other CPUs or snapshots
are not pooled with this comparison.

The [full report](bench-results/hex-rcf-carrier-proofs-43fe6690c-chungus2.json)
and [incremental records](bench-results/hex-rcf-carrier-proofs-43fe6690c-chungus2.json.samples.jsonl)
retain source/import hashes, package identities, all arms, compiler output,
memory and artifact sizes. Reproduce from a clean checkout with
`python3 scripts/bench/hexrcf_carrier_proofs.py --output <external-json-path>`.
The wrapper automatically leases a CPU without waiting for a quiet host.
Dependencies alone are warmed. These Mathlib-importing probes are build-only
members of the on-demand target, with no new CI job or runtime benchmark.

The comparison predates indexed sign retrieval. Its probes now explicitly pin
`rcf.algebraic.indexSigns false`; this later pin preserves the measured linear
lookup mode while changing current source hashes. The archived commit and
hashes remain the identities of the retained experiment.
