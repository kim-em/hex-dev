# Fixed-field certificate replay comparison

> The drivers under `scripts/bench/hexrcf_*.py` and the probe modules under
> `bench/HexRCF/ProofProbe/` that this report cites, other than `Examples` and
> `Registered/`, were removed from `main` after commit `45a4e4e9a4`. Check out
> that commit to rerun them.

This experiment tests #10634's proposal to check the certificate in one kernel
declaration. Both arms use the same imports, goal, solver, coordinate quotation,
interval signs, literal checker and soundness theorem. The reference checks
separate conjuncts; the candidate keeps the Boolean checker together and uses
one `decide +kernel` goal. Source authentication and the final handler proof
check remain separate. This does not make the entire tactic one kernel check.

The measured source is clean `f223f9abf25ede4a658edf6f2c5c1422e14b98b4` on
`chungus2`, with one Lean thread on automatically leased CPU 40 (SMT sibling
88). Four trial-major rounds rotate the three pairs, measure adjacent arms and
alternate AB/BA. All 24 arms completed and are retained without filtering.
Both arms used raw carriers, before the monic option existed. The probes now
explicitly pin `rcf.algebraic.monicCore false`; that pin was added after the
measurement and does not change its carrier mode. This comparison is not a
measurement of the current monic default.

| Goal | Split median (s) | Combined median (s) | Median paired change (s) |
| --- | ---: | ---: | ---: |
| Further square root | 18.407 | 18.617 | +0.272 |
| Reciprocal coefficient | 18.205 | 18.558 | +0.285 |
| Cubic coefficient | 20.252 | 20.314 | +0.058 |

Ten of the twelve paired changes favor the reference. There is no comparable
null control, so the harness reports `no-comparable-control`. These observations
do not establish a speedup or an isolated kernel estimate. They do not justify
enabling combined replay by default. `rcf.algebraic.singleReplay` remains false;
the true mode is retained as a comparison control.

Private olean sizes decrease from 628,448 to 551,976 bytes (further root),
683,656 to 639,472 (reciprocal), and 610,912 to 534,648 (cubic). Median peak RSS
increases from 4,818,092 to 5,476,988 KiB, 4,762,096 to 5,404,474 KiB, and
5,125,012 to 5,896,636 KiB respectively. Smaller proof files do not imply lower
replay time or memory. No physical-sharing or expanded-work reduction is
claimed from these sizes.

Every fresh-module proof audit contains only `propext`, `Classical.choice` and
`Quot.sound`. The probes require actual interval entries and the same
`PolyQuot.reduce` coordinate constructor in both arms. Separate conformance
proofs exercise combined replay on universal, existential, guarded and
half-open-domain goals. With combined replay enabled, they also check false
verdict and zero-divisor refusals before replay. Those refusals do not test a
failing combined kernel replay. The option
changes proof assembly, not the trusted checker or solver dispatch.

The maximum recorded Lean/Lake process count is 9, SMT sibling busy ratio
0.0874, and measurement-CPU foreign ratio 0.00107. These are retained host
context, not exclusion criteria. Absolute times from other source snapshots or
CPUs are not pooled with this comparison.

The [full report](bench-results/hex-rcf-replay-proofs-f223f9abf-chungus2.json)
and [incremental records](bench-results/hex-rcf-replay-proofs-f223f9abf-chungus2.json.samples.jsonl)
retain the source/import hashes, package identities, all arms, compiler output,
memory and artifact sizes. Reproduce from a clean checkout with
`python3 scripts/bench/hexrcf_replay_proofs.py --output <external-json-path>`.
The wrapper automatically leases a CPU; it does not wait for a quiet host.
Dependencies alone are warmed. These Mathlib-importing probes are build-only
members of the on-demand target, with no new CI job or runtime benchmark.

Indexed lookup and generator-interval refinement remain separate work. Carrier
normalization has its own retained comparison in
[the carrier report](hexrcf-carrier-proofs.md). Signed Sturm chains already use positive scaling; making them
arbitrarily monic can change their sign semantics. This comparison does not
evaluate those changes.

The comparison predates indexed sign retrieval. Its probes now explicitly pin
`rcf.algebraic.indexSigns false`; this later pin preserves the measured linear
lookup mode while changing current source hashes. The archived commit and
hashes remain the identities of the retained experiment.
