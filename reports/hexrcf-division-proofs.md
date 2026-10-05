# Fixed-field source conversion proof cost

> The drivers under `scripts/bench/hexrcf_*.py` and the probe modules under
> `bench/HexRCF/ProofProbe/` that this report cites, other than `Examples` and
> `Registered/`, were removed from `main` after commit `45a4e4e9a4`. Check out
> that commit to rerun them.

The question is whether direct `QAdjoin.toAlgebraicNumber` conversion adds
quotation cost over `Coefficients.ofField` for the same cubic reciprocal.
Both fresh modules prove `∀ x : ℝ, x / α = β * x`, where the selected root
`α` satisfies `α³ − α − 1 = 0` and `β` is the coordinate `α² − 1`.
They use identical imports and shared checked source definitions. The adapter
searches once for their single selected generator, authenticates both source
coordinates, checks the original divisor with the literal irreducibility
witness instantiated, and quotes the quotient's multiplication identity.
The source syntax is linear in `x`; after exact specialization the equality
atom is zero. This probe does not measure a nonzero carrier's root search.

The retained run uses source `b10ded7899be3f1f7d0fb88255b5bb070eb2ae05`,
Lean `v4.35.0-rc3`, shared host `chungus2`, automatically leased CPU 18 and one
Lean thread. Four adjacent alternating AB/BA rounds retain all eight completed
arms, their complete compiler output, source/dependency identities and host
context. Each actual quoted theorem has only `propext`, `Classical.choice`
and `Quot.sound` in its transitive axiom inventory.

| Observation | Wrapped conversion | Direct conversion |
| --- | ---: | ---: |
| Median fresh-module build | 10.441 s | 10.443 s |
| Median peak RSS | 3.29 GiB | 3.29 GiB |
| Public olean bytes | 51,248 | 51,256 |
| Private olean bytes | 603,000 | 603,000 |

Fresh-module build times include Lake startup and replay of dependencies,
as well as the target module's proof construction.

The median paired direct-minus-wrapped margin is +0.013 s, with individual
margins from −0.045 s to +0.071 s. These four observations do not resolve a
cost difference. They show that both source forms produce ordinary proofs
with the same private serialized artifact size for this input. Olean size
includes metadata and is not a count of proof or evidence DAG nodes.
The source-presentation sign table and target sign table are checked separately;
this measurement includes both checks and does not isolate their costs.
There is no import-only arm, numerical algorithm benchmark, parameter sweep
or general completeness claim. Absolute times are observations on this shared
host. Every completed sample is retained; there is no unchanged rerun.

A separate retained snapshot at source
`b0c5837926d565d350b56b7d0c822bd68283316e` uses the same four-pair schedule on
CPU 79: medians 11.22/11.07 s, paired median +0.09 s, paired range
−1.04 to +0.59 s, 3.30 GiB median RSS in both arms and 603,016 private olean
bytes. It predates the stricter guard preflight and alias/dispatch changes.
Later routing and environment-cleanup changes are outside these measured source
identities. These independently scheduled snapshots compare conversion forms within each
snapshot. They do not estimate the cost of changing guard validation or claim
that one source revision is faster than the other.

Reproduce with `python3 scripts/bench/hexrcf_division_proofs.py` from a clean
checkout. The runner leases a CPU, builds imports before timing and rebuilds
each proof module adjacently through Lake.

- [Instantiated-guard raw results](bench-results/hexrcf-division-b10ded789-chungus2.json)
- [Instantiated-guard completed arm records](bench-results/hexrcf-division-b10ded789-chungus2.json.samples.jsonl)
- [Earlier raw results](bench-results/hexrcf-division-b0c583792-chungus2.json)
- [Earlier completed arm records](bench-results/hexrcf-division-b0c583792-chungus2.json.samples.jsonl)
