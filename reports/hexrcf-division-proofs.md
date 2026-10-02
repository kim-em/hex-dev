# Fixed-field source conversion proof cost

The question is whether direct `QAdjoin.toAlgebraicNumber` conversion adds
quotation cost over `Coefficients.ofField` for the same cubic reciprocal.
Both fresh modules prove `∀ x : ℝ, x / α = β * x`, where the selected root
`α` satisfies `α³ − α − 1 = 0` and `β` is the coordinate `α² − 1`.
They use identical imports and shared checked source definitions. The adapter
searches once for their single selected generator, authenticates both source
coordinates, checks the original divisor, and quotes the quotient's
multiplication identity. The source syntax is linear in `x`; after exact
specialization the equality atom is zero. This probe does not measure a
nonzero carrier's root search.

The retained run uses source `b0c5837926d565d350b56b7d0c822bd68283316e`,
Lean `v4.35.0-rc3`, shared host `chungus2`, automatically leased CPU 79 and one
Lean thread. Four adjacent alternating AB/BA rounds retain all eight completed
arms, their complete compiler output, source/dependency identities and host
context. Each actual quoted theorem has only `propext`, `Classical.choice`
and `Quot.sound` in its transitive axiom inventory.

| Observation | Wrapped conversion | Direct conversion |
| --- | ---: | ---: |
| Median fresh-module build | 11.22 s | 11.07 s |
| Median peak RSS | 3.30 GiB | 3.30 GiB |
| Public olean bytes | 51,248 | 51,256 |
| Private olean bytes | 603,016 | 603,016 |

The median paired direct-minus-wrapped margin is +0.09 s, with individual
margins from −1.04 s to +0.59 s. These four observations do not resolve a
cost difference. They show that both source forms produce ordinary proofs
with the same private serialized artifact size for this input. Olean size
includes metadata and is not a count of proof or evidence DAG nodes.
The source-presentation sign table and target sign table are checked separately;
this measurement includes both checks and does not isolate their costs. The
recorded source predates the later alias/dispatch changes and the check that
instantiates each divisor guard with its literal irreducibility witness before
search. These observations are tied to the recorded source, not timings of the
final PR head or of the newly accepted source forms.
There is no import-only arm, numerical algorithm benchmark, parameter sweep
or general completeness claim. Absolute times are observations on this shared
host. Every completed sample is retained; there is no unchanged rerun.

Reproduce with `python3 scripts/bench/hexrcf_division_proofs.py` from a clean
checkout. The runner leases a CPU, builds imports before timing and rebuilds
each proof module adjacently through Lake.

- [Raw results](bench-results/hexrcf-division-b0c583792-chungus2.json)
- [All completed arm records](bench-results/hexrcf-division-b0c583792-chungus2.json.samples.jsonl)
