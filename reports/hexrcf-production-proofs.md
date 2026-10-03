# Fixed-field root-section proof cost

This experiment investigates the proof-construction cost of two actual algebraic
`rcf` goals: sections separated by `2^-132`, and a further algebraic root with
`x² = √2` and `1 < x < 2`. Each fresh module uses identical imports and emits an
ordinary-kernel proof. These are different formulas, so their adjacent comparison
does not isolate precision, degree or root-count scaling.

A development build of the close-section goal exposed repeated canonical
conversion of coordinate values while computing search signs. Search now captures
a prepared rational Sturm domain as data and applies Tarski queries at the same
selected root. The direct isolation attempt uses depth 256; canonical fallback
uses cached roots and doubles enclosure precision. The tactic bounds refinement
and keeps exhaustion distinct from invalid replay. The total library producer
has its separate acceptance and progress proofs. Quotation checks literal
evidence and does not repeat root isolation.

The current retained snapshot is source
`cdaac619c66a8874afb731352ef1caa78f304917`, Lean `v4.35.0-rc3`, shared host
`chungus2`, automatically leased CPU 17 and one Lean thread. Four adjacent
alternating AB/BA rounds retain all eight completed arms, compiler output,
source/dependency identities and host context. The actual quoted proofs use only
`propext`, `Classical.choice` and `Quot.sound`.

| Observation | Close sections | Further root |
| --- | ---: | ---: |
| Median fresh-module build | 10.502 s | 22.688 s |
| Individual builds | 10.209, 10.945, 10.722, 10.282 s | 22.203, 22.875, 22.500, 23.158 s |
| Median peak RSS | 3.46 GiB | 4.59 GiB |
| Public olean bytes | 54,144 | 53,264 |
| Private olean bytes | 615,784 | 837,480 |

The median paired further-minus-close margin is 11.962 s. Fresh-module times
include Lake startup, dependency replay and proof construction. They do not
separate abstraction, elaboration, quotation and replay. The additional serialized
size of the further-root case is an observation, not a count of evidence DAG
nodes. Both cases have one selected degree-two generator; the frontend may
abstract several compound coefficient expressions. Expanded versus shared work,
independent parameter ladders and joint nested realization remain unmeasured here.

A separate complete snapshot at source
`9a74987498942638c84a05907fd7bd129f98be94` uses the same four-pair schedule on
CPU 30: median times 16.469/35.043 s, median paired margin 17.366 s, median RSS
3.47/4.58 GiB and identical serialized sizes. This snapshot predates captured
prepared-sign data and finite tactic refinement budgets. Its raw metadata key
`source_coefficients: 1` counts selected generators, not frontend coefficient
expressions; the current runner calls it `selected_generators`.

These source revisions were measured separately and do not form an adjacent
before/after experiment. No performance improvement is inferred across them.
Host context is retained: the earlier snapshot observed up to 82 Lean/Lake
processes and SMT-sibling busy ratio 0.926; the current snapshot observed up to
24 and ratio 0.088. Every completed arm is retained. Neither snapshot has an
unchanged rerun or discarded sample. Absolute times are shared-host observations,
not scientific resource bounds or a full extension performance attestation.

Reproduce with `python3 scripts/bench/hexrcf_production_proofs.py` from a clean
checkout. The runner leases a CPU, builds imports before timing and rebuilds each
proof module adjacently through Lake. It adds no Mathlib-importing executable
benchmark.

- [Current raw results](bench-results/hex-rcf-production-proofs-cdaac619c66a-chungus2.json)
- [Current completed arm records](bench-results/hex-rcf-production-proofs-cdaac619c66a-chungus2.json.samples.jsonl)
- [Earlier raw results](bench-results/hex-rcf-production-proofs-9a7498749894-chungus2.json)
- [Earlier completed arm records](bench-results/hex-rcf-production-proofs-9a7498749894-chungus2.json.samples.jsonl)
