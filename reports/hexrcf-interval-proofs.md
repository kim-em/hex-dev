# Literal interval sign replay

This comparison selects exact rational Horner signs instead of a full rational
Sturm query for each field element when the generator's authenticated interval
suffices. Inconclusive bounds retain Sturm evidence. Singleton zero is exact
evidence; any wider bound containing zero declines. The same count-one interval,
keys, values, solver, checker and soundness theorem are used in both arms.
Both keep `PolyQuot.reduce` quotation. The probes inspect actual quoted entry
constructors through their local auxiliary declarations.

The named decision is which quotation mode to select in the new implementation.
The reference also runs the interval-preferring builder, then reconstructs
checked Sturm entries for interval hits during quotation. Thus it includes
Horner production/checking, a second `Sturm.prepare`, and host query production
and checking. The paired difference mixes elaboration and kernel savings.
It does not estimate a speedup against the implementation before interval
production, or isolate kernel replay time.

The measured clean source is `3728fa082`, shared host `chungus2`, Lean
`v4.35.0-rc3`, automatically leased CPU 10 with sibling 58 and one Lean thread.
Four trial-major rounds rotate the three pairs and alternate adjacent AB/BA.
All 24 completed arms are retained, without filtering or reruns. Source and
dependency identities are complete and release-quality with no exceptions.

| Goal | Reference median, s | Horner median, s | Median paired Horner minus reference, s |
| --- | ---: | ---: | ---: |
| Further square root | 24.255 | 19.171 | −4.513 |
| Reciprocal square root | 23.360 | 19.185 | −4.752 |
| Cubic coefficient | 38.579 | 24.962 | −13.553 |

All twelve paired margins favor Horner quotation. In trial order, further-root
margins are −3.626, −5.400, −6.656 and −3.512 seconds; reciprocal margins are
−1.122, −5.420, −7.069 and −4.084; cubic margins are −8.278, −18.828, −20.189
and −5.567. The collector reports `no-comparable-control`; these observations
are not a universal speedup or a precise isolated kernel estimate. They support
selecting `rcf.algebraic.intervalSigns=true` by default in this implementation.
The false arm remains a comparison control. Direct reduced-coordinate
quotation remains independently off by default.

| Quoted proof | Reference queries | Horner intervals | Horner queries |
| --- | ---: | ---: | ---: |
| Further square root | 128 | 127 | 1 |
| Reciprocal source authentication | 1 | 0 | 1 |
| Reciprocal goal certificate | 125 | 125 | 0 |
| Cubic coefficient | 125 | 125 | 0 |

The separate syntax audit inspects the completed measured proofs and reachable
auxiliary declarations from each source module; imported library bodies remain
leaves. It finds one distinct literal table expression in the further and cubic
proofs and two in the reciprocal proof. It records hashes of all six proof
artifacts and verifies they were unchanged during the audit. These are literal
entry counts, not expanded work, heap identities or allocation measurements.

Reference/Horner private olean sizes are 844,256/628,448,
889,704/683,424 and 943,008/610,912 bytes. Median reference/Horner peak RSS is
4,828,130/4,834,574, 4,773,878/4,765,764 and 5,136,810/5,136,484 KiB.
All fresh theorem dependency audits contain only `propext`, `Classical.choice`
and `Quot.sound`. Wall times include Lake startup, elaboration, source
preparation/authentication, production, quotation and replay.

The maximum recorded host Lean/Lake count is 87; maximum sibling busy ratio
is 0.7275 and measurement-CPU foreign ratio is 0.0533. These are retained host
context, not reasons to discard completed observations. Absolute timings from
other source snapshots or CPUs are not pooled with this comparison.

Indexed lookup and interval refinement remain outstanding from #10633. Carrier
normalization, rational-literal construction and shared replay work from #10634
are separate decisions. Signed Sturm-chain normalization already uses positive
absolute-leading-coefficient scaling; arbitrary monic scaling is not equivalent.

- [Collector](../scripts/bench/hexrcf_interval_proofs.py)
- [Matched proofs and syntax audit](../bench/HexRCF/ProofProbe/Intervals)
- [Complete results](bench-results/hex-rcf-interval-proofs-3728fa082-chungus2.json)
- [Retained incremental samples](bench-results/hex-rcf-interval-proofs-3728fa082-chungus2.json.samples.jsonl)
- [Entry split and unchanged proof hashes](data/hexrcf-interval-signs/3728fa082/audit.json)
- [Audit compiler output](data/hexrcf-interval-signs/3728fa082/compiler.log)
