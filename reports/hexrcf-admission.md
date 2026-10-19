# RCF proof dependency traversal

The ordinary-proof admission check now shares one visited set across the
constants in a single candidate. It discards the set before returning. Imported
constants still use Lean's exported axiom inventories, including hidden theorem
bodies; current-module declarations visit their types and bodies. The cases for
opaque declarations, inductives, constructors and recursors follow Lean's own
collector.

Both admission checks around the fresh, uncached kernel theorem remain. Unsafe
dependencies, unresolved expressions and disagreement with the original target
remain errors. There is no cross-call cache, budget increase or changed axiom
whitelist. This is an implementation change to the guard, rather than removal
of a guard.

The source implementation is `637da4c86e`; the accompanying record binds its
complete commit identifier and exact sources. Earlier evidence records retain
their original pins. Their integrity checks do not attest this changed checker.

## Functional evidence

The isolated checkout passed the complete original-source quotation with the
unchanged 24-million-node and 60-million-heartbeat limits, consuming 8,651,669
proof nodes. Its fresh importing audit checked 1,193 theorem bodies and 202
definitions, with 1,353 nonempty kernel traces. Its complete axiom closure was
`propext`, `Classical.choice`, and `Quot.sound`; the existing producer and old
fixture exclusions remained enabled. This probe changes only the namespace and
profiling options of the source regression.

The new default test module compares admission with the previous policy on 19
imported, local, opaque, inductive, shared, unresolved and forbidden expressions.
Three further cases reuse one declaration name across restored environments:
valid, forbidden, valid. The forbidden local declaration exists only inside a
fully restored test state. Three raw forbidden expressions and that discarded
fixture are intentional rejection tests, not accepted proof evidence. The
synchronous and asynchronous handler suites also passed in the isolated tree.

The broader 51-target source, rational-compatibility, optional-umbrella and
manual integration build passed. It also rebuilt the original source and
its fresh importing audit with the same node and body counts. The full log
and exact invocation are retained in the source-bound record.

## Cost evidence and limits

A fixed guard-only comparison used an automatically leased CPU on the shared
host, two trials in adjacent AB/BA order and ten checks per arm. A is the
reference policy's separate traversal per constant; B is the new checker. All
completed arms were retained.

| Trial and order | A, total milliseconds | B, total milliseconds |
| --- | ---: | ---: |
| 0, AB | 20.074 | 5.839 |
| 1, BA | 19.695 | 5.572 |

This input has a depth-128 local chain and eight roots sharing that chain. It
establishes a benefit for this dependency graph, not general scaling or a
whole-tactic speedup.

Separate full-source diagnostic profiles identified substantial admission work:
317 seconds with the timing-only original checker and 189 seconds with the
prototype. These are unpaired diagnostic runs. Lean's profiler reports exclusive
categories: nested kernel type checking is separate (237 and 270 seconds), as is
the remaining enclosing quotation work (378 and 388 seconds). Candidate-check
timings alone therefore do not measure all kernel work. No whole-source speedup
is inferred from these profiles. The timing-only build also rebuilt dependencies,
so its service runtime and memory are not a matched comparison.

The final integration's original-source module took 830 seconds. This remains
an expensive fixed-input proof construction; it is a host-specific observation,
not a matched before/after result.

Every Lean/Lake invocation used one serial systemd service with aggregate
`MemoryMax=32G`, `MemorySwapMax=0` and `LEAN_NUM_THREADS=2`. The prototype full
source used 5.7 GiB peak; its separate fresh audit used 6.8 GiB, both without swap.
Setup failures, the explicitly terminated cache-setup attempt, initial negative
test warning and the static negative-probe classification failure are
retained alongside successful runs. They are not reported as successful samples.

This work does not complete #10358's generic source/history assembly, accepted
algebraic completeness, general joint realization, strict compiled record
coverage, remaining manual/API coverage or final review and merge requirements.
