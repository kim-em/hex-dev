# Relation prototype review resolution

The first review is retained in [opus-review.txt](opus-review.txt).

- Determinant and target monomials now share a collision check, covered by
  `partialMerge` with the stronger scalar pass disabled.
- Signatures handle natural exponent syntax and signs, and avoid splitting
  polynomial quotient numerators the bounded evaluator would refuse. Signature
  precision remains an optimization limitation, never equality evidence.
- Selected products are walked directly; no `RingNF.cleanup` runs inside opaque
  atom interiors on this path. Atom/product proofs are cached.
- Rewriting returns an unchanged tail when no selected terms remain. Sum-tail
  indices are cached too, with explicit insertion/reuse tests after a detected
  early-return bypass.
- Entry normalization occurs before caching, allowing relation-proved zeros to
  trigger the existing recurrence pruning. Redundant product scans were removed.
- The hook's subject-preservation requirement is documented. Returned certificates
  remain kernel-checked; the callback cannot establish an unproved equality.
- The private-factor scalar test skips collision search when the factor map is
  injective on the current compact atoms. Atom-table growth invalidates its verdict.
- Tests require zero expansion proofs for independent quotients and positive
  expansion/cancellation for quotient identities. False targets, zero denominators,
  powers, signs, partial merging, work-budget and heartbeat-budget rejection are
  covered.
- A rank-one-plus-diagonal fixture tests partial cancellation and a nonzero target.
  The separate `fresh` control isolates hook overhead, including profiler samples.
- The work budget intentionally declines when exhausted. An additional local
  heartbeat ceiling bounds the backend and final comparison, even if the outer
  `maxHeartbeats` option is zero. Silent continuation into unbounded expansion was
  not adopted.
- Legacy Boolean controls remain for reproducing prior experimental arms; the new
  tactic entry points use named arguments. A production scalar-policy interface
  remains part of migration, not a new public experimental API.
- The generated `AdversarialSample*.lean` files are temporary measurement inputs
  and are removed by the runner. Only archived text snapshots are retained.

## Final review

The [final review](opus-final-review.txt) found no soundness blocker. Its
substantive changes are implemented and correctness-tested:

- Sum-tail indices now use `PersistentHashMap` and `PersistentHashSet`, avoiding
  copy-on-write bucket arrays at every retained tail.
- Target alignment maintains per-side selections, including propagation when an
  internally colliding monomial also appears on the other side. Diagnostic
  rewrite counts include alignment and are emitted after comparison.
- `targetGrowth` closes with the second pass disabled. A separate meta audit
  inspects the entry cache before recurrence and requires the normalized entry
  to be zero. Budget audits check exact work/heartbeat decline messages and preservation of
  a smaller outer heartbeat allowance. Target-growth diagnostics report four
  rewrites, exercising alignment counters after the comparison.
- The stable AtomM-prefix requirement and the shared atom/product certificate
  cache are documented in code. The stronger scalar comparison is explicitly
  described as heartbeat-bounded rather than sum-visit-bounded.

The reported generated sample was live during review, not a stale artifact:
its measurement finished normally and the runner removed it. The evidence
verifier confirms that no generated samples remain. The unrelated `.lock` file
is excluded from the commit.

Signature precision for unsupported syntax and atom-table rescans after a failed
independence test remain performance limitations. No soundness depends on these
hints. The suggested wider shared-denominator timing fixture remains future
qualification; this bounded round is closed. Existing timing samples are retained
against their original sources, and no speed claim is made for the final fixes.
