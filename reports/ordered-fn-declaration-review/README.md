# Ordered-function declaration review

The [computational assessment](computational.md) covers the five production
computational modules; the [companion assessment](companion.md) treats each
handwritten nontrivial semantic declaration in the eight companion modules.
Both refer to source commit `79b991882a486a8c8d05fd26aaf1656358834b7e`.
The module hashes in [manifest.json](manifest.json) agree with those modules in
the merged integration tree.

This source review checks generality, semantic hypotheses, characterization,
implementation identity and actual private-helper uses. It supplements the
existing lint/docstring checks; those checks alone would not discharge Phase 6.

[declaration-use.json](declaration-use.json) is a compiled-environment reference
and axiom inventory. Its 545 constants include generated structure declarations,
instances, equations and proofs. The retained [producer](audit.lean.txt) was
compiled by Lake with `HexManual` imported at the stated source commit; its
output path is the local capture destination. Source hashes and producer hash
are recorded in the manifest. A reproduction can copy that producer into a
temporary `HexOrderedFnMathlib/UsageAudit.lean`, change the output destination,
and build it with `lake build HexOrderedFnMathlib.UsageAudit`.

Named proof-body references do not encompass elaborator instance, ext and simp
registration or every anonymous example. Zero users therefore do not establish
that a public theorem is dead. The source assessments separately identify the
purpose of exported characterizing laws and actual uses of private helpers.
Their axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.
The inventory is not an axiom audit of unrelated dependencies added afterwards.

The [performance follow-up](../bench-results/ordered-fn-regression-followup/README.md)
still has four flagged parameters under the declared comparison rule. This review
**does not attest Phase 6** or advance Phase 7. The existing manual and Phase-5
proof/API work remain available while the performance finding is unresolved.
