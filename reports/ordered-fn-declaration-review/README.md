# Ordered-function declaration review

The [computational assessment](computational.md) covers the five production
computational modules; the [companion assessment](companion.md) treats each
handwritten nontrivial semantic declaration in the eight companion modules.
Both refer to source commit `79b991882a486a8c8d05fd26aaf1656358834b7e`,
preserved by the non-release tag `audit/issue-10575-orderedfn-review`.
Commit `d07b00469d75085b3fe6161f5896a6134c2037b2` contains byte-identical
copies of all thirteen production modules. Rebuilding against its larger
`HexManual` import closure changes `users`; the frozen inventory is reproduced
at the source tag, not by assuming HEAD has the same imported environment.
The module hashes in [manifest.json](manifest.json) agree with those modules in
the merged integration at `d07b00469d`. The current companion relocates the
two generic sign lemmas into `Sign` and uses `Bounds.width_add` in convergence;
the frozen inventory and tables remain assessments of their explicitly pinned
source, rather than claims about HEAD reference counts.

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

The [49 zero-reference dispositions](zero-references.md) distinguish existing
anonymous examples, rfl characterizations, the unfolded termination instance and
intentional public characterizing APIs. Named proofs normally retain references
to non-rfl simp/ext/instance lemmas, which the inventory counts. Anonymous
examples and elaborator reductions can leave no named edge; nonzero counts may
come from tests. Neither count alone decides production use or Phase-6 quality.
Their axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.
The inventory is not an axiom audit of unrelated dependencies added afterwards.

The [performance follow-up](../bench-results/ordered-fn-regression-followup/README.md)
still has four flagged parameters under the declared comparison rule. This review
**does not attest Phase 6** or advance Phase 7. The existing manual and Phase-5
proof/API work remain available while the performance finding is unresolved.

[Automation, imports and naming](quality.md) record the remaining quality
assessment and the shared sign module. Final Phase-6 acceptance is
still required.

The original benchmark sources are likewise retained by
`audit/issue-10575-orderedfn-baseline` (`ee490f54889e2db8170c8b9fc6e8568f8a978bbe`)
and `audit/issue-10575-orderedfn-candidate`
(`a9a8997e470a996509940d035deebdc79db56a79`). These evidence references
are separate from release-version tags and do not change publication eligibility.
