# Local candidate-package consumer

The question is whether the completed semantic modules can be consumed from
separate package trees with exact dependencies, and what prevents an optional
real-coefficient adapter from sharing the existing `HexRCF` namespace.
This is a local experiment for #10575, not release-sync validation or
publication eligibility. PR #10476 supplies the future release staging check;
its implementation is not duplicated here.

## Construction

Use `scripts/release/released.yml` for published source mappings and skeletons,
`libraries.yml` for the complete declared dependency closure, and the monorepo
lock for external requirements. Assemble the closure of HexRealRootsMathlib,
HexSturmMathlib, HexSignDetMathlib, HexOrderedFnMathlib, HexRealClosureMathlib and
HexRCF in dependency order. The local layout contains 62 Hex packages.

For existing mirrors, clone their public skeletons without writing to them.
For unpublished inputs, use local skeletons following `BOOTSTRAP.md`; do not
add those inputs to the released manifest. Reuse the existing driver's
`managed_paths`, `rsync_dir`, `copy_file`, `rewrite_test_target`,
`rewrite_doc_verso`, `rewrite_lib_settings`, `rewrite_lake_declarations`,
`rewrite_toolchains`, `rewrite_external_requires`, `rewrite_external_pins`,
`rewrite_requires`, `rewrite_manifest` and `validate_external_imports`.
Copy the already delivered sign/tower semantic adapters into their candidate
owner trees without changing the monorepo's active owner files. Exclude their
semantic regression modules from those additional candidate mappings.

Commit each tree locally. Replace Hex dependency URLs with local Git URLs and
pin every declared input to its exact candidate commit. A fresh consumer
requires those Git commits, never a path dependency on the monorepo. It may
reuse external build caches only after checking their Git revisions against
the lock; its Hex sources and build directories are separate checkouts.

Reuse the four `RealClosureConsumer` modules from `examples/`. Copy the existing
real-coefficient adapter sources and the owner's `TotalAlgebraicProofs` and
`ProductionProgress` checks into the consumer as test sources. This test host
does not select or install an optional package. Run `lake update`, followed by
`LAKE_NO_CACHE=true lake build`. The ordinary-import examples and the owner
proofs retain their exact ordinary-kernel axiom guards.

## Results and limits

The ordinary consumer compiles shared integer Tarski and complete field query
semantics, including `HexSturmMathlib.query_iff`,
complete BKR/Thom production, successive infinitesimal order and native tower
root coverage/multiplicities/order. The optional checks reuse the actual tactic
and exact-field production examples, including original divisor rejection,
refusal diagnostics, and quantified decisions. They do not prove joint
ordinary-real realization of nested samples or owner Phase-4 readiness.

The initial optional check fails with the default base library declaration:
Lake selects base HexRCF for absent `HexRCF.RealCoefficients.*` files instead
of the consumer's optional modules. Disjoint files alone do not establish
installable ownership. A local experiment changes only the candidate base
library to `roots = []` and exact non-test module globs; its separate test
target keeps the existing test module list. With those declarations the
optional checks compile. This base-package change is a proposal requiring
user direction and an owning SPEC revision before production integration.
The current release tool and manifest do not apply it.

Other retained failures concern local assembly: shallow source repositories
need full history for Lake's Git fetch, and an assembly attempt must start
with the original skeleton rather than feed rewritten local URLs back into
GitHub requirement synthesis. A host restart damaged late-written temporary
Git metadata; the affected candidate was recovered from its retained commit
and the consumer was rebuilt. These are not algorithm or performance results.

The [evidence ledger](../../reports/real-closure-candidate-consumer.json)
records all 62 candidate commits, exact external pins, configuration hashes,
consumer source hashes and build-log hashes. The fresh consumer build completes
10,918 jobs, including the existing rational HexRCF test target. Separate
HexRealRootsMathlib, HexSturmMathlib and unchanged-base HexRCF package builds
also pass without `lake update`; their generated locks stay byte-for-byte
unchanged. Computational package declarations and locks contain neither
Mathlib nor Tau Ceti. Local candidate commits
are not published versions or remotely installable release pins. None of
these checks runs a full sync dry run, creates mirrors, advances phases or
establishes distribution eligibility. The remaining publication requirements
are in [the publication plan](../../reports/real-closure-publication.md).
