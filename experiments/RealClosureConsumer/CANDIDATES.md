# Local candidate-package consumer

The question is whether the completed semantic modules can be consumed from
separate package trees with exact dependencies, and what prevents an optional
real-coefficient adapter from sharing the existing `HexRCF` namespace.
The evidence ledger identifies the exact source commit used by this local
experiment for #10575. It is not release-sync validation or publication
eligibility. Merged PR #10476 supplies the release staging check;
its implementation is not duplicated here.

## Construction

Use `scripts/release/released.yml` for published source mappings and skeletons,
`libraries.yml` for the complete declared dependency closure, and the monorepo
lock for external requirements. Assemble the closure of HexRealRootsMathlib,
HexSturmMathlib, HexSignDetMathlib, HexOrderedFnMathlib, HexRealClosureMathlib and
HexRCF in dependency order. The local layout contains 62 Hex packages.

Reproducing the recorded evidence requires its recorded source commit and
configuration hashes; it used the driver helpers available at that revision.
For a new candidate, use current `BOOTSTRAP.md` and the existing driver's
`managed_paths`, `apply_paths`, `render_lakefile`, `write_lakefile`,
`rewrite_toolchains`, `rewrite_manifest` and `validate_external_imports`.
Clone existing mirrors read-only and use local skeletons for unpublished
inputs. Do not add those inputs to the released manifest. Current Lake
configuration is generated from monorepo declarations and manifest metadata;
obsolete mirror declarations must not be copied into a new candidate.
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
consumer source hashes and build-log hashes. The fresh consumer uses the
experimental base declaration described above; its build completes 10,918
jobs, including the existing rational HexRCF test target under that declaration. Separate
HexRealRootsMathlib, HexSturmMathlib and unchanged-base HexRCF package builds
also pass without `lake update`; their generated locks stay byte-for-byte
unchanged. Computational package declarations and locks contain neither
Mathlib nor Tau Ceti. Local candidate commits
are not published versions or remotely installable release pins. None of
these checks runs a full sync dry run, creates mirrors, advances phases or
establishes distribution eligibility. The remaining publication requirements
are in [the publication plan](../../reports/real-closure-publication.md).
