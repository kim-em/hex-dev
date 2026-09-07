# Independent implementation review: issue #10074

Claude Opus reviewed PR #10110 in a fresh read-only process immediately after
opening the PR, while CI and the final integrated comparison ran. The review
found no defect in the proved factorization path. The responses below record
the findings, their verification, and the resulting changes.

1. **Singleton reconstruction and raw presentations.** The review correctly
   observes that returning the canonical monic input makes reconstruction an
   identity. No extra degree guard was added: `recover_singleton` proves exact
   equality with the reference recovery, and `factorSquarefree_mem_sound`
   proves irreducibility on validated towers. `Internal.extend?` checks a new
   relation over its already validated `NumberTower` parent; it does not run
   the checker over an arbitrary unvalidated parent list. The suggested
   hypothetical malformed raw presentation lies outside those guarantees,
   and a degree check would not validate such a presentation. The SPEC now
   explicitly states the raw helper boundary and the role of the singleton
   reconstruction check.

2. **Binary provenance after rebasing.** Accepted. The report now identifies
   the hash equality with the prototype as a pre-rebase fact at `4d6608de3`.
   It separately records the integrated executable `9c51c94c…` and its passing
   comparison against main `064902321`. That comparison was incomplete when
   the review read it; admitted attempts 2 and 4 now establish the final
   3.750–3.774× factorization and 3.991–4.002× replay improvements.

3. **Host admission audit.** Accepted. The decision validator now rechecks
   quiet-window history, both preflights/postflights, raw during-run samples,
   recomputed sibling means, successful process completion, benchmark names,
   affinity commands, and protocol flags. Adversarial tests cover forged
   means, busy or missing samples, nonfinite values, altered affinity and
   flags, and insufficient quiet history. A regression test reproduces all
   seven retained series' decisions under this audit, preserving the
   incomplete series' lack of a verdict. No threshold, admitted pair, or
   timing value changed.

4. **Differential driver maintenance and nonzero linear terms.** Accepted.
   `tower_factor_diff` is now built in the existing CI job and executed in its
   conformance tail. This retains the frozen reference as a checked regression
   surface, including execution of both nonzero-linear-term quadratic terms.
   No workflow, job, or benchmark registration was added.

5. **Proof unfolding duplication.** Partly accepted. `recover_singleton` now
   sits immediately after the recovery product theorem. The local cons-case
   unfolding proofs remain: soundness derives degree from successful checks,
   while completeness starts from positive degree and proves those checks
   succeed. Their explicit matches track the executable's guards and make
   future changes to those guards visible to Lean. No runtime helper or
   additional public unfolding API was introduced.

6. **Scope of the timed family.** Accepted as a documentation clarification.
   The report explicitly states that all eight Hex comparison cases have a
   quadratic top level and a singleton norm factor. Their measured constants
   do not cover multiple-factor gcd recovery; reducible conformance and
   differential cases cover that branch for correctness.

7. **API and presentation details.** The PR description identifies the
   `rawPoly_oneLevel` to `rawPoly_resultant` helper change and its new lower-field
   validity/injectivity/inverse-semantics hypotheses. Public factorization
   soundness and completeness statements are preserved. The long report line
   was wrapped. Full recorded telemetry remains intact, as required by the
   preregistered protocol; it was not compacted after measurement.

Validation after these changes: the full `HexNumberFieldTowerMathlib` build
and the differential driver pass; 32 validator tests pass, including the
retained-artifact audit. The measured benchmark executable remains unchanged.

## Focused review of the graph-sweep freshness rule

A second read-only Opus review examined the checked allowance added after an
upstream graph-sweep fingerprint expansion. It could not construct an accepted
Lake change that reaches the measured graph artifacts, but identified two
latent sources of an under-approximated import closure. Both were fixed:

- Import resolution now examines every tracked Lean source whose path suffix
  matches the imported module, rather than assuming sources live only at the
  repository root, `bench`, or `conformance`. This covers current and future
  source directories and conservatively scans every ambiguous match.
- The closure and tracked umbrella set now use the Git index and read exact
  blobs, matching the state fingerprinted by the sweep machinery. Untracked or
  unstaged worktree files cannot change the decision.

The review also caught the default `roots := #[name]` of a `lean_lib` with an
explicit `globs` field. A new library whose name is in the measured import
closure is now rejected explicitly. The graph freshness verdict and per-node
sweep selector share the same allowance. Tests cover arbitrary source
directories, exact index blobs, the measured closure's positive namespaces,
default library roots, mode and path guards, closure failure, and the complete
allowance wiring.

The suggested consolidation with the factor-sweep Lake block parser was not
made. The present graph rule intentionally recognizes a smaller syntax and
fails closed; its remaining positional limitations cause only false rejects.
Moving both mature checks onto a new shared parser would enlarge the change
without strengthening the accepted set's safety. Documentation now states the
`bench`/`conformance` restriction, top-level namespace exclusion, `roots` versus
`globs` semantics, index-based closure, and the factor check's separate
build-input rule.
