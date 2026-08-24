# Accomplished

- Required transport to name an exact current source version and install the
  identical source fact; added an exact `999` mismatch rejection canary.
- Added an authenticated inherited assembly-generation base to runtime state.
  Strict global instance generations now rebase coherently onto consecutive
  child-local branch generations.
- Extended the restarted split-child canary through a second instance at
  global generation two, then a fresh equality, fact, and transport chain.
- Added strict restarted generation, node, application, and instance one-over
  checks.
- Exposed an opaque ordinary-import `Tree.transitions` view and hardened tree
  validation against out-of-tree runtime identifiers and unauthenticated root
  origins.
- Nested runtime limits into result limits so retained event counts use
  `Runtime.Limits.maxEvents`; added the exact zero-event one-over.
- Corrected retained runtime accounting to charge accepted quotes once and
  each branch-chain position once while preserving exact cached cost checks.
- Documented raw endpoint/transport authority, generation rebasing, runtime
  event limits, and retained-cost asymptotics.
- Added the exact test-only `lakefile.lean` transition to the factorization
  freshness exemptions; the freshness gate now accepts the conformance target.
- Passed focused runtime/search/Mathlib conformance, source/static gates, and
  the full 9,820-job `lake build` before final restacking.

# Current frontier

The requested review repairs are complete locally. Upstream `main` advanced to
`cd620596e7d0672691695d29711819f444a8f4eb`; the commit is ready for a
mechanical restack and exact-head verification before force-pushing PR #9377.

# Next step

Restack on the recorded upstream head, rerun cached affected/static/full gates,
and force-push only `agent/interval-runtime-events`.

# Blockers

None.
