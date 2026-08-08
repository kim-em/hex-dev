# Accomplished

- Added a proof-equal compiled implementation for size-ordered classical
  recombination. It caches subset degree and endpoint residues, rejects most
  candidates before constructing a polynomial product, and preserves the
  reference budget/fuel result exactly through `@[csimp]` theorems.
- Added proof-equal fast paths for modular coefficient products and the ordinary
  smart-candidate prefilter, including monic multiplication/power shortcuts and
  an exact integer magnitude rejection before arbitrary-precision remainder.
- Kept the cached complete-subset shortcut below 20 local factors, where the
  proper search fits the existing default subset budget. The 72-local-factor
  regression canary remains on the ordinary size-ordered path and runs in about
  0.08 seconds.
- Incorporated independent review findings: changed the cached DFS to
  exclude-first traversal, moved list reversal below the prefilter, returned the
  proof-equal exhausted result without a duplicate reference scan, and deleted
  the unused earlier scanner/shortcut.
- Measured public `sd5` at 40.056 ms versus 90.353 ms on the merged baseline;
  no-decline classical improved from 89.168 ms to 81.465 ms. A 20-case random
  reducible A/B was neutral in aggregate (41.541 ms versus 41.470 ms across the
  two measured Hex entries).
- Completed `lake build`, the source/release/trust lints, the 102-case FLINT BZ
  oracle, the 52-trace anti-regression gate, and explicit axiom inspection. The
  new equivalence theorems depend only on Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound` axioms.

# Current frontier

The implementation is staged and ready for a code commit. The durable full-corpus
Hex sweep has not yet been recorded because its artifact name should carry the
new code commit.

# Next step

Commit and replay the change onto current `origin/main`, record only the affected
`hex-factor` and `hex-classical-nodecline` corpus entries, regenerate the merged
cross-system plots/report, then open the PR and merge after CI.

# Blockers

None.
