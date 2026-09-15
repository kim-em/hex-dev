# Rank-locus proof performance

## Preregistered measurements

`scripts/bench/rank_locus_sweep.py` registers eight fresh-module probes from the
`symbolic` family in `bench/HexGenericRank/Bench.lean`, restricted to thresholds
`r ≤ 3`. The checked-in literals expand that family's triangular and factorized
matrices. The selected rungs cover dimensions 2, 4 and 8; one and two variables;
degrees one and two; support caps one and four; and both full and low generic
rank. These are structured inputs, not a claim about worst-case expression growth.

Each case has six adjacent import-baseline/candidate pairs, with alternating
AB/BA order. The full-build ceiling is **30 seconds**, with a **120 second**
cleanup timeout. All completed samples are retained on the shared host, pinned
to one automatically selected CPU. The baseline imports exactly the same modules
as the candidates. Comparator: **no-comparable-surface-in-named-comparator**;
Mathlib has no tactic that produces a symbolic rank-locus statement.

The term-form probes certify the entire generator list. Lean's profiler records
batch reflection, compiled enumeration (including quotation), and the synchronous
kernel declaration check of `detIdealGensList` separately. Nested profiling is
disabled inside the batch and declaration-check categories. The full-build time
also includes entry and display proofs, theorem construction, imports, startup,
linting and serialization. No probe or provider reads an in-process clock.

Every accepted result must depend only on `propext`, `Classical.choice` and
`Quot.sound`. The runner records proof nodes, artifact sizes, source hashes,
compiler output, host activity and signed baseline differences.
