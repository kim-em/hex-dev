# Mathlib-free bench-root lint repair

## Accomplished

- Opened issue #8975 from the enforcement defect found during HexRCF's
  Phase-4 premise audit.
- Reworked `check_benches_mathlib_free.py` to parse every Lake executable's
  root and effective `srcDir`, reject missing declared roots, and traverse the
  actual source path instead of a guessed repository-root path.
- Updated the Lean import parser for `prelude`, module-system headers, nested
  comments, `public`/`private`/`meta` modifiers, `import all`, multiple imported
  modules, repository modules, and configured package library `srcDir`s.
- Made Lake parsing fail closed on unsupported computed `srcDir` expressions,
  ignore commented fake fields, and recognize indented, same-line-attributed,
  and escaped executable names before `_bench` policy classification.
- Kept the build-only Mathlib proof-probe restrictions and strengthened their
  LeanBench-import detection for the same import modifiers.
- Added eleven focused regression tests covering those parser and resolver
  boundaries, including dependency TOML `lean_lib` source roots.
- Extended the existing single CI lint step to run the regression suite before
  the repository lint; no job, matrix, or workflow was added.
- Rebased HexRCF conformance PR #8970 over newly merged interval-framework
  work, preserved both conformance globs, rebuilt `HexConformance` plus the RCF
  emitter successfully, and pushed the resolved branch with auto-merge intact.

## Current frontier

All eleven regression tests and the real 21-executable traversal pass. The
DAG, release-manifest, trust-surface, Phase-4 checks, Python compilation, and
diff checks are green. The first Sol review found five fail-open cases; all are
fixed with regressions. Its final pass found the Lean-4.32 header order
`module` then `prelude`; that case is also fixed and pinned. The bounded final
review returned GO with no remaining blocking false negative or regression.

## Next step

Commit and publish issue #8975, enable auto-merge, then continue with whichever
becomes actionable first: the
quiescent-host #8972 timing sweep or the contract work decomposed from #8973.

## Blockers

None for the lint repair. The unrelated #8972 scientific sweep remains
environment-blocked by heavy concurrent Lake/Lean load on the shared host.
