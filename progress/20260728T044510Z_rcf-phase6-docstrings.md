# HexRCF Phase 6 documentation audit

## Accomplished

- Ran the Mathlib linter with legacy import semantics, which retain imported
  documentation metadata under Lean's module system. The final audit reports
  zero errors across 392 HexRCF declarations and 14 linters.
- Added documentation for every genuinely undocumented public structure field
  and tactic implementation reported by the linter.
- Added documentation for 31 public theorems that another module could
  reasonably import, plus the non-obvious private open-cell boundary lemmas.
- Named the internal `rcf_ring` macro declaration `rcfRing` so its generated
  declaration follows Lean naming conventions without changing tactic syntax.
- Removed prohibited terminology and semicolon run-ons from the HexRCF source
  prose touched by this audit.
- Rephrased tactic diagnostics as separate sentences and updated their exact
  regression, conformance, and manual outputs without changing refusal or
  false-verdict behavior.
- Shortened the public builder-characterisation names to
  `check_buildSturmReplay`, `Separation.check_separate`, and
  `exists_cert_of_decide`.
- Removed the unused `IsolationCert.sample?` wrapper and its theorem. The
  implemented pipeline and SPEC use `IsolationCert.openPoint` directly.
- Replaced the checker-local positive-degree recursion with `List.all`. Kept
  endpoint-vector, duplicate-removal, and separation helpers public because
  exposed definitions depend on them or the SPEC and tests exercise them.
- Shortened five overqualified semantic theorem names, including
  `IsolationCert.existsUnique_root`, `RootModel.root_unique_leftSpan`, and
  `Polynomial.sign_eq_of_noRoot`.
- Moved the decision-builder meta import from `Reify` to its actual consumer,
  `Tactic`, and made tactic-only Mathlib and Lean imports meta-only. Added the
  direct Syntax meta dependency required to compile reifier constructors.
- Confirmed by downstream tactic tests that the direct public
  `HexRealRootsMathlib.IsolateRoots` import is required for expansion of the
  public `rcf_ring` macro, so retained it.
- Added `HexRCF.LintTests` to the existing default regression target, making
  the zero-error public namespace lint a permanent build invariant.
- Verified that every private HexRCF declaration has at least one textual use,
  then built all changed modules and the complete `HexRCF` target.

## Current frontier

- The documentation, linter, API, dead-declaration, and import-boundary audits
  are complete on `rcf-phase6-docstrings`, rebased over merged PRs #9032 and
  #9033.
- `lake build HexRCF HexRCFTests HexConformance HexManual` succeeds with 9,526
  jobs, including the permanent zero-error lint regression.
- Repository DAG, release-manifest, trust-surface, Phase 4, copyright, and diff
  checks pass.

## Next step

- Publish the Phase 6 quality milestone, obtain an independent Claude Opus
  review, address any actionable findings, and merge after CI.

## Blockers

- None for this milestone.
