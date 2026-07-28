# HexRCF Phase 6 documentation audit

## Accomplished

- Ran the Mathlib linter with legacy import semantics, which retain imported
  documentation metadata under Lean's module system. The final audit reports
  zero errors across 396 HexRCF declarations and 14 linters.
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
- Verified that every private HexRCF declaration has at least one textual use,
  then built all changed modules and the complete `HexRCF` target.

## Current frontier

- The documentation and linter corrections are complete on the stacked
  `rcf-phase6-docstrings` branch.
- The branch still needs the public/test separation milestone from PR #9032
  before its lint audit can become a permanent non-public test module.
- Public characterising lemmas with no current in-repository caller remain
  under API and dead-declaration review. They are not being removed solely
  because a textual search found no caller.

## Next step

- Rebase onto main after PRs #9032 and #9033 merge.
- Add the permanent lint module to `HexRCFTests`, finish the API and
  dead-declaration review, and publish the Phase 6 quality milestone.

## Blockers

- None. The two preceding milestone PRs are already queued to merge after CI.
