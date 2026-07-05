# Relocate cross-check/testing modules into `conformance/` (issue #8607)

## Accomplished

Separated verification content from library implementation for legibility.

- `git mv` of five `HexFoo/CrossCheck.lean` → `conformance/HexFoo/CrossCheck.lean`
  (HexArith, HexGFq, HexHensel, HexBerlekampZassenhaus, HexGF2). Lean module
  names (`HexFoo.CrossCheck`) are preserved because they are path-relative to
  the `HexConformance` `srcDir := "conformance"`, which already reuses the
  `HexFoo.*` namespace — so `conformance/HexGFq/EmitFixtures.lean`'s
  `import HexGFq.CrossCheck` (uses public `genericN16_irr`) still resolves with
  no edit.
- Renamed the two `HexFoo/Smoke.lean` → `conformance/HexFoo/FastCheck.lean`
  (HexModArith, HexGF2); "smoke" is banned vocabulary.
- Dropped the `import HexFoo.CrossCheck` / `.Smoke` lines from the umbrella
  `HexFoo.lean` files and refreshed the umbrella docstrings.
- Added the 7 relocated modules to the `HexConformance` `globs` in
  `lakefile.lean` so their `#guard`s still elaborate on the CI
  `lake build HexConformance` step (same critical path; nothing about what
  runs changes).
- The SPEC/testing.md convention writeup (new "Where cross-check content
  lives" section, plus corrections to the pre-existing stale "re-exported
  from the umbrella" claims) and the matching `scripts/conformance_targets.py`
  docstring fixes are split into a companion PR (#8609) to keep documentation
  isolated from the functional relocation. This branch (#8608) is the source
  move only.

Verified: full `lake build` of the affected libs + `HexConformance` + all
emit-fixture exes is green; `scripts/conformance_targets.py --check` and
`scripts/check_file_line_counts.py` pass. Codex second opinion + a subagent
review both confirmed the mechanics are clean; their only findings were the
doc-accuracy wording, now addressed.

None of the affected libraries are released repos, and the release sync treats
both `<Lib>/` and `conformance/<Lib>/` as managed paths, so the publish model
is unaffected.

## Current frontier

Change complete on branch `issue-8607`; opening the PR.

## Next step

Merge after CI. If a future release promotes any of these libraries, the moved
modules publish under `conformance/<Lib>/` automatically.

## Blockers

None.
