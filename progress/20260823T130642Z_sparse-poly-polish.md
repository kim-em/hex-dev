# hex-sparse-poly + companion: Phase-6 polish

## Accomplished

- Warning sweep to zero across the core: 8 unused simp arguments
  removed, 17 `omit [...]` clauses added for unused auto-included
  section variables (including two revealed by the first pass), two
  no-op `simp only [hgap]` lines deleted, two unused lambda binders
  anonymised.
- Two unused instance arguments dropped: `SparsePolyCanonical` loses
  `[DecidableEq R]`, `divMonomial?` loses `[Mul R]`.
- Build-enforced docstring coverage: `HexSparsePolyMathlib/LintTests.lean`
  runs Batteries' default linter set plus `docBlame`/`docBlameThm'`
  (the RCF pattern, additionally filtering the `@[ext]`-generated
  `ext_coeff_iff`) over both libraries, wired into `HexSparsePolyTests`.
  43 missing docstrings written (one def, 42 theorems). It lives under
  the mathlib-true owner because it imports the Mathlib linter
  framework.
- Dead-declaration sweep: 262 public declarations, 25 referenced only
  at their definition, all kept with documented interface roles: the
  SPEC'd law/transport surface (round trips, `ofDense_*`/`toDense_*`
  images, `divExactMonic?` iffs, `divMod_degree_lt`,
  `mulMonomial_divMonomial`, `derivative_add`, `eval_substPow`,
  `coeff_substScale`, `dvd_def`, the companion `equiv_*` lemmas and
  the `_apply` conventions) plus two characterising helpers
  (`coeffList_termsOfCoeffsList_of_lt`, `addCoeff_zero_left`).
- Perf regression check against the Phase-4 headline numbers, one
  registration per family at the top schedule rungs: mul at parity
  (8.51 ms vs 8.67 ms at t=256), eval parity (13.8 µs vs 13.5 µs at
  t=512), substPow flat (128 ns at k=32768 vs 126 ns), add and
  convert-gcd about 2x faster than the recorded numbers (systematic
  main-side improvement, not a regression).
- Native-path criterion holds (no native_decide, csimp twins only);
  no irreducibility claims in scope. `done_through: 6` for both.

Also this session, stack maintenance: the Phase-4 checker grew a
cost-model-derivation requirement on main; satisfied by amending the
conformance-branch commit message (which owns the bench registration
lines) with per-family derivations, and by naming the comparators
verbatim in the headline report. #9374 merged; #9380 retargeted to
main with auto-merge armed.

## Current frontier

Both libraries at Phase 7 (user-facing documentation).

## Next step

Phase 7: `HexManual/Chapters/HexSparsePoly.lean` Verso chapter with the
Mathlib-correspondence section (check_phase7.py enforces the companion
documents inside the parent chapter), `HexSparsePoly/README.md` per
SPEC/readme.md, `done_through: 7` both. Then the release tail.

## Blockers

None.
