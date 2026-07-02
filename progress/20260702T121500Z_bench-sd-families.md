# bench-sd-families — SD tier-crossover ladders, figures, report

Follow-up to PR #8537 (level-aware decline boundary), turning that PR's
ad-hoc benchmark comments into tracked lean-bench targets with committed
artefacts and figures, per Kim's request.

**Accomplished**
- Registered three one-parameter families in
  `bench/HexBerlekampZassenhaus/Bench.lean` (all `scheduled-hardware`,
  so merge-gating `verify` is unchanged — measured 18 targets / 0.04 s):
  `SD_k` ladder (k = 1..5), pair ladder `SD_k(x)·SD_k(x+1)` (k = 1..5,
  classical → lattice at k = 5), block ladder `∏_{i<m} SD_4(x+i)`
  (m = 1..4, crossover at m = 3). SD literals pinned from sympy;
  derived products via `DensePoly.compose`/mul with `#guard` pins of
  constant coefficients. Seven new verified-Isabelle fixed rungs (every
  rung the AFP extraction answers under 120 s; the pair k = 5 rung is
  deliberately absent — no lattice tier, > 120 s).
- Clean-tree exports committed under
  `reports/bench-results/hex-berlekamp-zassenhaus-7da4747e-*.json`
  (hex three families, Isabelle rungs incl. per-request baseline,
  informational FLINT curve).
- Figure generators `scripts/plots/hex-berlekamp-zassenhaus-sd.py`
  (+ `-sd-flint.py`); three log-y SVGs in `reports/figures/`. The pair
  figure shows the story in one glance: the verified reference's curve
  leaves the chart at k = 5 where hex's lattice tier answers in 16.7 s.
- Headline-report subsection (tables, artefact SHA-256s, agreement
  hashes for all nine shared rungs — all AGREE — and trend narrative).

**Current frontier**
- Trend worth watching (recorded in the report as an optimisation
  target): hex loses ground to the verified Isabelle extraction as `r`
  grows on the pure certification ladder (hex/Isabelle ≈ 1.6 at SD4,
  ≈ 10 at SD5) — the classical tier's full-powerset certification burn.

**Next step**
- Wire these families into whatever scheduled-hardware timing runs get
  set up (SPEC §Scientific timing runs); the report records the exact
  commands.

**Blockers**
- None.
