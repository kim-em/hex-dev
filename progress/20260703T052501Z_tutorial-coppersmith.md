# Tutorial 4: LLL in cryptanalysis (toy Coppersmith attack)

Wrote the fourth capstone tutorial page specified in
[SPEC/tutorials.md](../SPEC/tutorials.md) §4, the LLL-anchored Phase 7
tutorial ([PLAN/Phase7.md](../PLAN/Phase7.md) table).

## Accomplished

- New Verso chapter `HexManual/Tutorials/Coppersmith.lean`: an
  application-first page that presents a weak RSA `e = 3`
  stereotyped-message instance, encodes the missing suffix as a small
  modular root of `f(x) = (a + x)^3 - c`, builds the minimal single-shift
  Coppersmith / Howgrave-Graham lattice, LLL-reduces it with the exact
  integer reducer `Hex.lllNative`, and recovers the hidden code from the
  reduced basis.
- The worked example is fully build-checked. Coefficients are computed
  live from public data via a `centerMod` helper (no magic constants).
  Recovery scans all reduced rows, de-scales each (every basis column is
  divisible by its `X^j` scale, so de-scaling always succeeds), searches
  `0 <= x < X` for an integer root, and accepts the first that reproduces
  the ciphertext. Four `#guard`s pin: the ciphertext genuinely wraps mod
  `N` (not a raw cube), the reduced basis passes `lllReducedInt`, and the
  recovered code is `42`.
- Concrete instance: `p = 100000007`, `q = 100000037`,
  `N = 10000004400000259`, template `a = 55555500`, bound `X = 100`,
  hidden `x0 = 42`. Validated first in Python, then authoritatively in
  Lean via a temporary compiled `lean_exe` (needed because `lllNative`
  routes through the `@[extern]` `Matrix.exactDiv`, which the plain
  interpreter cannot run): Lean's `lllNative` produces the same reduced
  basis Python does, and recovery returns `some 42`. The reduction is
  nontrivial (the recovered short polynomial has leading coefficient 27,
  a genuine integer combination of the four rows), so the page shows LLL
  doing real work rather than returning `f` unchanged.
- Wired into the aggregator: `HexManual.lean` gains the import and a new
  `# Tutorials` section that includes the page at heading depth 1. No
  `lakefile.lean` change (the `HexManual` lean_lib discovers modules by
  import); no `libraries.yml` change (`HexLLL` is already
  `done_through: 7`, this closes its outstanding tutorial exit criterion).

## Current frontier

Page builds clean inside the `HexManual` lean_lib (all embedded `#guard`s
green, zero line-length warnings after shortening four lines) and the
full manual renders.

## Next step

None for this page. The remaining tutorials (AES arithmetic, AES modulus
irreducibility, Kummer-Dedekind splitting) are separate anchor-library
work.

## Blockers

None.
