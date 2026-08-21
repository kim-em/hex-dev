# 2026-08-21T06:34:24Z — spec: truncated power series libraries (#9320)

## Accomplished

Wrote `SPEC/Libraries/hex-truncated-series.md`, covering
`hex-truncated-series` and its Mathlib companion, and registered the
pair in `SPEC/Libraries/README.md` (computational list, companion list,
implementation dependencies, DAG section, index) and in
`SPEC/future-work.md`.

Decisions the SPEC records, each with the argument for it in the text:

- The representation is `structure TSeries (R) (n) where coeffs : Vector R n`,
  with the precision in the type and no normalisation invariant. The
  dependency is hex-basic alone: `Hex.instDecidableEqVector`,
  `Hex.Vector.ofFn'`, and `HexBasic.Fold` are what the type needs, and
  hex-poly cannot use any of them because it declares no dependencies.
- Conversion to reversed `DensePoly` and fast polynomial division are
  left to the planned `hex-poly-fast`, above both libraries. The SPEC
  states why the reverse direction has no valid publication order in
  `scripts/release/released.yml`.
- Hypotheses are per algorithm and precision-indexed. `NatInverses R m`
  holds over `Int` at `m ≤ 1` and fails at `m = 2`, so `exp` and `log`
  over `ℤ` exist up to precision `2` and no further, which is the true
  boundary. `sqrt` takes the constant root and one hypothesis, `2 * r`
  invertible.
- **Reversion is Newton, not Lagrange.** Lagrange inversion divides by
  `k` at every index and so needs integer inverses the answer does not:
  reverting `x + x²` over `ℤ` gives `x - x² + 2x³ - 5x⁴ + …`. Lagrange
  stays as a second route where `NatInverses` is in scope, and as a
  conformance cross-check.
- Newton uses one driver, structurally recursive on the step count, with
  `steps n = ⌈log₂ n⌉` and `two_pow_steps_ge`. No fuel argument, so no
  fallback branch to classify under design principle 8. Each step is
  bounded through `mulUpTo (2 ^ (j+1))`, which is what makes the total
  cost `O(M(n))` rather than `O(M(n) log n)`.
- Failure is two forms per algorithm: a witness-taking total form and an
  `Option` form. No junk-value fallback anywhere.
- A "Degenerate-input audit" section tabulates every operation at
  precision `0` and `1` and at noninvertible constant and linear terms.
  Precision zero is the zero ring, so `inv?` and `rev?` succeed there
  unconditionally, and hypotheses are written so they are automatically
  satisfied out of range (`log` takes `(a - 1).coeff 0 = 0`, not
  `a.coeff 0 = 1`).
- Honest performance claim: at schoolbook multiplication Newton
  inversion, `sqrt`, `exp`, and `log` all *tie* their naive linear
  recurrences. Only composition and reversion win today. The bench
  requirement is "within `2x` of the recurrence", not "faster".

## Verification

- `git diff --check`, `scripts/check_dag.py`,
  `scripts/release/check_released_manifest.py`,
  `scripts/release/check_manual_split.py`, `scripts/check_phase4.py`,
  and `scripts/conformance_targets.py --check` all pass.
- Every relative link in the three edited files resolves.
- Mathlib citations checked against the vendored checkout:
  `PowerSeries.substInvOfIsUnit` with `subst_substInvOfIsUnit_left/right`
  exists under exactly this library's reversion hypotheses;
  `PowerSeries.exp` and `logOf` need `[Algebra ℚ A]`; there is no
  `PowerSeries` square root.
- `Nat.log2` kernel-reduces (`example : Nat.log2 8 = 3 := by decide +kernel`
  accepted), and `#print Nat.log2` shows a `Nat.rec` on the argument
  reused as a bound rather than `WellFounded.fix`. The SPEC records both
  the fact and the reason.
- Reversion coefficients `0, 1, -1, 2, -5, 14` for `x + x²` and the
  `ZMod 2` / `ZMod 9` square-root counterexamples were checked by hand.

## Review round

A Codex second opinion found real errors, all now fixed. Recording the
substantive ones because they are the kind a successor could reintroduce:

- **The degenerate disjunct was in the wrong place** for two of the
  three success conditions. `rev?` drops the linear-coefficient test at
  precision one but keeps the constant-term test, so
  `rev? (C 1 : TSeries R 1)` is `none`; the original
  `n ≤ 1 ∨ (b.coeff 0 = 0 ∧ …)` claimed every precision-one series is
  reversible. `sqrt?` splits the same way: at `n ≤ 1` unitality of
  `2 * r` is irrelevant but `r * r = a.coeff 0` still holds, so
  `sqrt? (4 + x) 2` over `ℤ` succeeds at precision one.
- **Two Mathlib correspondence theorems were false.**
  `PowerSeries.HasSubst` is `IsNilpotent (constantCoeff a)`, not
  vanishing, so `ofPowerSeries_subst` under it fails over `ZMod 4` with
  `g = C 2`. `PowerSeries.invOfUnit f u` uses whatever `u` it is handed,
  so the transport needs `constantCoeff f = u`, which is exactly what
  `mul_invOfUnit` carries.
- **Mathlib refuses `Grind.CommRing → CommRing`.**
  `Mathlib/Algebra/Ring/GrindInstances.lean` carries the converse as an
  `example` with a comment that the direction should never be used. The
  companion builds the instance from the executable operations,
  following `HexPolyFpMathlib.commRing`.
- **`exp` and `log` did not need `[UnitOps R]`** (they invert only with
  the literal witness `1`), and carrying it would have made the
  `[Algebra ℚ R]` correspondence unstatable.
- **The reversion iteration did not typecheck**, the same `n - 1` trap
  as the `log` one: `b.deriv : TSeries R (n-1)` against `y : TSeries R n`.
  Resolved with a zero-padded derivative plus the lemma that the missing
  top coefficient is never read.
- **The geometric bound needed the bounded discipline to propagate.**
  The `exp` step calls `log` and the reversion step calls `comp`; at
  full precision those give `O(M(n) log n)`, so `invUpTo`, `logUpTo`,
  and `compUpTo` are now specified.
- Smaller: `NatInverses (ZMod q) m` needs `q` prime, and the boundary is
  `n ≤ p` not `n < p`; the Lagrange claim is about the direct `1/k`
  evaluation, not about reversion needing integer inverses; a series
  does not have exactly two square roots (`1` has four in `ℤ/15`); fast
  multiplication lands in this library, not hex-poly-fast, because a
  downstream library cannot change what `invOfUnit` calls; `DecidableEq R`
  is localized; the Brent-Kung bench requirement no longer names a
  crossover the SPEC says it will not guess.

Two errors I found myself before the review: the "within 2x" bench
threshold was unachievable (the counted ratio is 8/3), and `log` as
`integrate (deriv a * inv a)` does not typecheck at precision zero.

## Current frontier

The SPEC is complete. No Lean was written, per the issue.

## Next step

`libraries.yml` gains no entry yet, matching the other planned-library
SPECs (`hex-poly-z-gcd`, `hex-mv-gcd`, `hex-smith`), which carry their
proposed YAML inside the SPEC. Scaffolding the library is Phase 1 work
for a separate issue.

## Blockers

None.
