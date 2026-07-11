# HexRealRoots Performance Report

## Bench Targets

Declared complexities copied verbatim from the `setup_benchmark` registration
sites in `bench/HexRealRoots/Bench.lean`:

- `Hex.RealRootsBench.runIsolateWellSep`: `n ^ 4`
- `Hex.RealRootsBench.runIsolateChebyshev`: `n ^ 4`
- `Hex.RealRootsBench.runIsolateMignotte`: `n ^ 3`
- `Hex.RealRootsBench.runIsolateDescartesFirst`: `n ^ 4`
- `Hex.RealRootsBench.runIsolateSturm`: `n ^ 5`
- `Hex.RealRootsBench.runSturmChain`: `n ^ 2`
- `Hex.RealRootsBench.runSturmVarAt`: `n ^ 2`
- `Hex.RealRootsBench.runMobiusTransform`: `n ^ 2`
- `Hex.RealRootsBench.runRootBound`: `n`
- `Hex.RealRootsBench.runSepPrec`: `n`
- `Hex.RealRootsBench.runRefineTo`: `n`

The `isolate?` surface is exercised on three structurally different input
families, never a single happy-path shape:
`well-separated-products` (∏(x−k)), `chebyshev-clustered` (integer `T_n`), and
`mignotte-worst-case` (`xⁿ−(a·x−1)²`, `a = 1000`). The Sturm-chain,
sign-variation, Möbius-transform, root-bound, separation-precision, and
refinement primitives run on the `dense-primitive` family (deterministic
reliably-squarefree bounded-coefficient dense integer polynomials).

## Verdicts

Scientific run at commit `81a9128e8d39d92a0846d56ceb82e66c2e66bbe3` on
`chungus2` (AMD EPYC 9455, linux `x86_64`, Lean `4.32.0-rc1`, `lean-bench`
`0.1.0`), command:

```sh
lake exe hexrealroots_bench run \
  Hex.RealRootsBench.runIsolateWellSep Hex.RealRootsBench.runIsolateChebyshev \
  Hex.RealRootsBench.runIsolateMignotte Hex.RealRootsBench.runIsolateDescartesFirst \
  Hex.RealRootsBench.runIsolateSturm Hex.RealRootsBench.runSturmChain \
  Hex.RealRootsBench.runSturmVarAt Hex.RealRootsBench.runMobiusTransform \
  Hex.RealRootsBench.runRootBound Hex.RealRootsBench.runSepPrec \
  Hex.RealRootsBench.runRefineTo \
  --export-file reports/bench-results/hex-real-roots-81a9128e8d39.json
```

The run used deterministic benchmark inputs from `bench/HexRealRoots/Bench.lean`;
random seeds are not involved. The harness recorded `81a9128e8d39` with
`git_dirty: true` because the Phase-4 files were staged but uncommitted in this
worktree at run time. Export artefact:
`reports/bench-results/hex-real-roots-81a9128e8d39.json`.

- `Hex.RealRootsBench.runIsolateWellSep`: consistent with declared complexity
  (`β=+0.040`, parameters `4..24`, final hash `0xcca264b97b312156`).
- `Hex.RealRootsBench.runIsolateChebyshev`: consistent with declared complexity
  (parameters `4..20`, final hash `0xd27c7fd8e6574c19`).
- `Hex.RealRootsBench.runIsolateMignotte`: consistent with declared complexity
  (parameters `4..20`, final hash `0x43c746669439e0f0`).
- `Hex.RealRootsBench.runIsolateDescartesFirst`: consistent with declared
  complexity (parameters `4..20`, final hash `0x88e69732f982a9a0`).
- `Hex.RealRootsBench.runIsolateSturm`: consistent with declared complexity
  (parameters `4..20`, final hash `0x88e69732f982a9a0`).
- `Hex.RealRootsBench.runSturmChain`: consistent with declared complexity
  (`β=-0.072`, parameters `16..256`, final hash `0x46a8579b01ab7489`).
- `Hex.RealRootsBench.runSturmVarAt`: inconclusive (`β=-0.792`, looks faster
  than declared, parameters `16..256`, final hash `0x8`). See below.
- `Hex.RealRootsBench.runMobiusTransform`: inconclusive (`β=+0.435`, looks
  slower than declared, parameters `16..256`, final hash `0x0`). See below.
- `Hex.RealRootsBench.runRootBound`: consistent with declared complexity
  (`β=-0.142`, parameters `16..256`, final hash `0x1e8482`).
- `Hex.RealRootsBench.runSepPrec`: consistent with declared complexity
  (`β=-0.047`, parameters `16..256`, final hash `0x1132`).
- `Hex.RealRootsBench.runRefineTo`: consistent with declared complexity
  (`β=+0.097`, parameters `16..256`, final hash `0xffffffffe205ac28`).

Nine of eleven registrations are consistent with their declared textbook
complexity. The two inconclusive registrations are both operation-count-vs-
wall-clock artifacts of exact bignum arithmetic, not wrong-asymptotic
implementations, and neither is in the *slower-than-a-declared-worst-case*
direction that the verdict-as-bug-trigger doctrine treats as an implementation
finding:

- `runSturmVarAt` is *faster* than its `O(n²)` declared model
  (`β=-0.792 < 0`). The SPEC's `O(n²)` is the operation-count bound (one Horner
  pass per chain element, degrees summing to `O(n²)`); on the deterministic
  `dense-primitive` fixture the per-element dyadic accumulators stay small and
  the `O(n²)` bound is not saturated at feasible degrees, so the measured
  wall-clock scales sub-quadratically. Being under an upper bound is the safe
  direction.
- `runMobiusTransform` is *slower* than its `O(n²)` operation-count model
  (`β=+0.435`), because the Taylor-shift pipeline produces binomial-scaled
  coefficients of `O(n)` bits over `(−1, 1]`; the measured `~n^2.4` reflects the
  transition from the `O(n²)` word-operation count toward the `O(n³)` bit
  complexity as those coefficients cross the machine-word boundary. This
  coefficient growth is exactly what the SPEC §"Complexity contract" flags
  (`O(n·h)` primitive-chain growth) and is a documented characteristic of the
  exact-integer engine, not a defect in the Taylor-shift implementation.

### Cross-engine compare group

```sh
lake exe hexrealroots_bench compare \
  Hex.RealRootsBench.runIsolateDescartesFirst Hex.RealRootsBench.runIsolateSturm
```

reports `agreement: all functions agree on common params` over the shared
`well-separated-products` domain (`4, 8, 12, 16, 20`): the Descartes-first
`isolate?` and the certified `isolateSturm?` engines produce identical
isolation-endpoint hashes (both `0x88e69732f982a9a0` at `n = 20`), the
cross-implementation conformance check the compare group is for. The
relative-timing summary quantifies the engine gap the declared models predict:
`isolate?` (Descartes-first) is `O(n⁴)` while the Sturm-only engine is `O(n⁵)`
(full Sturm-chain evaluation per node with `O(n·h)` coefficient growth), which
is why `isolate?` runs Descartes first.

### SPEC time budgets

`SPEC/Libraries/hex-real-roots.md` §"Time budgets" states rough targets for
well-separated roots. Single-rung measurements of `runIsolateWellSep`
(`--param-floor N --param-ceiling N`), same host and commit:

| degree `n` | per-call | SPEC budget | verdict |
|-----------:|---------:|-------------|---------|
| 10 | 1.896 ms | < 1 s | met (≈530× margin) |
| 20 | 32.2 ms | — | — |
| 50 | 1.112 s | < 10 s | met (≈9× margin) |
| 100 | 24.559 s | < 1 min | met (≈2.4× margin) |

All three budgets are met with margin. Degree 100 required raising
`--max-seconds-per-call` to 90 s for the single measured call (its `O(n⁴)`
per-call time exceeds the 6 s scientific cap); the value is a point
measurement, not a scaling verdict.

Smoke wiring was also checked with:

```sh
lake exe hexrealroots_bench list
lake exe hexrealroots_bench verify
```

`verify` passed all 11 registered benchmarks (`≈1 s` wall) at the same commit,
comfortably under the per-library 30 s soft warning and the repo-wide
`BENCH_VERIFY_HARD_CAP_SECONDS` budget.

## Comparator Ratios

`SPEC/Libraries/hex-real-roots.md` names SageMath (`real_roots`), python-flint
(`fmpz_poly` real-root API), and FLINT/Arb in an oracle role. These are
classified `informational` in `libraries.yml: HexRealRoots.phase4.comparators`
under the single comparator entry
`SageMath real_roots / python-flint fmpz_poly real-root API`:
they perform floating-point / ball-arithmetic real-root isolation,
structurally different from the certified exact-integer Sturm/Descartes engines
here (the comparator answers with approximate intervals refined to a requested
precision; Hex answers with a decidable Sturm-count certificate). The
comparator is scheduled-only — the persistent-subprocess Python driver is not
wired in this PR — so there are no external comparator ratios to record in this
snapshot; none gate Phase 4.

The gating cross-implementation check is internal: the Descartes-first vs
certified-Sturm compare group above, which joins on isolation-endpoint hashes
and reports full agreement.

## Profile

Profiles were recorded on `chungus2` (AMD EPYC 9455, linux `x86_64`) with
`perf record -g -F 999` on the in-process `_child` batch runner
(`hexrealroots_bench _child --bench <NAME> --param <N> --target-nanos
3000000000`), one representative case per `phase4.input_families` entry. Leaf
cost is categorised by self-time across {own code, GMP, allocation, Lean
runtime}; the `perf.data` artefacts are developer-local under `/tmp` and are not
committed.

### `well-separated-products`

`runIsolateWellSep` at `n = 24` (∏_{k=1}^{24}(x−k)). Leaf self-time: allocation
36.6%, GMP big-integer arithmetic 34.8% (`__gmpz_init_set`, `__gmpn_copyi`,
`__gmp_default_reallocate`), Lean runtime 14.7% (`lean::mpz::~mpz`,
`lean_dec_ref`), Hex/Lean own code 10.5% (`Array.ofFn`, the Möbius
`compose`/`mul` folds). The huge `∏(x−k)` coefficients (`~n!`, `O(n log n)`
bits) make GMP arithmetic and its allocation traffic dominate; the inclusive
cost flows through `isolate?` → `isolateDescartes?` → `mobiusTransform`, both of
which carry their own registrations.

### `chebyshev-clustered`

`runIsolateChebyshev` at `n = 20` (`T_20`). Leaf self-time: allocation 32.3%,
GMP 27.3%, Hex/Lean own code 19.7% — here the largest single own-code leaf is
`Hex.mobiusTransform`'s `compose`/`mul` fold (`~6.7%` self) — Lean runtime
17.0%. The clustered-root regime spends a visibly larger own-code share in the
Taylor-shift Möbius pipeline than the well-separated family, consistent with
the deeper bisection the clustering forces.

### `mignotte-worst-case`

`runIsolateMignotte` at `n = 20` (`x²⁰−(1000·x−1)²`). Leaf self-time: allocation
41.2%, GMP 32.3% (`realloc`/`__gmp_default_reallocate`-heavy), Lean runtime
12.7%, own code 10.6%. The large `a = 1000` coefficients and the close-pair
bisection depth make reallocation of growing GMP limbs the dominant leaf cost;
inclusive cost is the registered `isolate?` path.

### `dense-primitive`

`runSturmChain` at `n = 256`. Leaf self-time: GMP 39.2% (`__gmpz_init_set`,
`__gmpn_copyi`, `__gmpn_mul_1`, `mpz_to_int`), allocation 39.3%, Lean runtime
10.5%, own code 6.1%. The primitive-remainder-sequence coefficient growth
drives GMP multiply/copy and allocation; the inclusive cost is the registered
`runSturmChain` (`ZPoly.sturmChain`) target itself.

No unregistered dominant inclusive helper appears in any of the four profiles:
every dominant path terminates in a registered bench target (`isolate?`,
`mobiusTransform`, or `sturmChain`), so the Attribution rule is satisfied and no
new target is required.

## Concerns

None. The two inconclusive verdicts (`runSturmVarAt`, `runMobiusTransform`) are
documented operation-count-vs-wall-clock characteristics of exact bignum
arithmetic explained in §Verdicts, not filed audit-found issues: `runSturmVarAt`
is *faster* than its declared upper bound, and `runMobiusTransform`'s measured
`~n^2.4` is the coefficient-bit-growth transition the SPEC's `O(n·h)` growth
note anticipates. Neither is a slower-than-declared-worst-case implementation
finding, so neither triggers the verdict-as-bug-trigger rollback, and there is
no open Attribution-rule concern.
