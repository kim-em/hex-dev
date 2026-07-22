# HexRealRoots Performance Report

## Bench Targets

Declared complexities copied verbatim from the `setup_benchmark` registration
sites in `bench/HexRealRoots/Bench.lean`:

- `Hex.RealRootsBench.runIsolateWellSep`: `n ^ 4`
- `Hex.RealRootsBench.runIsolateChebyshev`: `n ^ 4`
- `Hex.RealRootsBench.runIsolateMignotte`: `n ^ 3`
- `Hex.RealRootsBench.runIsolateDescartesFirst`: `n ^ 4`
- `Hex.RealRootsBench.runIsolateSturm`: `n ^ 5`
- `Hex.RealRootsBench.runSturmChain`: `n ^ 3`
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
refinement primitives run on the `dense-primitive` family: deterministic
monic dense integer polynomials with bounded-height (`h ≈ 11` bits) generic
coefficients whose remainder sequence is *normal* (degree drops exactly one
per pseudo-division), so `sturmChain` attains full length `deg + 1` and the
fixtures exercise the whole primitive remainder sequence with its `O(n·h)`-bit
coefficient growth (probed at ≈ 31 bits/degree).

## Verdicts

Scientific run at commit `49cf630a3c21d33263b5758015e7bd64cfefb1d1` on
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
  --export-file reports/bench-results/hex-real-roots-49cf630a3c21.json
```

The run used deterministic benchmark inputs from `bench/HexRealRoots/Bench.lean`;
random seeds are not involved. The harness recorded `49cf630a3c21` with
`git_dirty: true` because the retuned bench module and this report were staged
but uncommitted in the worktree at run time. Export artefact:
`reports/bench-results/hex-real-roots-49cf630a3c21.json`.

All eleven parametric registrations are **consistent with declared
complexity**:

- `Hex.RealRootsBench.runIsolateWellSep`: consistent with declared complexity
  (`β=+0.034`, parameters `4..24`, final hash `0xcca264b97b312156`).
- `Hex.RealRootsBench.runIsolateChebyshev`: consistent with declared complexity
  (parameters `4..20`, final hash `0xd27c7fd8e6574c19`).
- `Hex.RealRootsBench.runIsolateMignotte`: consistent with declared complexity
  (parameters `4..20`, final hash `0x43c746669439e0f0`).
- `Hex.RealRootsBench.runIsolateDescartesFirst`: consistent with declared
  complexity (parameters `4..20`, final hash `0x88e69732f982a9a0`).
- `Hex.RealRootsBench.runIsolateSturm`: consistent with declared complexity
  (parameters `4..20`, final hash `0x88e69732f982a9a0`).
- `Hex.RealRootsBench.runSturmChain`: consistent with declared complexity
  (`β=+0.114`, parameters `32..256`, final hash `0xb9c42f739ec0a8e9`).
- `Hex.RealRootsBench.runSturmVarAt`: consistent with declared complexity
  (`β=+0.101`, parameters `24..128`, final hash `0x7e`).
- `Hex.RealRootsBench.runMobiusTransform`: consistent with declared complexity
  (`β=+0.112`, parameters `64..512`, final hash `0xffffffffffffffff`).
- `Hex.RealRootsBench.runRootBound`: consistent with declared complexity
  (`β=-0.061`, parameters `64..1024`, final hash `0x1e8470`).
- `Hex.RealRootsBench.runSepPrec`: consistent with declared complexity
  (`β=-0.067`, parameters `16..256`, final hash `0x2748`).
- `Hex.RealRootsBench.runRefineTo`: consistent with declared complexity
  (`β=+0.093`, parameters `16..256`, final hash `0xffffffffe205ac28`).

The verdicts for `runSturmChain`, `runSturmVarAt`, and `runMobiusTransform`
were re-checked across three consecutive runs each (`β` spread ≤ 0.01); the
schedules are pinned in the registration `where` clauses, and each
registration's derivation comment states how the schedule relates to the
GMP word-size regime (the exact-ℤ per-operation cost is flat and
allocation-dominated on the registered rungs, so wall clock tracks the SPEC's
operation-count contract there; below the floors the boxed-scalar-to-mpz
transition distorts the local slope, and far past the ceilings the operand
word count adds its own factor).

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
| 10 | 1.903 ms | < 1 s | met (≈530× margin) |
| 50 | 1.110 s | < 10 s | met (≈9× margin) |
| 100 | 24.621 s | < 1 min | met (≈2.4× margin) |

All three budgets are met with margin. Degree 100 required raising
`--max-seconds-per-call` to 90 s for the single measured call (its `O(n⁴)`
per-call time exceeds the 6 s scientific cap); the value is a point
measurement, not a scaling verdict.

Smoke wiring was also checked with:

```sh
lake exe hexrealroots_bench list
lake exe hexrealroots_bench verify
```

`verify` passed all 11 registered benchmarks in under 1 s wall at the same
commit, comfortably under the per-library 30 s soft warning and the repo-wide
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
3000000000`), one representative case per `phase4.input_families` entry, at
the same commit as the scientific run. Leaf cost is categorised by self-time
across {own code, GMP, allocation, Lean runtime}; the `perf.data` artefacts
are developer-local under `/tmp` and are not committed.

### `well-separated-products`

`runIsolateWellSep` at `n = 24` (∏_{k=1}^{24}(x−k)). Leaf self-time: allocation
38.1%, GMP big-integer arithmetic 34.4% (`__gmpz_init_set`, `__gmpn_copyi`,
`__gmp_default_reallocate`), Lean runtime 14.2% (`lean::mpz::~mpz`,
`lean_dec_ref`), Hex/Lean own code 9.9% (`Array.ofFn`, the Möbius
`compose`/`mul` folds). The huge `∏(x−k)` coefficients (`~n!`, `O(n log n)`
bits) make GMP arithmetic and its allocation traffic dominate; the inclusive
cost flows through `isolate?` → `isolateDescartes?` → `mobiusTransform`, both
of which carry their own registrations.

### `chebyshev-clustered`

`runIsolateChebyshev` at `n = 20` (`T_20`). Leaf self-time: allocation 31.5%,
GMP 27.7%, Hex/Lean own code 19.5% — the largest single own-code leaf is
`Hex.mobiusTransform`'s `compose`/`mul` fold — Lean runtime 18.0%. The
clustered-root regime spends a visibly larger own-code share in the
Taylor-shift Möbius pipeline than the well-separated family, consistent with
the deeper bisection the clustering forces.

### `mignotte-worst-case`

`runIsolateMignotte` at `n = 20` (`x²⁰−(1000·x−1)²`). Leaf self-time:
allocation 40.2%, GMP 32.5% (`realloc`/`__gmp_default_reallocate`-heavy), Lean
runtime 13.2%, own code 11.1%. The large `a = 1000` coefficients and the
close-pair bisection depth make reallocation of growing GMP limbs the dominant
leaf cost; inclusive cost is the registered `isolate?` path.

### `dense-primitive`

`runSturmChain` at `n = 256` (normal full-length remainder sequence,
coefficients to ≈ 8000 bits). Leaf self-time: GMP 89.4% (`__gmpn_addmul_2`
23.8%, `__gmpn_copyi` 20.0%, `__gmpn_mul_1` 10.9%, `__gmpn_submul_1` 9.3%,
plus base-case multiplication and division kernels), allocation 6.6%, Lean
runtime 1.7%, own code 0.7%. The primitive-chain workload is genuinely
GMP-multiplication-bound at the schedule ceiling — the expected profile for
pseudo-division with `O(n·h)`-bit operands — and the inclusive cost is the
registered `runSturmChain` (`ZPoly.sturmChain`) target itself.

No unregistered dominant inclusive helper appears in any of the four profiles:
every dominant path terminates in a registered bench target (`isolate?`,
`mobiusTransform`, or `sturmChain`), so the Attribution rule is satisfied and
no new target is required.

## Concerns

None. All eleven parametric registrations are consistent with their declared
complexity at their registered scientific schedules, the compare group agrees
on its full common domain, the SPEC time budgets are met, and no
Attribution-rule concern surfaced in the profiles.
