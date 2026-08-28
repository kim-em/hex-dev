# HexRoots Performance Report

**Phase 4 is claimed for HexRoots.** The ordered-mode remediation retains
`runMahlerPrec` in mode 1, repairs `runRefineTo` into a second passing mode-1
registration, and promotes the repaired integer-centre `runTaylor` ladder to
mode 1 as well. It selects mode 3 for the other eleven registrations only after
the recorded current-fixture schedules fail to supply a stable scalar wall
model. Every mode-3 benchmark names a canonical hard input and enforces its
body-scoped ceiling independently of process startup. The preserved
Phase-5--7 evidence was rechecked after this remediation, so `libraries.yml`
records `done_through: 7`. This report records the evidence per
[PLAN/Phase4.md](../PLAN/Phase4.md) and
[SPEC/benchmarking.md §Headline reports](../SPEC/benchmarking.md#headline-reports).

The clean ordered-mode artifacts were recorded on quiet `chungus2` (AMD EPYC
9455 48-Core, 96 CPUs), pinned to an idle core, with Lean `4.34.0-rc2`,
lean-bench `0.1.0`, and `git_dirty: false`:

- `reports/bench-results/hex-roots-f5bc993-issue9794-parametric.json` records the Taylor-kernel,
  refinement, certification, and achieved-precision repair schedules.
- `reports/bench-results/hex-roots-f568569-issue9794-n7.json` records the corrected `~n⁷`
  `runIsolateAll` and strategy schedules plus shared-rung hash agreement.
- `reports/bench-results/hex-roots-6aab88b-issue9794-final.json` records both passing mode-1 ladders
  and five repeats of every fixed row; its expected-hash failure on
  `runIsolateAll` is the clean observation that identified the stale row.
- `reports/bench-results/hex-roots-b29031d-issue9794-isolateall.json` is the focused clean rerun after
  refreshing that expectation; all five repeats agree and match.
- `reports/bench-results/hex-roots-4016ee7-issue9794-taylor-n3.json` records the
  current integer-centre cubic-bound attempt, which is inconclusive because the
  ladder is faster than declared.
- `reports/bench-results/hex-roots-ff0724c-issue9794-taylor-n2.json` records the
  same current fixture passing the stronger quadratic mode-1 model.
- `reports/bench-results/hex-roots-28b965d-issue9794-postreview.json` is the
  final all-registration sweep after promoting Taylor and widening the fixed
  ceilings for shared-runner stability; all fourteen selected modes pass,
  every fixed hash matches, and the strategy trio agrees.

Their SHA-256 digests are respectively
`3d74adb2e4821bad833217668ac413865918ef10d8bca1ce5aaf1646b14c1a63`,
`bc17e25a3cb49a0027f2eb5a9f983357100fdf4f7dc076bd7a988f44c6e1c4b7`,
`b027965f3a113a0f3731ddd3385cf344ad2899f215d050afcc023a6792e5f305`,
`8dac7b8607208062b6940563d98ff2f0255f82aae737606aad6e91ca7589a79b`,
`1900396363b66efef68aeca1b9cd3af3ff4bf9c47152a271b9e6a4f5485c90b6`,
`e545b1d784c26f4ddb6698edfe327bf887a367c9bdcf9d48215423129aea3637`,
and `16aa917569d20d145ad7ff99b8bd284c36b79ef4aa4f6872a24de4a700d91520`.

The first four artifacts predate the final rebase. Their stamped source commits
map to surviving, byte-identical relevant-source commits as follows:
`f5bc99321ec → b5fca0ecded`, `f5685691f82 → e2e475f9023`,
`6aab88becd8 → e28328f2d7f`, and `b29031d5383 → d77ea055645`.
For each pair, the diff restricted to `HexRoots/`, `HexRootsMathlib/`, and
`bench/HexRoots/Bench.lean` is empty; only the rebased ancestry differs. The
two Taylor artifacts and the final all-registration sweep stamp surviving
commits directly.

The original Phase-4 sweep is
`reports/bench-results/hex-roots-973c2cd-round5.json`, recorded on quiet
`chungus2` (AMD EPYC 9455 48-Core, 96 CPUs), Lean `4.32.0-rc1`, lean-bench
`0.1.0`. The post-ratchet fixed rerun is
`reports/bench-results/hex-roots-b96b03f-issue8751.json` on the same quiet
host and toolchain. Its `git_dirty: true` records the staged benchmark cap and
post-review core/report update.

## Graeffe and soft-Pellet ratchet

The issue-8751 implementation adds an exact-dyadic soft front end without
changing the certificate proposition. `CoeffBall` keeps a rounded
Gaussian-dyadic centre and an outward-rounded `L¹` error radius; its arithmetic
encloses the locally scaled Taylor coefficients. Each Graeffe step computes
`E(X)² - X O(X)²`, transports all three radius intervals by squaring, and
tests every candidate count before building the next coefficient array.
Shallow centres use one exact Taylor shift rounded to 64 significant bits;
the seeded orbit now reuses the proof-indexed Taylor cache from #8927. Deep
centres use a fully soft 64/128/256-bit ladder. Failure remains
inconclusive and takes the exact cached-shift path. The same machinery gives a
cheap `T₀` discard for far subdivision squares. The combined per-count
kernel preserves the exact-first order below precision 32, avoiding a soft-
setup regression on the small canonical fixed benchmarks, and switches to
soft-first once centre precision is large.

Once a driver round consists entirely of atoms, the Pellet-bearing strategies
whose current certificate discs are already pairwise disjoint now refine those
atoms independently to the requested target and emit only if every local
refinement succeeds and the final discs remain pairwise disjoint.
This avoids carrying already-separated roots through the conservative global
`separationDepth` prefix. The Mathlib companion proves coefficient-ball
enclosure, Graeffe root squaring with multiplicity, transported Pellet root
counts and boundary exclusion, soft `T₀` soundness, and the local finisher's
atom/precision/disjointness/coverage contracts. Failure of the optional path
returns to the unchanged globally normalized completeness proof.

The SPEC budget expression was remeasured on quiet `chungus2` with a compiled
direct driver. The expensive degree-100 row now completes, so it is pinned for
the first time:

| degree | target precision | measured after ratchet | prior checkpoint | new ceiling |
|---:|---:|---:|---:|---:|
| 10 | 32 | 0.130 s median (0.129–0.131 s, 3 calls) | 0.324 s median | 0.3 s |
| 20 | 32 | 3.433 s median (3.421–3.436 s, 3 calls) | 5.830 s median | 7 s |
| 50 | 64 | 52.234–52.289 s (2 calls) | 482.979 s | 105 s |
| 100 | 128 | 630.421 s (10.51 min, 1 call) | >1143 s, no completion | 21 min |

The slower degree-50 call is **9.24× faster** than the preceding 482.979 s
checkpoint. Degree 100 improves from no result inside 19 minutes to a completed
100-atom isolation in 10.51 minutes. The soft front end is gated at polynomial
size 32: the degree-10/20 gains come from the all-atoms local finisher (on top
of #8927's Taylor reuse), while degree 50/100 exercise Graeffe and soft Pellet.
The original 10 s / 1 min aspirations remain stretch targets rather than
gates. The local finisher also makes the deferred 50-case degree-20
python-flint fixture tier practical again; fresh emission is restored instead
of relying on the reduced degree-6–12 subset. The full 56-case
stream (six curated plus fifty seeded) emitted in **308.82 s** and occupied
140 KB; every case returned certificates rather than `none`, and python-flint
replayed all 56 with zero failures.

The ordered-mode audit found that the post-#8839 all-atoms finisher sent every
atom directly through globally normalized refinement, bypassing the bounded
lineage-local loop that made the Pellet-bearing paths fast. The finisher now
tries the proven bounded local refinement first and retains complete normalized
refinement as fallback. The final pairwise-disjointness check and the Mathlib
coverage/readiness proofs cover both branches, so the repair restores the
optimization without weakening the soundness-motivated fallback.

On identical inputs and hashes, direct pinned measurements changed Pellet-only
from about 10.128 s to 2.508 s, combined from 10.164 s to 2.462 s, and
`runIsolate` from 2.923 s to 0.498 s. NK-only stayed near 9.2 s. The clean final
five-repeat medians are `runIsolate` 0.496 s, `runIsolateAll` 8.521 s, NK-only
9.187 s, Pellet-only 2.483 s, and combined 2.471 s. The fixed table below
records the current medians, body-scoped budgets, and refreshed hashes.

## Taylor-shift reuse ratchet

Component certification now computes one exact Taylor shift at its base centre
and shares it between the witness and Newton kernels. The exact Pellet
candidate fallback shares that shift across all attempted root counts; the NK
route shares it between its base witness and speculative Newton step. Because
the widened Pellet fallback is concentric with the NK enclosure, the default
combined route also reuses that same shift across the strategy boundary under
an exact centre-equality guard. A recentred candidate still gets its own shift
for re-certification. The cache is indexed by its polynomial and centre and
carries the coefficient equality as a proof field, so this changes evaluation
work without weakening the certificate interface.

On the canonical degree-128 pinned-NK `runCertify` case, five-repeat medians on
`chungus2` fell from **6.655 ms** to **4.434 ms** (**33.4%**), with the result
hash unchanged at `0x1698ec123da6112f`. The canonical degree-12
`runIsolateAll` case changed from 9.172 s to 8.916 s; its deeper subdivision
work dominates the saved certification shifts. The final five-repeat ranges
were 4.400–4.443 ms and 8.888–9.039 s respectively.

The SPEC budget table was remeasured with the compiled expression
`isolateAll? (seededPoly degree) target #[Component.cauchy ...]`. The degree-10
and degree-20 rows used five cold measured calls (`warmup := false`); the
degree-50 row used one cold call because each invocation takes several minutes.
All runs used `Hex.RootsBench.runIsolateAll` with temporary fixture-only
degree/target substitutions, `--ignore-expected-hash`, and JSON export. Those
fixture substitutions were restored after measurement. Machine-readable
developer-local artefacts are `/tmp/hexroots-8751-d10.json`,
`/tmp/hexroots-8751-d20.json`, and `/tmp/hexroots-8751-d50.json`.

These are current-tree regression measurements, not claimed controlled
before/after speedups: the older issue numbers were single calls from earlier
trees. The ceilings are ratcheted to roughly twice the current measurement:

| degree | target precision | measured | regression ceiling |
|---:|---:|---:|---:|
| 10 | 32 | 0.324 s median (0.285–0.343 s, 5 calls) | 0.7 s |
| 20 | 32 | 5.830 s median (5.426–7.098 s, 5 calls) | 12 s |
| 50 | 64 | 482.979 s (8.05 min, 1 call) | 14 min |

This table is the earlier Taylor-reuse-only checkpoint. The Graeffe and
soft-Pellet table above supersedes its ceilings and completes the next
optimization steps tracked by issue #8751.

## Bench Targets

Mode-1 parametric registrations:

- `runTaylor`: `n²` on seeded bounded-coefficient polynomials at centre 1,
  degrees `64, 128, 256, 512, 1024, 2048`.
- `runMahlerPrec`: `n` on seeded bounded-coefficient polynomials, degrees
  `64, 128, 256, 512, 1024, 2048, 4096`.
- `runRefineTo`: `t²` on the achieved-precision ladder
  `32773, 65541, 131077, 262149, 524293`.

Mode-3 fixed registrations (`repeats = 5`) are `runIsolate`
(fixed-separation degree 8), `runWitnessCheck`, `runNkWitnessCheck`, and
`runNewtonSquare` (bounded-height degree 128), `runRefine1` (degree 8),
`runCertify` (degree-128 pinned NK branch), `runIsolateAll` (fixed-separation
degree 12), the three strategy drivers (shared `linProdPoly 10`), and
`runSameRoot`. Their adjacent registration comments give the cost derivation,
failed stronger-mode route, hard input, measured baseline, and ceiling.
lean-bench#67 continues to track structured op-count/operand-growth reporting
for the GMP-transition cases.

### Superseded round-one target record

Declared complexities copied verbatim from the `setup_benchmark` registration
sites in `bench/HexRoots/Bench.lean`. These are *wall-time* models: the SPEC
op-count contract multiplied by the family's working-bit-length growth `B`
where that growth is asymptotically significant on the schedule (each
registration's comment records the reconciliation).

- `Hex.RootsBench.runTaylor`: `n * n`
- `Hex.RootsBench.runMahlerPrec`: `n`
- `Hex.RootsBench.runWitnessCheck`: `n * n`
- `Hex.RootsBench.runNkWitnessCheck`: `n * n`
- `Hex.RootsBench.runNewtonSquare`: `n * n`
- `Hex.RootsBench.runRefine1`: `n * n`
- `Hex.RootsBench.runCertify`: `n * n`
- `Hex.RootsBench.runIsolateAll`: `n * n * n * n * n`
- `Hex.RootsBench.runIsolate`: `n * n * n * n * n`
- `Hex.RootsBench.runRefineTo`: `t * t`
- `Hex.RootsBench.runIsolateNk`: `n * n * n * n * n`
- `Hex.RootsBench.runIsolatePellet`: `n * n * n * n * n`
- `Hex.RootsBench.runIsolateNkThenPellet`: `n * n * n * n * n`
- `Hex.RootsBench.runSameRoot`: fixed benchmark, `repeats = 5`

Three input families (`libraries.yml: HexRoots.phase4.input_families`):
`seeded-dense` (seed-`0xC0FFEE` dense integer polynomials, coefficients in
`[-10, 10]`, generically distinct irrational roots — the whole-polynomial
drivers, `taylor`, `mahlerPrec`, `refine1`, `certify`), `wilkinson-linprod`
(`∏(X−j)`, `j = 1..n`, integer roots — the witness/Newton primitives and the
dual-route compare group), and `refine-fixed` (the degree-3 `(x−1)(x−2)(x+3)`
whose atom `refineTo?`/`sameRoot` sharpen).

### Op-count-vs-wall reconciliation (Phase4.md performance rationale)

The current registrations reconcile operation counts with each fixture's
working-bit-length growth as follows:

- **`runTaylor` is `n²`.** Repeated synthetic division performs `O(n²)` exact
  multiply/adds. The repaired centre is the integer `1`, so it introduces no
  denominator growth and centre multiplication is unit scaling. A clean
  `64..2048` attempt is consistent at `n²` (`β=+0.110`); the conservative
  `n³` bit-cost attempt is inconclusive because the ladder is faster than
  declared by `~n^0.882`.
- **`runMahlerPrec` is `n`; the witness/Newton/refinement primitives have
  `n²` operation shapes.** `mahlerPrec` remains word-sized on its bounded-height
  family. The other reachable schedules cross GMP allocation/limb transitions,
  so their honestly derived scalar models do not have stable constants and are
  enforced in mode 3 instead.
- **`runIsolateAll`, `runIsolate`, and the three compare-group drivers have a
  `~n⁷` candidate wall model on their current families.** The SPEC supplies
  `O(n³·B²)`. Both `separatedPoly n` and `linProdPoly n` have
  `log‖p‖∞ = Θ(n log n)`, hence
  `B = prec + n·log‖p‖∞ = Θ(n² log n)` at the isolation depth and the
  wall candidate is `n⁷ log²n`. The report suppresses the polylogarithm as
  `~n⁷`; every reachable schedule remains inconclusive, so none is fitted to a
  lower transition-band power.
- **`runRefineTo` is `t²`.** At fixed degree the achieved Newton precision `t`
  parameterizes the actual work; the dominant final witness performs a fixed
  number of `t × t` schoolbook products.

## Verdicts

`runTaylor`, `runMahlerPrec`, and `runRefineTo` use **mode 1, two-sided
parametric**. Taylor's integer-centre repair produces a passing quadratic wall
model on `64..2048`. The Mahler-precision linear model is derived from the
coefficient scan with bounded coefficient height and passes in both directions.
For `runRefineTo`, parameterizing by the achieved Newton precision removes the
raw-target staircase and makes the derived `t²` model measurable.

The other eleven registrations use **mode 3, enforced absolute ceilings**
under
[`SPEC/benchmarking.md` §Choosing the complexity claim](../SPEC/benchmarking.md#choosing-the-complexity-claim).
Mode 1 was attempted first. The clean experimental artifact records:

| registration or group | attempted current-fixture schedule/model | result |
|---|---|---|
| `runTaylor` | integer-centre seeded degrees `64..2048`, first conservative `n³`, then stronger `n²` | `n³` inconclusive (`β=-0.882`); **`n²` consistent (`β=+0.110`)**, promoted to mode 1 |
| `runWitnessCheck` | degree `64..384`, `n³` | inconclusive, `β=-0.411` |
| `runNkWitnessCheck` | degree `64..512`, `n³` | inconclusive, `β=-0.457` |
| `runNewtonSquare` | degree `64..512`, `n³` | inconclusive, `β=-0.526` |
| `runRefine1` | smooth separated degrees `4,6,8,10,12,14`, `n²` | inconclusive, normalized cost `23133..52721` |
| `runCertify` | pinned-NK degree `64..384`, `n³` | inconclusive; excluding the dropped warmup rung, normalized cost on `96..384` is non-monotone `2.542 → 1.367 → 1.533`; at degree 512 `pinnedCertify?` returns `none` (hash `0x0`), so the artifact's headline slope/`cMin` include a degenerate rung and are not load-bearing |
| `runIsolateAll` | smooth separated degrees `4,6,8,10,12,14`, corrected `~n⁷` | inconclusive, `C=392.544..208.586` on verdict rungs |
| `runRefineTo` | achieved precision `32773..524293`, `t²` | **consistent**, `β=-0.030`, promoted to mode 1 |
| strategy trio | `linProdPoly` degrees `2,3,4,5,6,8,10`, corrected `~n⁷` | all inconclusive: NK `β=-0.460`, Pellet `-1.168`, combined `-1.149`; hashes agree at every rung |

The repaired schedules therefore rule out a stable scalar wall model for nine
of the ten outstanding fixed routes and recover the tenth as mode 1. The
separate current-fixture Taylor repair recovers another mode-1 registration:
the quadratic model passes, while the conservative cubic bound is observably
too high. `runIsolate` has the same honestly derived `~n⁷` shape, but degree 8 is
already the canonical mid-schedule hard case and extending far enough to reach
the asymptote exceeds the usable per-call range. `runSameRoot` is one exact
comparison with no meaningful family parameter. Mode 2 is unavailable because
the published SPEC bounds bit operations rather than the profiled executable
wall time, and no cited result covers the dominant transition-band behavior.
This exhausts stronger modes before selecting mode 3. For these eleven
operations, asymptotic regression detection is given up; the enforced absolute
ceiling is the performance gate.

Quiet-machine commands:

```sh
taskset -c "$(python3 scripts/bench/idle_core.py)" lake exe hexroots_bench run \
  <repaired kernel names> --export-file \
  reports/bench-results/hex-roots-f5bc993-issue9794-parametric.json
taskset -c "$(python3 scripts/bench/idle_core.py)" lake exe hexroots_bench run \
  <corrected n7 isolation names> --export-file \
  reports/bench-results/hex-roots-f568569-issue9794-n7.json
taskset -c "$(python3 scripts/bench/idle_core.py)" lake exe hexroots_bench run \
  <all 14 registration names> --export-file \
  reports/bench-results/hex-roots-6aab88b-issue9794-final.json
taskset -c "$(python3 scripts/bench/idle_core.py)" lake exe hexroots_bench run \
  Hex.RootsBench.runTaylor --export-file \
  reports/bench-results/hex-roots-4016ee7-issue9794-taylor-n3.json
taskset -c "$(python3 scripts/bench/idle_core.py)" lake exe hexroots_bench run \
  Hex.RootsBench.runTaylor --export-file \
  reports/bench-results/hex-roots-ff0724c-issue9794-taylor-n2.json
taskset -c "$(python3 scripts/bench/idle_core.py)" lake exe hexroots_bench run \
  <all 14 registration names> --export-file \
  reports/bench-results/hex-roots-28b965d-issue9794-postreview.json
```

The selected mode-1 verdicts are consistent:

| registration | model | verdict | evidence | final hash |
|---|---|---|---|---|
| `runTaylor` | `n²` | consistent | final sweep `β=+0.110`, `cMin=138.570`, `cMax=326.486` over `64..2048`; leading warmup rung dropped | `0x1f1070e211681de7` |
| `runMahlerPrec` | `n` | consistent | final sweep `β=-0.000`, `cMin=5.705`, `cMax=6.553` over `64..4096` | `0x10805` |
| `runRefineTo` | `t²` | consistent | final sweep `β=-0.070`, `cMin=0.017`, `cMax=0.019`; leading warmup rung dropped (repair sweep `β=-0.030`) | `0x482ae3757e2b9db3` at achieved precision 524293 (`0x8dd3e4ee56489bf8` at 131077) |

(`runIsolate` was parametric at `n⁵` in the previous revision of this
report and its `4..10` range check passed, but post-merge review showed
the adjacent derivation could not support `n⁵` on this family:
`separatedPoly n` has `log ‖p‖∞ = Θ(n·log n)`, so the `separationDepth`
floor makes the emission-level bit-length `B = Θ(n²·log n)` and the
honestly derived wall from `O(n³·B²)` is `~n⁷`, unreachable in any usable
per-call band. Per the no-fitting rule the registration was demoted to
a fixed case rather than kept on a fitted model; see issue #8750.)

The mode-3 ceilings are independent per operation and enforced inside the
registered body by `budgeted`; returning its sentinel makes `expectedHash`
fail. `maxSecondsPerCall` is deliberately only a child-process safety cap.
They are rounded operation-by-operation to at least 8× the clean pinned-core
median so the absolute gate remains stable on shared merge-gating runners.
The wrapper executes on every calibrated inner iteration; lean-bench checks the
first iteration's hash, so a deterministic ceiling violation there carries the
sentinel into verification. `runSameRoot`'s distinct fine representative is
prepared in each child initializer, outside the timed body, raising every
child's spawn floor by about 0.3 s without affecting the operation ceiling.
The final post-review artifact supplies five clean repeats for all eleven
selected fixed rows after refreshing the `runIsolateAll` expectation. Every
observed hash agrees across repeats and matches its registered expectation:

| registration | canonical hard input | ceiling | clean median | hash |
|---|---|---:|---:|---|
| `runWitnessCheck` | bounded-height degree 128 | 20 ms | 2.385 ms | `0xb` |
| `runNkWitnessCheck` | bounded-height degree 128 | 19 ms | 2.291 ms | `0xb` |
| `runNewtonSquare` | bounded-height degree 128 | 18 ms | 2.185 ms | `0x450307c7dcbe905c` |
| `runRefine1` | fixed-separation degree 8 | 18 ms | 2.152 ms | `0x6dd99fc71c5233ae` |
| `runCertify` | pinned-NK degree 128 | 36 ms | 4.498 ms | `0x1698ec123da6112f` |
| `runIsolateAll` | fixed-separation degree 12 | 70 s | 8.521 s | `0x5e4b3fd1d798497a` |
| `runIsolate` | fixed-separation degree 8 | 4 s | 495.557 ms | `0x16c307fd2a36d31e` |
| `runIsolateNk` | `linProdPoly 10` | 75 s | 9.187 s | `0xda631bdf13415a4f` |
| `runIsolatePellet` | `linProdPoly 10` | 20 s | 2.483 s | `0xda631bdf13415a4f` |
| `runIsolateNkThenPellet` | `linProdPoly 10` | 20 s | 2.471 s | `0xda631bdf13415a4f` |
| `runSameRoot` | distinct coarse/131077-bit representatives | 1 ms | 15.956 µs | `0xb` |

The refreshed `runIsolateAll` hash is `0x5e4b3fd1d798497a`. The repaired
`runRefineTo` ladder records `0x8dd3e4ee56489bf8` at the old fixed precision
131077 and `0x482ae3757e2b9db3` at its final rung, replacing both stale rows from
the dirty post-ratchet export. The `runIsolateAll` digest is unchanged from
`main`'s post-#8839 output; the local-finisher repair changes timing, not this
observable.

The repaired finisher does select tighter dyadic representatives for the full
HexRoots conformance corpus. Its 56-case fixture was regenerated and replayed
against python-flint with zero failures. The representation change propagates
to four HexNumberField fixed hashes (`runRoots`, `runLazyAddLadder`,
`runQAdjoinRootsLadder`, and `runAlgebraicRootsLadder`); their refreshed
expectations match current-tree verification and the CI observations that
exposed the fixture drift. The downstream
HexNumberField fixture was regenerated as well: six box/result records now
carry the tighter representatives, while the HexNumberFieldTower emitter
reproduces its existing 30-record fixture byte for byte.

### Superseded round-one verdict record

Scientific run, one command, exporting
`reports/bench-results/hex-roots-b08a66cce522.json`:

```sh
lake exe hexroots_bench run \
  Hex.RootsBench.runTaylor Hex.RootsBench.runMahlerPrec \
  Hex.RootsBench.runWitnessCheck Hex.RootsBench.runNkWitnessCheck \
  Hex.RootsBench.runNewtonSquare Hex.RootsBench.runRefine1 \
  Hex.RootsBench.runCertify Hex.RootsBench.runIsolateAll \
  Hex.RootsBench.runIsolate Hex.RootsBench.runRefineTo \
  Hex.RootsBench.runIsolateNk Hex.RootsBench.runIsolatePellet \
  Hex.RootsBench.runIsolateNkThenPellet \
  --export-file reports/bench-results/hex-roots-b08a66cce522.json
```

Inputs are deterministic; no random seeds are involved. Every verdict verbatim
(`β` is the residual log-log slope of `C = per-call / model`; the harness calls
a run *consistent* iff `|β| ≤ 0.15`, or, on a log-x range too narrow to fit a
slope, iff `cMax/cMin ≤ max(1.5, exp(0.15·xRange))`):

| registration | model | verdict | β / range | final-param hash |
|---|---|---|---|---|
| `runTaylor` | `n²` | **inconclusive** | `β=+0.415` (slower by `~n^0.42`) | `0x1242736d713af35b` @256 |
| `runMahlerPrec` | `n` | consistent | `β=−0.148` | `0xc83…` @256 |
| `runWitnessCheck` | `n²` | **inconclusive** | `β=−0.227` (faster by `~n^0.23`) | `0xb` @16 |
| `runNkWitnessCheck` | `n²` | consistent | `β=−0.095` | `0xb` @16 |
| `runNewtonSquare` | `n²` | **inconclusive** | `β=+0.198` (slower by `~n^0.20`) | `0x450307c7dcbe905c` @16 |
| `runRefine1` | `n²` | consistent | range check (`cMax/cMin=1.33`) | `0x67a4e6fe2931f85d` @12 |
| `runCertify` | `n²` | **inconclusive** | range check (`cMax/cMin=2.38`) | `0x7c47cfcdaf58dbfb` @12 |
| `runIsolateAll` | `n⁵` | **inconclusive** | `β=+0.266` (slower by `~n^0.27`) | `0xe04d9a38cc8e2885` @20 |
| `runIsolate` | `n⁵` | **inconclusive** | range check (`cMax/cMin=1.57`) | `0x83846a2a71bf4090` @16 |
| `runRefineTo` | `t²` | **inconclusive** | range check (`cMax/cMin=2.96`) | `0x9de10954e8ec1aa1` @256 |
| `runIsolateNk` | `n⁵` | consistent | range check (`cMax/cMin=1.25`) | `0x6519358031d0ea70` @6 |
| `runIsolatePellet` | `n⁵` | **inconclusive** | range check (`cMax/cMin=1.68`) | `0x6519358031d0ea70` @6 |
| `runIsolateNkThenPellet` | `n⁵` | **inconclusive** | range check (`cMax/cMin=1.81`) | `0x6519358031d0ea70` @6 |

**4 consistent, 9 inconclusive.** The fixed `runSameRoot` benchmark:
median `132 ns` (min `130`, max `134`, `×2^13` inner repeats), all repeats
agree on hash `0xb`, matching the registered `expectedHash`.

The nine inconclusive verdicts are analysed in the historical calibration
record below. They fall into four
root causes, none of which is a wrong-asymptotic *implementation* bug that a
rollback of the implementation would fix: the fixed non-integer Taylor
centre's transition-band growth, the startup-dominated microsecond band of the
small-degree witness benches, the seeded family's degree-dependent (hence
non-power-law) root geometry, and `refineTo`'s Newton-doubling precision
quantisation. They are benchmark-family / schedule findings.

## Comparator Ratios

Declared informational comparator: `python-flint fmpz_poly.complex_roots`,
scoped to the whole-polynomial isolation surface.

The final fixed strategy trio shares `linProdPoly 10`; all hashes are
`0xda631bdf13415a4f`, preserving the bench-side agreement regression. The
agreement was also checked directly with:

```text
lake exe hexroots_bench compare Hex.RootsBench.runIsolateNk Hex.RootsBench.runIsolatePellet Hex.RootsBench.runIsolateNkThenPellet
agreement: all functions agree on output
```

The clean issue-9794 medians are NK `9.187 s`, Pellet `2.483 s`, and
NK-then-Pellet `2.471 s`. The bounded local-finisher repair therefore restores
the Pellet-bearing routes' earlier ordering. The corrected scaling experiment
over degrees `2..10` remains informational: normalized against the independently
derived `~n⁷` model, NK, Pellet, and combined have residuals `-0.460`, `-1.168`,
and `-1.149`. No asymptotic conclusion is drawn from this transition band.

`HexRoots/SPEC/hex-roots.md` names python-flint (`fmpz_poly.complex_roots`, the
ci-tier oracle) as the sole Phase-4 performance comparator. It is classified
`informational` in `libraries.yml: HexRoots.phase4.comparators` and does not
gate Phase 4. The per-library yardstick is the SPEC's time budgets, not a
constant-factor `1×` goal, because FLINT's multiprecision ball engine is
structurally different from this library's decidable exact-integer
certificates. MPSolve remains a local correctness oracle for the adversarial
corpus, not a Phase-4 performance comparator.

### python-flint (`informational`, run)

`scripts/bench/hexroots_flint_compare.py` times `fmpz_poly.complex_roots()` at
`ctx.prec = 32` on the same fixed-separation products as the whole-polynomial
drivers. The final fixed canonical points are `runIsolate` at degree 8 and
`runIsolateAll` at degree 12. A pre-demotion `runIsolateParam` diagnostic
ladder at degrees `4..10` is retained solely to show the ratio's shape; it is
not an asymptotic verdict or a registered complexity claim. The degree-12
comparison matches `runIsolateAll`'s target precision 32. The `runIsolate`
diagnostic and canonical rows are same-input orientation rather than
equal-precision work: Lean continues to its degree-dependent
`separationDepth`, while FLINT starts from `ctx.prec = 32` and internally
raises precision as needed to certify its balls. All degrees run in one warm
process. The measured per-call overhead
(`complex_roots` on `x²−2`) is `1.111 µs`, below 5 % of comparator wall time at
every rung, so no adjusted column is required. Data:
`reports/bench-results/hex-roots-flint-round5.json`; diagnostic Lean values
come from `hex-roots-isolate-diagnostic-round5.json`. The FLINT inputs and
hashes are unchanged, while the canonical Hex values below are refreshed from
the clean issue-9794 artifact.

Diagnostic ratio shape (unregistered `runIsolateParam` helper):

| degree | hex | flint | ratio hex/flint |
|---:|---:|---:|---:|
| 4 | 7.078 ms | 63.419 µs | 111.6 |
| 5 | 18.299 ms | 93.254 µs | 196.2 |
| 6 | 43.282 ms | 109.722 µs | 394.5 |
| 7 | 113.879 ms | 135.967 µs | 837.5 |
| 8 | 159.871 ms | 215.234 µs | 742.8 |
| 9 | 346.203 ms | 301.942 µs | 1146.6 |
| 10 | 597.162 ms | 406.227 µs | 1470.0 |

Final registered canonical points:

| degree | Lean surface | hex | flint | ratio hex/flint |
|---:|---|---:|---:|---:|
| 8 | `runIsolate` | 495.557 ms | 215.234 µs | 2302.4 |
| 12 | `runIsolateAll` | 8.521 s | 591.777 µs | 14400.0 |

**Trend.** On the diagnostic ladder, apart from the degree-8 local dip, the
ratio diverges from `112×` at degree 4 to `1470×` at degree 10; the
equal-precision canonical `runIsolateAll` point is `14400×` at degree 12. That
direction is expected: the Lean drivers perform certified exact isolation
with degree- and precision-dependent exact-dyadic work, while FLINT uses a
structurally different multiprecision ball algorithm. No scalar asymptotic
model is asserted for the diagnostic curve. Under the informational-comparator doctrine,
expected divergence between documented different complexity classes is an
orientation finding rather than a Concern; the absolute SPEC time budgets
remain the performance yardstick.

The other registered surfaces are the separation-bound helper and internal
Taylor/witness/Newton, component/refined-atom, or individual-strategy kernels.
The library SPEC declares `no-comparable-surface-in-named-comparator` for them
because python-flint does not expose those operations as callable APIs. With only one
declared Phase-4 comparator, the multi-comparator per-family plot rule does not
apply; `scripts/plots/hex-roots-comparator.py` remains a reproducible optional
plot of the shared fixed-separation ladder.

### Historical parametric cross-strategy run

```sh
lake exe hexroots_bench compare \
  Hex.RootsBench.runIsolateNk Hex.RootsBench.runIsolatePellet \
  Hex.RootsBench.runIsolateNkThenPellet
```

reports `agreement: all functions agree on common params` over the shared
`wilkinson-linprod` domain (`n = 2, 3, 4, 5, 6`): the strategy-invariant
`rootsDigest` (atom count + integer-grid centre buckets) is identical across
`.nk`, `.pellet`, and `.nkThenPellet` (final hash `0x6519358031d0ea70` at
`n = 6` for all three), the cross-implementation conformance check the compare
group exists for. This is the dual-route experiment's measurement record. The
per-degree strategy timings and the `pellet/nk` ratio:

| degree | `.nk` | `.pellet` | `.nkThenPellet` | pellet/nk |
|---:|---:|---:|---:|---:|
| 2 | 0.414 ms | 0.273 ms | 0.288 ms | 0.659 |
| 3 | 2.203 ms | 1.832 ms | 2.050 ms | 0.832 |
| 4 | 8.227 ms | 5.781 ms | 6.220 ms | 0.703 |
| 5 | 27.71 ms | 14.71 ms | 15.18 ms | 0.531 |
| 6 | 78.35 ms | 34.97 ms | 36.16 ms | 0.446 |

On this integer-root family the **Pellet-only route is the faster one, and
increasingly so with degree** (ratio `0.66 → 0.45`): Pellet certifies at a
coarser precision than the sup-norm Newton-Kantorovich witness needs, so the
`.nk` route subdivides more levels. `.nkThenPellet` tracks `.pellet` closely
(NK does not fire early on these coarse squares, so the default falls through to
Pellet after one NK attempt). This is a genuine dual-route finding for the
companion's eventual route-retirement decision: on well-separated integer roots
Pellet wins; the NK route's advantage (exact first-order bounds, no `√2`) is not
visible on this family at these degrees.

## Profile

`perf record -g -F 999` on the in-process `_child` batch runner
(`hexroots_bench _child --bench <NAME> --param <N> --target-nanos 3000000000`),
one representative case per `phase4.input_families` entry. The seeded profile
is retained from the original family audit because that bounded-height path is
unchanged. The fixed-separation, current degree-10 strategy, and refine-fixed
profiles were refreshed after the local-finisher repair; refine-fixed uses
achieved precision 131077. Leaf self-time is categorised across
{own code, GMP, allocation, Lean runtime}; own code = `l_Hex_*`, `lp_Hex_*`,
`l_Dyadic_*`, `l_GaussDyadic_*`, and the dyadic-mantissa integer leaves
(`l_Int_*`). `perf.data` artefacts are developer-local under `/tmp` and are not
committed.

### `seeded-dense` — `runIsolateAll` at `n = 16` (2447 samples)

Leaf self-time: GMP 32.9 % (`__gmpz_init_set` 7.6 %, `__gmpz_cmp_si` 2.6 %,
`__gmpz_add` 2.1 %, `__gmpz_realloc`/`__gmpn_*`), allocation 21.5 %
(`malloc` 7.5 %, `cfree` 7.1 %, `realloc`, `mi_*`), Lean runtime 22.7 %
(`lean_dec_ref_cold`, `lean::mpz_to_int`, `lean::mpz::~mpz`), own code 19.0 %
(`l_Dyadic_add` 3.8 %, `l_Dyadic_mul` 1.9 %, `l_Int_trailingZeros_aux`,
`lp_Hex_…taylor`); 96.2 % classified. The working bit-length reaches multiple
GMP words, so big-integer arithmetic and its allocation/box-unbox traffic
dominate, flowing inclusively through the registered `isolateAll?` →
`taylor`/`witnessCheck` path. This establishes the growing-precision regime;
the corrected family-specific wall derivation used for ordered-mode selection
is `~n⁷`.

### `fixed-separation-product` — fixed `runIsolate` at degree 8 (3758 samples)

Quiet-host `perf record -g -F 999` across four final canonical repeats
(`1.980 s` total, hash `0x16c307fd2a36d31e`) retained **3758 samples**. Leaf
self-time is 97.5 % classified: GMP 33.6 % (`__gmpn_divrem_1` 6.5 %,
`__gmpz_init_set` 6.3 %), Lean runtime 22.6 %, own dyadic/integer code 21.2 %
(`Int.trailingZeros` 4.5 %, `Dyadic.add` 4.4 %, `Dyadic.mul` 2.9 %), and
allocation 20.1 %; 2.6 % is other/unresolved. Inclusive cost terminates in the
registered fixed `runIsolate` driver and exercises the restored bounded local
finisher. Artefact: developer-local `/tmp/hexroots-9794-isolate.perf`.

### `wilkinson-linprod` — `runIsolateNkThenPellet` at `n = 10` (2755 samples)

The current fixed canonical call took `2.421 s` and returned
`0xda631bdf13415a4f`. Leaf self-time is 97.9 % classified: GMP 38.2 %
(`__gmpn_divrem_1` 9.0 %, `__gmpz_init_set` 8.2 %), Lean runtime 23.3 %,
allocation 22.2 %, and own dyadic/integer code 14.2 % (`Dyadic.add` 4.2 %,
`Dyadic.mul` 2.1 %, `Int.shiftLeft` 1.8 %); 2.1 % is other/unresolved. The
inclusive path is the registered combined strategy driver through the restored
local finisher. Artefact: developer-local
`/tmp/hexroots-9794-combined.perf`.

### `refine-fixed` — `runRefineTo` at achieved precision 131077 (~4000 samples)

The refreshed current profile covers two timed calls and **1270 retained
samples** (`308.830 ms` per call, hash `0x8dd3e4ee56489bf8`). Leaf self-time is
97.4 % classified: GMP 88.6 %, allocation 5.6 %, Lean runtime 2.6 %, and own
code 0.6 %; 2.6 % is other/unresolved. GMP is dominated by
`__gmpn_divrem_1_x86_64` 71.3 % and `__gmpn_copyi_x86_64` 15.0 %. The
high-precision reciprocal/division is therefore the actual canonical
bottleneck, inclusively terminating in registered `refineTo?`. Artefact:
developer-local `/tmp/hexroots-9794-refineto.perf`.

**Attribution rule.** Every dominant inclusive path terminates in a registered
bench target (`isolateAll?`/`isolate`, `taylor`, `witnessCheck`/
`nkWitnessCheck`, `newtonSquare`, `refine1`/`certify`, `refineTo?`), so no
unregistered helper dominates and no new target is required. (Lean's
closure-call unwinding fragments some inclusive attribution into an unresolved
`0x1` frame ~6 %, a `perf`/RTS artefact, not an unregistered hot path.)

## Historical Calibration Record

The preceding Phase-3 audit blocked Phase 4 and kept `done_through` at `3`.
Each item below is retained as historical evidence together with its diagnosis
and then-current proposed resolution. The clean issue-9794 experiment above
attempts those repairs under the ordered rule: only the achieved-precision
`runRefineTo` route reaches a stable scalar model, while the remaining routes
justify their now-enforced fixed ceilings. None was a wrong-asymptotic
implementation bug that required rolling back an executable definition.

1. **`runIsolate`, `runIsolateAll` inconclusive — seeded-family
   non-monotonicity.** At `n⁵` the residual is small (`β=+0.266` for
   `isolateAll`), but the seeded polynomials' degree-dependent root geometry
   makes wall time non-monotonic in `n` (e.g. `isolateAll` at `n=18` is
   `6.52 s` but `n=20` is `4.02 s`, because `seededPoly 18` happens to have a
   closer root pair), so no power-law fit is clean. Resolution: replace the
   per-degree-varying seed with a family whose isolation difficulty is smooth
   in `n` (e.g. a fixed root-separation product), then re-measure `n⁵`.

2. **`runIsolatePellet`, `runIsolateNkThenPellet` inconclusive — narrow-range
   range check.** `n⁵` is the right model (`runIsolateNk` on the same domain is
   *consistent*), but the 5-rung `n=2..6` schedule is too narrow for a slope
   fit, so the verdict falls to the multiplicative range check, which the
   slightly-sub-`n⁵` Pellet growth (`cMax/cMin = 1.68`, `1.81`) fails against
   the `1.5` noise floor. Resolution: widen the compare-group schedule
   (larger degrees, or in-fill rungs) so a slope fit governs the verdict.

3. **`runTaylor` inconclusive — non-integer-centre transition band.** The fixed
   centre `1/4 + i/8` gives `Θ(n)` denominator growth, so wall scales
   `~n^{2.25}` (probed to `n=1024`), between the `n²` op-count and the `n³`
   bit-op asymptote; neither clean power is consistent (`n²` gives `β=+0.42`).
   The analogous hex-real-roots `runMobiusTransform` is consistent at `n²`
   precisely because it uses an *integer* interval endpoint. Resolution: an
   integer Taylor centre for the benchmark, or declare and reach the `n³`
   multiplication-bound regime (operand word counts an order of magnitude past
   the wallclock cap).

4. **`runWitnessCheck`, `runNewtonSquare`, `runCertify` inconclusive —
   startup-dominated microsecond band.** These run in `1–45 µs` on the small
   `n ≤ 12/16` schedules, where the fixed per-call overhead (array allocation,
   checksum) makes the `C` curve U-shaped (`witnessCheck` `β=−0.23`,
   `newtonSquare` `β=+0.20`, `certify` monotone-decreasing), so `n²` does not
   fit cleanly even though the operands are provably flat. `runRefine1` and
   `runNkWitnessCheck` on the same band happen to pass. Resolution: raise the
   schedules into a signal band clear of startup (larger degrees, keeping
   operands sub-word), or hoist more of the per-call fixed cost out of the
   timed body.

5. **`runRefineTo` inconclusive — Newton-doubling precision quantisation.**
   Speculative Newton doubles precision per jump, so `refineTo?` reaches a
   *discrete* precision ladder and the per-call work is a step function of the
   target `t` (`t=96` and `t=128` do equal work; likewise `t=192`, `t=256`),
   not smooth in `t`. `t²` cannot fit a staircase. Resolution: parametrise the
   benchmark by the *number of Newton jumps* (monotone in work) rather than the
   raw target precision.

6. **SPEC time budget: degree 50 @ prec 64 FAILS.** SPEC target `< 10 s`.
   Measured with `isolateAll? (seededPoly 50) 64` (used because
   `separationDepth(deg 50) ≫ 64`, per the SPEC note): single call
   **495.85 s** (`chk = 4218`, 50 atoms), **`49.6×` over budget**. Resolution:
   this is a rough-first-guess budget the implementation does not meet at `n⁵`
   scaling; either the absolute budget is re-appraised or the driver is
   optimised (Graeffe iteration, deferred in the SPEC, would cut the
   `ceilLog2(deg)` separation-depth factor).

7. **SPEC time budget: degree 100 @ prec 128 FAILS.** SPEC target `< 1 min`.
   Measured with `isolateAll? (seededPoly 100) 128`: the single call did **not
   complete within a 19-minute window** (`> 1143 s`, already `> 19×` the budget,
   then stopped; extrapolating the `n⁵·B²` model from the degree-50 point puts
   the true time in the hours). Same resolution as Concern 6.

For reference, the one budget that is met: **degree 10 @ prec 32** runs in
`0.137 s` (`isolateAll? (seededPoly 10) 32`, compiled, calibrated against the
`runIsolateAll` `n=10` bench row of `138 ms`), comfortably under the `< 1 s`
target.

The two obsolete time-budget items were reality-anchored by #8762 and
subsequently tightened by the Graeffe/soft-Pellet ratchet recorded at the top
of this report. The transition-band and family/schedule items are resolved by
the ordered-mode experiment and enforced ceilings above.

## Phase 5--7 re-attestation

The ordered-mode registration changes do not alter the public API, proof
surface, conformance fixtures, or manual chapter. The preserved later-phase
evidence was rechecked with a sorry-free scan of `HexRoots` and
`HexRootsMathlib`, a successful
`lake build HexRoots HexRootsMathlib HexRealRoots HexRoots.Conformance HexManual.Chapters.HexRoots`,
and the Phase-7,
release-manifest, manual-split, published-trust-surface, Mathlib-free-bench,
file-line-count, copyright, and DAG guards. The benchmark `verify` command and
the explicit three-strategy comparison also pass. HexRoots is therefore
re-attested through Phase 7 rather than stopping at the repaired Phase 4.

## Concerns

None.
