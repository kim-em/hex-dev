# Cross-system Berlekamp–Zassenhaus factorization sweep

This report documents the re-runnable cross-system factorization benchmark suite
(issue #8545): a publication-quality comparison of hex against FLINT, NTL,
PARI/GP, and two verified Isabelle/AFP factorizers over a multi-family
polynomial corpus, with durable records and cumulative-time ("cactus") charts.

The suite is **explicitly not CI**. No workflow under `.github/workflows/` runs
it; sweeps run manually on dedicated hardware (carica) and their records are
committed. See the
[SPEC/benchmarking.md § Cross-system comparator sweeps](../SPEC/benchmarking.md)
addendum for how this sits beside the one-harness rule: the sweep is a
comparator, not a parallel harness for hex-internal claims.

> **Changing a hex factor path?** Re-measure the hex entries and refresh these
> charts, then show them to the requester — the external comparators do not need
> re-running (the plotter merges records newest-per-system). The exact commands
> and when a full re-measure is required are in
> [`HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md` § Cross-system sweep
> charts](../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md) and under
> [Reproducing](#reproducing) below.

## Systems

Every measured system runs as a warm persistent process speaking one line
protocol — request `{"coeffs":[...]}` (integer coefficients, ascending degree),
reply `{"ok":true,"result":{"scalar":s,"factors":[{"coeffs":[...],
"multiplicity":m},...]}}`, a decline reply `{"ok":true,"result":null}`, or an
error `{"ok":false,"error":...}`. A decline is counted as unsolved, deliberately
not distinguished from a timeout.

| curve | system | reconstruction | driver |
| --- | --- | --- | --- |
| `hex-factor` | hex | production cost-based hybrid | `hexbz_factor_service --entry factor` |
| `hex-lattice` | hex | van Hoeij CLD knapsack (lattice tier) | `--entry factorLattice` |
| `hex-fast` | hex | proof-facing fast path | `--entry factorFast` |
| `hex-classical-nodecline` | hex | classical recombination to completion/cutoff | `--entry factorClassicalNoDecline` |
| `flint` | FLINT | `fmpz_poly.factor` | `bz_flint_service.py` |
| `ntl` | NTL | `ZZXFactoring` | `bz_ntl_service.cc` |
| `pari` | PARI/GP | `factor` | `bz_pari_service.py` |
| `isabelle-bz` | verified Isabelle | exponential subset recombination | AFP `Berlekamp_Zassenhaus`, `setup_bz_isabelle.sh` |
| `isabelle-lll` | verified Isabelle | polynomial-time direct-LLL | AFP `LLL_Factorization`, `setup_bz_lll_isabelle.sh` |

**Why two verified Isabelle systems.** hex, Isabelle's `Berlekamp_Zassenhaus`,
and Isabelle's `LLL_Factorization` share the same modular front end (Berlekamp
mod p + Hensel lift) and differ only in reconstruction: BZ does exponential
subset recombination; `LLL_Factorization` finds each factor as a short lattice
vector in polynomial time; hex is the van Hoeij CLD knapsack recombination, also
polynomial but over a small lattice (dimension = number of modular factors).
Comparing only against exponential BZ makes "hex beats verified Isabelle" a soft
claim (polynomial beats exponential); adding the verified polynomial-time
`LLL_Factorization` turns it into a verified-poly-vs-verified-poly comparison
isolating the knapsack advantage over direct-LLL.

**The `factorClassicalNoDecline` curve.** Production `factor` declines a
hopeless classical recombination early and routes to the lattice tier. The
`factorClassicalNoDecline` entry (library additions `scaledRecombinationFull` /
`classicalCoreFactorsToCompletion` / `factorClassicalNoDecline`, reusing the
proven recombination loops with the #8530 level-aware tightening removed) instead
runs the full subset enumeration to completion or the wall-clock cutoff. Its
answers are correct where it terminates; where it does not, it times out. This
makes the classical exponential wall visible on the same charts. Production
`factor` and the CI-gated Mathlib proofs are untouched.

### isabelle-lll build spike — passed

The build spike (issue #8545) is confirmed on carica: the AFP `LLL_Factorization`
session builds and code-exports to Haskell, the export theory
`scripts/oracle/bz-lll-isabelle/Hex_LLL_Factor_Export.thy` compiles, and the
built `lll_isabelle` driver agrees with hex, FLINT, NTL and `isabelle-bz` on
every cross-checked instance. The AFP bundles the verified direct-LLL
reconstruction as `one_lattice_LLL_factorization :: int_poly_factorization_algorithm`
(a `typedef` pairing the algorithm with its soundness proof), and
`factorize_int_poly_generic` takes that bundle; the correct composition is
`factorize_int_poly_generic one_lattice_LLL_factorization`, mirroring BZ's
`factorize_int_poly_generic berlekamp_zassenhaus_factorization_algorithm`. Both
Isabelle drivers contribute curves to the recorded sweep below.

## Methodology

- **Corpus.** `bench/corpus/hexbz-factor-corpus.jsonl`, generated deterministically
  by `scripts/bench/gen_factor_corpus.py` (regenerates byte-identically). 205
  instances across 10 families (cyclotomic, cyclotomic-products, swinnerton-dyer,
  sd-products, chebyshev, legendre, laguerre, wilkinson, random-products,
  hoeij-zimmermann), degrees 3–1030. Each record carries `expectedFactorDegrees`
  where known and a deterministic `combined` flag (mix doctrine).
- **Per-call overhead.** Each system is timed on a trivial input (`x - 1`) over
  21 calls; the median is recorded in the sweep `config` block, per the
  [external-comparator overhead clause](../SPEC/benchmarking.md).
- **Repeats policy.** Median-of-5 when the first real call is under 1 s, single
  call otherwise. Timings are `perf_counter_ns` wall-clock.
- **Cutoff.** Default 10 s per call, parameterized (`--cutoff`) so 60 s / 300 s
  sweeps can be recorded later; each record carries its cutoff so sweeps at
  different cutoffs coexist. On timeout the process is killed, the abandonment
  recorded as `timeout`, and the process respawned.
- **Statuses.** `ok | declined | timeout | error` — failures are always recorded,
  never dropped.
- **Differential correctness.** Per instance, the factor degree multiset is
  cross-checked against `expectedFactorDegrees` where present and pairwise across
  every system that answered; a mismatch fails the sweep. The sweep therefore
  doubles as a differential-correctness test of hex against the other
  implementations.
- **Mix doctrine.** The `combined` flag caps every family at an equal count
  (spread across its degree range) so the combined cactus plot is a balanced
  mixture rather than dominated by the largest family. Per-family plots use all
  instances.

## Charts

Per system, the cactus plot sorts its solved instances by median runtime and
plots cumulative time (log y) against the number of instances solved (x); a curve
ends at that system's solved count. One SVG per family plus the combined mixture,
regenerated deterministically by `scripts/plots/hexbz-cactus.py` from the
committed sweep JSON.

![Combined-mixture cactus plot](figures/hexbz-cactus-combined.svg)

![Swinnerton-Dyer cactus plot](figures/hexbz-cactus-swinnerton-dyer.svg)

![Swinnerton-Dyer runtime vs degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)

![Cyclotomic cactus plot](figures/hexbz-cactus-cyclotomic.svg)

Per-family figures for the remaining families
(`hexbz-cactus-<family>.svg`, `hexbz-runtime-degree-<family>.svg`) are published
alongside these under `reports/figures/`.

## Recorded sweeps

### carica, 10 s cutoff (2026-07-03)

- **Artifact:** `reports/bench-results/hexbz-factor-sweep-cc203779-carica.json`
  SHA-256 `33a1d9b4ddfc0c4ebfc277a0926780bc81a9528c5bbd8d35e003c8a303d5624d`
- **Command:**
  `python3 scripts/bench/factor_sweep.py --systems hex-factor,hex-lattice,hex-fast,hex-classical-nodecline,flint,ntl,isabelle-bz,isabelle-lll --cutoff 10 --skip-unavailable`
- **Corpus:** `bench/corpus/hexbz-factor-corpus.jsonl`
  SHA-256 `02155334449b001b6cf86a3859e7f4fae5a812a2c6810935bebb73163d76e830` (205 instances)
- **Env:** host carica, commit `cc203779` (clean), toolchain
  `leanprover/lean4:v4.32.0-rc1`, arm64, 24 cores, 2026-07-03T03:56:45Z; AFP
  release `afp-2026-05-29` for both Isabelle systems.
- **Cross-check:** all eight answering systems agree — hex's factor degree
  multisets match FLINT, NTL, verified Isabelle BZ and verified Isabelle LLL on
  every instance any two solved (differential correctness across 205 instances,
  five independent implementations).

| system | ok | timeout | declined | overhead (µs) |
| --- | ---: | ---: | ---: | ---: |
| hex-factor | 180 | 25 | 0 | 41.0 |
| hex-lattice | 177 | 28 | 0 | 47.2 |
| hex-fast | 116 | 72 | 17 | 46.7 |
| hex-classical-nodecline | 180 | 25 | 0 | 40.7 |
| flint | 204 | 1 | 0 | 27.0 |
| ntl | 204 | 1 | 0 | 12.5 |
| pari&nbsp;† | 204 | 1 | 0 | 29.5 |
| isabelle-bz | 184 | 21 | 0 | 18.0 |
| isabelle-lll | 142 | 63 | 0 | 16.8 |

† PARI/GP is measured in the companion record below (same corpus SHA and
10 s cutoff); the plotter merges it into every chart newest-per-system,
so its row sits in this table while its curve is added to every plot.

The C-implementation ceiling (FLINT, NTL, PARI) solves 204/205, missing
only `hoeij_S9` (Swinnerton-Dyer SD₉, degree 512) at the 10 s cutoff.

**The verified-vs-verified headline is the point of the two Isabelle curves.**
On the corpus as a whole the counts are close (hex-factor 180, isabelle-bz 184,
hex-lattice 177, isabelle-lll 142), because the mixture is dominated by easy
low-degree instances where exponential recombination is cheap. The interesting
signal is where the reconstruction actually matters — the lattice-stress
families, by maximum degree solved:

| family | hex-lattice | isabelle-bz | isabelle-lll | flint | pari |
| --- | ---: | ---: | ---: | ---: | ---: |
| swinnerton-dyer | **64** | 32 | 16 | 128 | 128 |
| sd-products | **56** | 42 | 16 | 128 | 128 |

On Swinnerton-Dyer, hex's van Hoeij CLD lattice tier reaches degree 64 —
double the reach of verified exponential BZ (32) and four times that of verified
direct-LLL (16). `isabelle-lll` (the full-degree direct-LLL lattice) is the
slowest verified system on every hard family and across the corpus (142/205,
63 timeouts), matching the literature: a full-degree lattice with large entries
is notoriously slow in practice. hex's small knapsack lattice (dimension = number
of modular factors) is the advantage this comparison isolates. On irreducible
cyclotomics the picture inverts — exponential `isabelle-bz` confirms
irreducibility fastest among the verified systems (reaching degree 1030) — an
honest, family-dependent result.

The `hex-classical-nodecline` curve runs the classical recombination to
completion or cutoff with the level-aware early decline disabled, so its 25
timeouts are the classical exponential wall made visible on the same charts (it
never declines — 0 declined — it either completes correctly or times out).
`hex-fast` (the proof-facing path) is the weakest hex tier here. PARI/GP now has
a curve on every chart (companion record below): it sits with FLINT and NTL at
the C-implementation ceiling — 204/205 overall, reaching Swinnerton-Dyer and
sd-products degree 128 (double hex-lattice's 64, and far past both verified
Isabelle systems), and solving 9/10 of the hoeij-zimmermann literature set.
Longer-cutoff (60 s / 300 s) sweeps record alongside this one, each carrying its
own cutoff; the sole instance no system solves at 10 s is `hoeij_S9` (degree 512),
and the hardest hoeij-zimmermann entries fall only to the three C libraries
(FLINT, NTL, PARI) — the natural target for those longer sweeps.

### carica, 10 s cutoff — PARI/GP addition (2026-07-03)

- **Artifact:** `reports/bench-results/hexbz-factor-sweep-07b6363e-carica.json`
  SHA-256 `b56a7748d0816432d6e15c5c47d1ae252ddfcbebce2893f7672d73ab06b9eb20`
- **Command:**
  `python3 scripts/bench/factor_sweep.py --systems pari --cutoff 10 --skip-unavailable`
- **Corpus:** `bench/corpus/hexbz-factor-corpus.jsonl`
  SHA-256 `02155334449b001b6cf86a3859e7f4fae5a812a2c6810935bebb73163d76e830` (205 instances) —
  identical to the baseline, so the two records merge cleanly.
- **Version:** PARI/GP 2.17.3 (via `cypari2` 2.2.4).
- **Env:** host carica, commit `07b6363e` (clean), arm64, 24 cores,
  2026-07-03T06:31:46Z.
- **Result:** 204/205 solved, one timeout (`hoeij_S9`, degree 512, ~15 s),
  29.5 µs per-call overhead. PARI's factor-degree multisets match
  `expectedFactorDegrees` on every solved labelled instance (record cross-check
  green), and its factor counts agree with hex, FLINT, NTL and both verified
  Isabelle systems on all 1387 co-solved (system, instance) pairs carried in the
  baseline — the differential-correctness cross-check holds with PARI added.

**Only PARI was re-run.** The plotter takes the newest measurement of each
system, guarded by a matching corpus SHA, so this record contributes PARI's
curve to every chart while the other eight systems' curves carry over unchanged
from the baseline record above. The expensive external comparators (FLINT, NTL,
and especially the two Isabelle systems, whose setup rebuilds AFP session heaps)
were **not** re-run — adding one comparator never requires re-measuring the
others. See [Reproducing](#reproducing).

## Reproducing

> **Run only the systems that changed — never the whole board.** The plotter
> merges records **newest-per-system** (guarded by a matching corpus SHA), so
> every chart is assembled from whichever record measured each system most
> recently. To add a new comparator or refresh one that changed, run
> `--systems <that-one>` and commit the small record next to the baseline; its
> curve slots into every chart and the other systems carry over untouched. Do
> **not** re-run the expensive external comparators to "add" one — re-running
> FLINT/NTL/PARI wastes an afternoon and the two Isabelle setups rebuild AFP
> session heaps (many minutes each) for no benefit. Full-board runs are for the
> first-ever record on a host or a corpus change, not for incremental additions.

```
# Regenerate the corpus (byte-identical) and confirm:
python3 scripts/bench/gen_factor_corpus.py
python3 scripts/bench/gen_factor_corpus.py --check

# First-ever record on a host (or after a corpus change): run every available
# system at the 10 s cutoff. This is the ONLY time you run the whole board.
python3 scripts/bench/factor_sweep.py --cutoff 10 --skip-unavailable

# Regenerate the charts (default: merge every committed record, newest-per-system):
python3 scripts/plots/hexbz-cactus.py
```

### Adding or refreshing one system — the common case

Each sweep writes a permanent, timestamped record naming every system and its
version. Because the merge is newest-per-system, adding a comparator (e.g.
bringing PARI onto the charts once `cypari2` is installed) or re-measuring the
hex entries after a factor-path change is a **single-system** run against the
same corpus at the same cutoff — the other curves come from the committed
baseline automatically:

```
# Add one external comparator (PARI/GP shown; same shape for any single system):
python3 scripts/bench/factor_sweep.py --systems pari --cutoff 10 --skip-unavailable

# Re-measure just the hex entries as they evolve:
python3 scripts/bench/factor_sweep.py \
    --systems hex-factor,hex-lattice,hex-fast,hex-classical-nodecline \
    --cutoff 10 --skip-unavailable

# Regenerate charts: the fresh record wins for the systems it measured, and every
# other curve carries over from the committed baseline it was last measured in
# (newest measurement per system, guarded by a matching corpus SHA):
python3 scripts/plots/hexbz-cactus.py
```

A single-system record still cross-checks that system's factor-degree multisets
against `expectedFactorDegrees` (present on 198/205 instances), which is the same
oracle every other system was validated against — so a green single-system run is
the differential-correctness check for the system you added, without re-running
the rest. The plotter prints a per-system provenance line (record timestamp and
cutoff) so a mixed-time chart is honest about which curves are fresh; merging
records over different corpora is refused. Keep the cutoff identical across the
records you merge, or the solved-counts are not comparable (the subtitle flags a
mixed cutoff). Commit the fresh record alongside the baseline; both coexist under
`reports/bench-results/`.
