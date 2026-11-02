# Finite-field F4 medium comparison with current msolve

Hex source `dd2370a9e993` remains slower than msolve on this fixed
medium development suite. Its family-balanced whole-process ratio is 1.9147
against exact mode 2 and 2.1551 against probabilistic mode 42. These observations
do not satisfy the SPEC's fastest-open-source milestone or establish a compiler
or runtime impossibility.

The suite is the same 14 grevlex systems described in
[the medium development corpus](hexgroebner-medium.md): cyclic7, Katsura8, Eco11,
Noon5, Reimer6, MinRank and dense quadratic6, each over primes 32003 and
2147483647. Inputs and provenance are archived. This is a development suite,
with no held-out or acceptance claim. Results from other source snapshots and
comparator builds are separate observations and are not pooled here.

The Hex driver is freshly built from snapshot `4f744b62fbfb25087abd963ef6cfd19bc30daef7`,
parent `67c70e5e4c7c83c3649789c12a4bdae135e5f823`, with only pinned dependency packages shared. Lean is
4.35.0-rc3. SHA-256 identifies the measured executable as
`c585b436028c7fe3bb3627d0c024b3e0f782e67bacc3895301f630c927dab803`. Its complete source manifest, source blobs,
initialization checks and build log are retained. Candidate production includes
canonical packing, F4 and final interreduction; certificate generation,
independent final certification and kernel checking are excluded. The matrix
continuation remains unselected in this engine.

The current upstream msolve checkout is clean at
`3672113ee2c696a2ac9c637636e0f7214f500ba1`. The build uses Clang 23.1.3, `-O3 -march=native`
with `NIX_ENFORCE_NO_NATIVE=0`; the recorded driver resolves to `znver5`.
The engine's ELF records the native compiler command. GMP 6.3.0, MPFR 4.2.2
and FLINT 3.6.0 linkage, full configure/build settings, failed setup diagnostics
and public source are retained. The direct `.libs/msolve` ELF is measured with
its recorded neogb library path. No libtool launcher or stripped native flag is
used. OpenMP configuration and thread settings are retained; both arms request
one algorithm thread. Mode 42's random seeds and diagnostics are retained,
without a deterministic-elimination guarantee.

Each mode has one first campaign, adjacent AB then BA per input, on the shared
host `chungus2`. Automatically leased logical CPUs are 63 for mode 2 and 12 for
mode 42. Placement does not establish isolation. Identical GNU-time wrappers
include startup, parsing and complete monic reduced-basis output in process
wall time and collect post-exec peak RSS. The per-process limits are 60 seconds,
16 GiB address space and 64 MiB output. Every completed sample is retained;
there is no unchanged repeat or host-activity filtering.

Both modes complete all 14 inputs in both blocks. Each has 56 successful
processes, 28 complete-basis comparisons, zero failures and zero timeouts.
All complete reduced bases agree. Hex's internal candidate time is retained
but is not compared with msolve process time. Counter definitions differ
between engines and are not treated as equal measures of algebraic work.

| Hex/msolve process ratio | Equal-family mean | Median | Range | Peak RSS Hex/msolve KiB |
| --- | ---: | ---: | --- | ---: |
| Exact mode 2 | 1.9147 | 1.9807 | 0.7746–3.1473 | 126344/20212 |
| Probabilistic mode 42 | 2.1551 | 2.1700 | 0.7675–4.9191 | 126344/20212 |

The mean first combines paired ratios within each family geometrically, then
weights the seven families equally. Every family mean is above one. Individual
wins and the full ratio range remain visible in the raw records.

| Family | Exact mode 2 | Probabilistic mode 42 |
| --- | ---: | ---: |
| cyclic | 3.0476 | 3.6810 |
| kat | 2.2970 | 2.5361 |
| eco | 1.9192 | 3.0343 |
| noon | 1.8922 | 1.8570 |
| reimer | 2.4137 | 2.6712 |
| minrank | 1.0286 | 1.0155 |
| dense-quadratic | 1.4949 | 1.5134 |

The remaining acceptance work includes current matched comparisons with the
other open-source contenders, held-out and hard families, additional field
widths and finite extensions, parallel sweeps, solved coverage, family-balanced
and per-family acceptance, and separate certification/native-verification/kernel
checking costs. The timing data identify a remaining gap; they do not attribute
it to a specific algorithm, representation, generated-code or runtime cost.

The [complete archive](raw/f4-msolve-dd2370a9e993.tar.gz) has SHA-256
`64eee38080a797688d93bff7bd322e6a5caaadf6da7b163be89607e3c9a6631b` and 644 payloads. It includes a per-payload digest
manifest, both complete campaigns and analysis, frozen Hex source blobs,
msolve source and build identity, inputs, full outputs, failures, memory and
host-load context. All archived payloads were read back and checked.
