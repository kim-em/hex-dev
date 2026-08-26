# HexBerlekampZassenhausMathlib Performance Report

## Bench Targets

`HexBerlekampZassenhausMathlib` owns an executable elaboration runtime (the `factor_poly` / `irreducibility` elaborators and their `factor_poly!` / `irreducibility!` kernel-decide fallbacks) but no separable compiled computation: the integer-polynomial factorization arithmetic those elaborators run as untrusted search belongs to the Mathlib-free `HexBerlekampZassenhaus` library and is measured by its `hexbz_bench` executable. Every operation this library advertises is therefore on the proof track. These build-only fresh-module probes replace a compiled complexity registration for `factor_poly`/`irreducibility` elaboration, certificate emission, and ordinary kernel checking of the emitted terms.
Accordingly, this surface has no LeanBench registration, executable,
`list`/`verify` entry, complexity verdict, or timed-region sampling profile.

| probe | reference | candidate | case |
|---|---|---|---|
| `fresh-build-null` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | baseline, calibration-only |
| `kernel-8-null` | `HexBerlekampZassenhausMathlib.ProofProbe.Kernel8` | `HexBerlekampZassenhausMathlib.ProofProbe.Kernel8` | kernel-8, calibration-only |
| `factor-4` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Factor4` | factor-distinct, degree 4, 2 factors |
| `factor-8` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Factor8` | factor-distinct, degree 8, 4 factors |
| `factor-12` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Factor12` | factor-distinct, degree 12, 6 factors |
| `irreducible-4` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible4` | irreducibility, degree 4 |
| `irreducible-8` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible8` | irreducibility, degree 8 |
| `irreducible-16` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible16` | irreducibility, degree 16 |
| `kernel-4` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Kernel4` | kernel-fallback, degree 4 |
| `kernel-8` | `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | `HexBerlekampZassenhausMathlib.ProofProbe.Kernel8` | kernel-fallback, degree 8 |
| `multiplicity-8` | `HexBerlekampZassenhausMathlib.ProofProbe.Factor8` | `HexBerlekampZassenhausMathlib.ProofProbe.Repeated8` | multiplicity-attribution, degree 8, 4 factors |

All `factor_poly` inputs are products of distinct irreducible quadratics `X² + c` over `ℤ` except `multiplicity-8`'s candidate, `(X² + 2)⁴` (same degree and factor count with multiplicity as `factor-8`'s candidate, all multiplicity). The `irreducibility` inputs are the Eisenstein binomials `Xᵈ − 2`. The `kernel-fallback` inputs are the Swinnerton-Dyer minimal polynomials of `√2 + √3` (degree 4) and `√2 + √3 + √5` (degree 8): balanced modulo every prime, not Eisenstein at any small shift, and outside the multi-prime degree-sum obstruction language, so `irreducibility!` on them genuinely replays the compiled factorizer inside the kernel rather than replaying a certificate.

Every probe carries the same import block, including the `import all` executable closure the emitted certificate checks and the kernel replays need, so the paired delta isolates elaboration, proof emission, and kernel checking. That shared closure costs ~6.65 s in every arm, which is why the expensive null control is `Kernel8` rather than a cheaper module: the harness requires its two same-module controls to differ in build magnitude by at least `2.0x`, and only the degree-8 kernel replay clears that (`2.4537x` measured below, against `1.37x` for the degree-16 binomial). It is also the costliest substantive arm, so every substantive envelope is interpolated between the controls rather than extrapolated past them.

`HexBerlekampZassenhausMathlibProofProbe` supplies reduced CI coverage (`Baseline`, `Factor4`, `Irreducible4`, built by the ordinary single CI job); `HexBerlekampZassenhausMathlibProofProbeScientific` owns the larger release arms (`Factor8`, `Factor12`, `Repeated8`, `Irreducible8`, `Irreducible16`, `Kernel4`, `Kernel8`) and stays outside routine CI.

## Verdicts

Scientific fresh-module run at commit `a9f5a5088af2b5cc6bf005ce383cea0648788408` on designated host `chungus2`, logical CPU `1` (physical core `1`, SMT sibling CPU `49`).

Exact command invoked:

```sh
taskset -c 1 python3 scripts/bench/bz_mathlib_sweep.py --samples 6 \
  --timeout 300 --warm-timeout 900 \
  --shared-host --expected-host chungus2 --cpu 1 \
  --max-core-interference-ratio 0.005 \
  --max-pair-retries 32 \
  --preflight-timeout-seconds 1800 \
  --output bz-mathlib-release-cpu1.json
```

The artifact below is the byte-for-byte committed copy of that output.

| field | artifact value |
|---|---|
| artifact | `reports/bench-results/hex-berlekamp-zassenhaus-mathlib-a9f5a508-chungus2.json` |
| artifact SHA-256 | `818b81a4a2a8796248c1d6e8d91ba6ec53650743640032f595460addc7dee8e7` |
| embedded source-hash map | `source_sha256` in the cited artifact |
| schema | `hex-berlekamp-zassenhaus-mathlib-proof-probe-v1` |
| measurement | `paired-fresh-module-olean-wall-robust-null-v2` |
| measurement state | `complete` |
| release quality | `True` |
| host protocol | `designated-shared-host-v3` |
| accepted paired samples | 66 |
| rejected pair attempts | 122 |
| rejected preflight windows | 126 |
| preflight failures | 0 |
| exhausted pairs | 0 |
| maximum admitted aggregate core-interference ratio | 0.004743010381276924 |
| maximum core-interference allowance | 0.08391322905 s |
| maximum attempts spent on any one pair | 32 |
| maximum preflight wait | 18.011156780028716 s |

The preregistered `--max-core-interference-ratio 0.005` governs each arm's
allowance as `max(quantization, ratio x wall)`. These arms run 6.61 s to
16.32 s, so `ratio x wall` (0.033 s to 0.084 s) exceeds the three-tick
accounting quantization floor (0.030 s) throughout, and the ratio rather
than the floor is the binding admission gate. The maximum aggregate
interference actually admitted into any arm is `0.004743010381276924`,
inside that bound.

The suite preregisters `max_pair_retries=32` rather than the default eight,
which `SPEC/benchmarking.md` permits for a suite with preregistered long
arms and which "changes only how many clean-pair opportunities are
attempted, never the admission threshold". These arms are roughly `3x` the
sibling `HexBerlekampMathlib` suite's, so each is proportionally longer
exposed to a stray scheduler tick and is rejected more often on a busy
shared host: this run spent 122 rejected pair attempts and 126 rejected
preflight windows to obtain its 66 clean pairs, and one pair needed the full
32-retry budget. Every rejected attempt and window is retained in the cited
artifact. The alternative of raising the interference ratio was considered
and rejected: it would have admitted dirtier arms rather than buying more
chances at a clean one.

Every sample cell is `reference / candidate / signed candidate-reference`; wall times are exact nanosecond values rendered as seconds. `R->C` and `C->R` record build orientation, and `aN` records the admitted complete-pair attempt.

Null controls are descriptive only: their medians are not subtracted, their ranges do not widen a budget, and they are neither significance tests nor scientific evidence. Under the `robust-null-v2` contract each robust null envelope is floored by the maximum observed absolute null delta, and substantive envelopes are interpolated between the two controls by build magnitude.

### Null-control raw samples

| control | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `fresh-build-null` | a1, R→C; 6.630576569 s / 6.633931002 s / +0.003354433 s | a2, C→R; 6.620948520 s / 6.604151735 s / -0.016796785 s | a1, R→C; 6.681613842 s / 6.654509386 s / -0.027104456 s | a2, C→R; 6.642415161 s / 6.649177027 s / +0.006761866 s | a14, R→C; 6.682048267 s / 6.650276120 s / -0.031772147 s | a1, C→R; 6.663095671 s / 6.645123415 s / -0.017972256 s |
| `kernel-8-null` | a1, R→C; 16.289687363 s / 16.209587793 s / -0.080099570 s | a1, C→R; 16.427479507 s / 16.238308358 s / -0.189171149 s | a4, R→C; 16.357409370 s / 16.782645810 s / +0.425236440 s | a1, C→R; 16.064450625 s / 16.168142485 s / +0.103691860 s | a2, R→C; 16.395037358 s / 16.247880893 s / -0.147156465 s | a5, C→R; 16.182629751 s / 16.307390853 s / +0.124761102 s |

### Null-control ranges and medians

| control | signed range | absolute span | per-sample Δ/reference relative range | median relative delta | median signed delta | zero-centred robust envelope | build magnitude |
|---|---|---|---|---|---|---|---|
| `fresh-build-null` | -0.031772147 s … +0.006761866 s | 0.038534013 s | -0.475485% … +0.101798%; span 0.577283% | -0.261710% | -0.017384520 s | 0.059528458 s | 6.652755416 s |
| `kernel-8-null` | -0.189171149 s … +0.425236440 s | 0.614407589 s | -1.151553% … +2.599656%; span 3.751209% | +0.076877% | +0.011796145 s | 0.505221291 s | 16.323548366 s |

### Substantive raw samples

| proof pair | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `factor-4` | a1, R→C; 6.699260298 s / 6.713785444 s / +0.014525146 s | a2, C→R; 6.774415334 s / 6.985880620 s / +0.211465286 s | a1, R→C; 6.624785911 s / 6.711530135 s / +0.086744224 s | a3, C→R; 6.682753273 s / 6.729909530 s / +0.047156257 s | a4, R→C; 6.642945933 s / 6.724689933 s / +0.081744000 s | a2, C→R; 6.699315590 s / 6.764913682 s / +0.065598092 s |
| `factor-8` | a1, R→C; 6.655137395 s / 6.850361621 s / +0.195224226 s | a2, C→R; 6.710169046 s / 6.891626630 s / +0.181457584 s | a1, R→C; 6.604160463 s / 6.906948086 s / +0.302787623 s | a3, C→R; 6.585870993 s / 6.898021078 s / +0.312150085 s | a1, R→C; 6.638389377 s / 6.960214159 s / +0.321824782 s | a4, C→R; 6.638260827 s / 6.883726769 s / +0.245465942 s |
| `factor-12` | a1, R→C; 6.614712345 s / 6.996292720 s / +0.381580375 s | a1, C→R; 6.774214546 s / 7.077085126 s / +0.302870580 s | a1, R→C; 6.620243502 s / 6.974681304 s / +0.354437802 s | a5, C→R; 6.714463438 s / 7.064034767 s / +0.349571329 s | a2, R→C; 6.624625940 s / 7.008992560 s / +0.384366620 s | a3, C→R; 6.681797279 s / 7.075838633 s / +0.394041354 s |
| `irreducible-4` | a8, R→C; 6.668898408 s / 6.895941300 s / +0.227042892 s | a9, C→R; 6.596406442 s / 6.868679848 s / +0.272273406 s | a3, R→C; 6.693272718 s / 6.878555993 s / +0.185283275 s | a1, C→R; 6.598866066 s / 6.885070283 s / +0.286204217 s | a1, R→C; 6.594293537 s / 6.870527553 s / +0.276234016 s | a2, C→R; 6.627842220 s / 6.899402555 s / +0.271560335 s |
| `irreducible-8` | a1, R→C; 6.641779357 s / 7.128922677 s / +0.487143320 s | a1, C→R; 6.654130993 s / 7.199468818 s / +0.545337825 s | a2, R→C; 6.733870507 s / 7.237495705 s / +0.503625198 s | a1, C→R; 6.605750914 s / 7.196773137 s / +0.591022223 s | a1, R→C; 6.625091471 s / 7.172415515 s / +0.547324044 s | a8, C→R; 6.733342574 s / 7.136694203 s / +0.403351629 s |
| `irreducible-16` | a5, R→C; 6.623546776 s / 8.942109454 s / +2.318562678 s | a1, C→R; 6.630779316 s / 9.005239225 s / +2.374459909 s | a1, R→C; 6.789939763 s / 9.168037514 s / +2.378097751 s | a1, C→R; 6.652318120 s / 8.972364879 s / +2.320046759 s | a4, R→C; 6.730519588 s / 9.095046182 s / +2.364526594 s | a1, C→R; 6.604683344 s / 9.001967709 s / +2.397284365 s |
| `kernel-4` | a2, R→C; 6.580258150 s / 7.758223631 s / +1.177965481 s | a1, C→R; 6.615228222 s / 7.619461416 s / +1.004233194 s | a2, R→C; 6.701421926 s / 7.667776779 s / +0.966354853 s | a1, C→R; 6.681446238 s / 7.601349703 s / +0.919903465 s | a1, R→C; 6.746391471 s / 7.765102388 s / +1.018710917 s | a1, C→R; 6.594916372 s / 7.644456511 s / +1.049540139 s |
| `kernel-8` | a1, R→C; 6.671588222 s / 16.174366334 s / +9.502778112 s | a1, C→R; 6.647887621 s / 16.177352223 s / +9.529464602 s | a6, R→C; 6.609382671 s / 16.156503985 s / +9.547121314 s | a1, C→R; 6.691513045 s / 16.379976674 s / +9.688463629 s | a2, R→C; 6.697130224 s / 16.362396959 s / +9.665266735 s | a1, C→R; 6.552624825 s / 16.143714730 s / +9.591089905 s |
| `multiplicity-8` | a32, R→C; 6.876686722 s / 6.754052244 s / -0.122634478 s | a1, C→R; 6.926647731 s / 6.732485433 s / -0.194162298 s | a3, R→C; 6.856619727 s / 6.810861473 s / -0.045758254 s | a3, C→R; 6.914900377 s / 6.764524569 s / -0.150375808 s | a4, R→C; 6.907006223 s / 6.750628947 s / -0.156377276 s | a1, C→R; 6.953538497 s / 6.764718875 s / -0.188819622 s |

### Substantive summaries

| proof pair | median reference | median candidate | median signed delta | control | magnitude ratio | raw control span | raw control envelope | scaled span | scaled envelope | resolution |
|---|---|---|---|---|---|---|---|---|---|---|
| `factor-4` | 6.691006785 s | 6.727299731 s | +0.073671046 s | fresh-build-null + kernel-8-null | 1.011205 | 0.024885852 s | 0.062963944 s | 0.024885852 s | 0.062963944 s | resolved |
| `factor-8` | 6.638325102 s | 6.894823854 s | +0.274126782 s | fresh-build-null + kernel-8-null | 1.036386 | 0.028813737 s | 0.070684541 s | 0.028813737 s | 0.070684541 s | resolved |
| `factor-12` | 6.653211609 s | 7.036513663 s | +0.368009088 s | fresh-build-null + kernel-8-null | 1.057684 | 0.032135893 s | 0.077214526 s | 0.032135893 s | 0.077214526 s | resolved |
| `irreducible-4` | 6.613354143 s | 6.881813138 s | +0.271916870 s | fresh-build-null + kernel-8-null | 1.034431 | 0.028508679 s | 0.070084923 s | 0.028508679 s | 0.070084923 s | resolved |
| `irreducible-8` | 6.647955175 s | 7.184594326 s | +0.524481511 s | fresh-build-null + kernel-8-null | 1.079943 | 0.035607893 s | 0.084039043 s | 0.035607893 s | 0.084039043 s | resolved |
| `irreducible-16` | 6.641548718 s | 9.003603467 s | +2.369493251 s | fresh-build-null + kernel-8-null | 1.353365 | 0.078257620 s | 0.167870777 s | 0.078257620 s | 0.167870777 s | resolved |
| `kernel-4` | 6.648337230 s | 7.656116645 s | +1.011472055 s | fresh-build-null + kernel-8-null | 1.150819 | 0.046663526 s | 0.105769849 s | 0.046663526 s | 0.105769849 s | resolved |
| `kernel-8` | 6.659737921 s | 16.175859278 s | +9.569105609 s | fresh-build-null + kernel-8-null | 1.009130 | 0.246423215 s | 0.498414821 s | 0.246423215 s | 0.498414821 s | resolved |
| `multiplicity-8` | 6.910953300 s | 6.759288406 s | -0.153376542 s | fresh-build-null + kernel-8-null | 1.038811 | 0.029191919 s | 0.071427891 s | 0.029191919 s | 0.071427891 s | resolved |

All nine substantive arms resolve against their interpolated robust-null
envelopes.

The `factor_poly` candidate medians are 6.727300 s, 6.894824 s, and
7.036514 s at degrees 4, 8, and 12 over the ~6.65 s import-only baseline:
elaboration deltas of +0.073671046 s, +0.274127 s, and +0.368009 s. The
point estimates increase with the distinct-quadratic count, though the
degree-4 to degree-8 step is larger than the degree-8 to degree-12 one, so
the three points do not by themselves fix a growth law. The
`irreducibility` deltas are +0.271917 s, +0.524482 s, and +2.369493 s at
degrees 4, 8, and 16.

The kernel-decide fallback is the most expensive surface by a wide margin:
`irreducibility!` on the Swinnerton-Dyer quartic costs +1.011472 s and on
the octic +9.569106 s. That ~9.5x step from degree 4 to degree 8 is the
measured price of the fallback, and it is what the `bangBudget = 13`
dense-size cap in `KernelFactorTactic.lean` exists to bound. The mechanism
is that the bang form makes the kernel re-run the whole compiled factorizer
instead of replaying a certificate; that reading comes from the tactic's
implementation, not from this measurement, which times each arm end to end
and has no matched search-versus-replay decomposition to attribute the cost
between phases.

The degree-8 multiplicity attribution is -0.153376542 s against a
0.071427891 s envelope: the fourth power of one quadratic elaborates faster
than four distinct quadratics of the same degree and factor count. That is
consistent with the emitted certificate carrying one irreducibility
sub-certificate with multiplicity four instead of four distinct ones, which
is the same sign and the same explanation the sibling `HexBerlekampMathlib`
suite records.

Every arm completed far below the 300 s timeout. These are raw proof-track
timings, never complexity verdicts. The reported timing is not corrected.
Only wholly clean adjacent pair attempts enter the tables; rejected attempts
and preflight windows remain in the cited artifact.

### Axiom validation and emitted artifact sizes

| module | expected axioms | observed axioms | ilean_bytes | olean_bytes | olean_private_bytes | olean_server_bytes | source_bytes |
|---|---|---|---|---|---|---|---|
| `HexBerlekampZassenhausMathlib.ProofProbe.Baseline` | null | null | 7072 | 18000 | 808 | 2200 | 7107 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Factor12` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8294 | 28664 | 54360 | 1632 | 7042 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Factor4` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8017 | 26120 | 32096 | 1632 | 6963 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Factor8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8149 | 27368 | 44608 | 1632 | 6996 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible16` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8396 | 25144 | 52488 | 1664 | 6992 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible4` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8385 | 25144 | 30640 | 1592 | 6975 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8385 | 25144 | 37832 | 1592 | 6973 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Kernel4` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8464 | 27344 | 28168 | 2080 | 7219 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Kernel8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8727 | 29120 | 40952 | 2024 | 7243 |
| `HexBerlekampZassenhausMathlib.ProofProbe.Repeated8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 8169 | 25456 | 31496 | 1888 | 7075 |

### Provenance and configuration

| environment field | artifact value |
|---|---|
| git commit | a9f5a5088af2b5cc6bf005ce383cea0648788408 |
| git dirty | False |
| toolchain | leanprover/lean4:v4.34.0-rc2 |
| hostname | chungus2 |
| platform | Linux-6.12.100-x86_64-with-glibc2.42 |
| machine ID | 8be29815875342aeaae06e62d60f6b03 |
| architecture | x86_64 |
| CPU model | AMD EPYC 9455 48-Core Processor |
| Python | 3.14.6 |
| GNU time | /run/current-system/sw/bin/time |

Repository checkout:
```json
{
  "dirty": false,
  "head": "a9f5a5088af2b5cc6bf005ce383cea0648788408",
  "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662",
  "state_sha256": "f39f5bdd7c7ab35866333ab6f181e821ca9cd36f8871fde530604a998a146cc6",
  "status": "",
  "tree": "c6882b09a038c3b10ea2705077c3c7a510c990bc"
}
```

Dependency checkouts:
```json
{
  "Cli": {
    "dirty": false,
    "head": "ab3a82db9fea14cf0fd7f5a2de650f4b534640af",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/Cli",
    "state_sha256": "65df434312cafbe625f7c255f523575c7ac14dd658fe7d755edcf376634406e2",
    "status": "",
    "tree": "9f7b5faae284be737c556b3b205043b293061fd2"
  },
  "LeanSearchClient": {
    "dirty": false,
    "head": "ba67e212be1197b84c1f1f6299488a10a3002713",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/LeanSearchClient",
    "state_sha256": "4554659b2b9ebedb58446b1c8d0c3b4439940cd9b4d92c081036ca51b3c4d1dc",
    "status": "",
    "tree": "89abb77cd7d9344beed0f5e041b444c5458674f7"
  },
  "MD4Lean": {
    "dirty": false,
    "head": "31907cc18f48a95384f99cee5582c00fb39e0f67",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/MD4Lean",
    "state_sha256": "371e7dd0e12c88d3bf727066e87ba96e0b3630c1b381e30f80bb86d2d3d98b01",
    "status": "",
    "tree": "968ae7de50111d78c47ecf0682e9de2dfd257f67"
  },
  "Qq": {
    "dirty": false,
    "head": "507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/Qq",
    "state_sha256": "a98d09e28230aad983f781592db94732afd1c3f6ee89665f5381a4a523c24cd7",
    "status": "",
    "tree": "22ba3c95e36bbc7d0aa9d55677ffebf0be90cccd"
  },
  "aesop": {
    "dirty": false,
    "head": "18889deb9e83ea7420ef51c160d6f88552e744e3",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/aesop",
    "state_sha256": "6f95bf2c6fe0e9d21f222f7894115224789824d945de6e03ebb05077c5c6035e",
    "status": "",
    "tree": "ef71b806106b107d2b259d9b50077d4786aefb66"
  },
  "batteries": {
    "dirty": false,
    "head": "d54dddc581e08be364c278052863524bff7a99a9",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/batteries",
    "state_sha256": "d147fd1a7a237e14711c7d53bbac46f83e1df7f386e6368dde5dfcd3274aa6b9",
    "status": "",
    "tree": "f7460b599b386df89d85bfdf1a7465cd44ff0861"
  },
  "illuminate": {
    "dirty": false,
    "head": "6e558472c981dbee8cb9fcde92fa9593daf04228",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/illuminate",
    "state_sha256": "a98eb6e62a445ff4d98e457669bdcf6fbd215cfb275333232cef9833329a925a",
    "status": "",
    "tree": "6fe64d8f2c0a64d7b7a3647f555f465fb636a55b"
  },
  "importGraph": {
    "dirty": false,
    "head": "d8823026ac7ef130c253089d95685f9877b95323",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/importGraph",
    "state_sha256": "24ea70ed738b9b9a3e6f6e4fb49174b541e5fe5f285b730163cd3cba093193b4",
    "status": "",
    "tree": "d5d88b13966b0a4d89a5d04e5cf9f8f5bf25dfeb"
  },
  "lean-bench": {
    "dirty": false,
    "head": "fa30c2763cf523f3ac8e46dc3a1dad0845a40098",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/lean-bench",
    "state_sha256": "689f9504c42512f18b20bb58391f1b3026e7a114591037ba1c2e4400db003ff9",
    "status": "",
    "tree": "5e2c6d004439e19a8fc005e136fea4beb9f28c5b"
  },
  "mathlib": {
    "dirty": false,
    "head": "85e3a25e006c35636f0e53b0e9296caca2685bc0",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/mathlib",
    "state_sha256": "40b120f09ff47e9ca7d54b6aca919463d61cb27f1ad58ee07362fe7b54bf3c23",
    "status": "",
    "tree": "955cb3928b885a10e8deb4e1f293f8f50d82664e"
  },
  "plausible": {
    "dirty": false,
    "head": "d9598f07b1bc701f1e3aae163d2681c1fd978793",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/plausible",
    "state_sha256": "9bd4c1e4cd877b3bdc974e50fc27789ab6a80107ae139a051d3f467037d4e16e",
    "status": "",
    "tree": "81f195d87b0f1efa7b9430b6d21034ed51bd2006"
  },
  "proofwidgets": {
    "dirty": false,
    "head": "a8acbfd87375ff4abe14ce09db5b7664d383bc7f",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/proofwidgets",
    "state_sha256": "cb5d130298c96a2f42742dc55b5ca802ee6703fb70147c39d23a10ffaecc8687",
    "status": "",
    "tree": "7c0d97efaaf9c6b9faeed6c863b8c4085cc989a2"
  },
  "subverso": {
    "dirty": false,
    "head": "847084e80500726e4331dded5f17007ddaf89c31",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/subverso",
    "state_sha256": "1ce57a39bc7eb6e755cb1a46f70ea6022bfdf80c5436ff2108efa77c6e9918e6",
    "status": "",
    "tree": "653a5d4a775e9b68056f0f8b9b253da8c65c286f"
  },
  "verso": {
    "dirty": false,
    "head": "90c688db9db7280364c8bd7f8264c82a01582fd4",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-issue-9662/.lake/packages/verso",
    "state_sha256": "a5dfe8c36b946d57874bafe6ebdd4477bf0415624f31e324f4f733587b76810d",
    "status": "",
    "tree": "a8e1171167bee808e429a0bf3492a96bd54c5c1a"
  }
}
```

The complete per-source SHA-256 map is retained under `source_sha256` in the cited artifact; the artifact file itself is anchored above by SHA-256 `818b81a4a2a8796248c1d6e8d91ba6ec53650743640032f595460addc7dee8e7`.

Recorded configuration:
```json
{
  "accounting_quantization_ticks": 3,
  "allow_busy": false,
  "allow_dirty": false,
  "command_template": "lake build +<module>:olean",
  "core_interference_accounting": "measurement-cpu-foreign-plus-all-SMT-sibling-busy",
  "cpu_affinity": [
    1
  ],
  "cpu_topology": {
    "core_id": "1",
    "logical_cpu": 1,
    "physical_package_id": "0",
    "scaling_cur_freq_khz": "4440670",
    "scaling_governor": "schedutil",
    "thread_siblings_list": "1,49"
  },
  "expected_host": "chungus2",
  "frequency_measurement": "cpufreq-time-in-state-arm-mean",
  "import_baseline_control": null,
  "lean_num_threads": "1",
  "max_core_interference_ratio": 0.005,
  "max_frequency_spread_ratio": 0.15,
  "max_load_per_cpu": 0.5,
  "max_null_robust_spread_ratio": 0.1,
  "max_pair_retries": 32,
  "measurement_cpu_foreign_accounting": "busy-minus-child-minus-runner-minus-irq-softirq",
  "minimum_control_magnitude_ratio": 2.0,
  "null_magnitude_factor": 3.0,
  "order": [
    "fresh-build-null",
    "kernel-8-null",
    "factor-4",
    "factor-8",
    "factor-12",
    "irreducible-4",
    "irreducible-8",
    "irreducible-16",
    "kernel-4",
    "kernel-8",
    "multiplicity-8"
  ],
  "pairing": "adjacent measured reference and candidate fresh modules; contamination retries the complete oriented pair",
  "preflight_max_busy_ticks": 2,
  "preflight_timeout_seconds": 1800.0,
  "preflight_window_seconds": 2.0,
  "requested_cpu": 1,
  "rotation": "pairs left by round index; pair orientation alternates",
  "samples": 6,
  "shared_host": true,
  "timeout_seconds": 300.0,
  "warm_command_template": "lake build +<module>:deps",
  "warm_timeout_seconds": 900.0
}
```

### Shared-host interference observations
```json
{
  "accounting_quantization_ticks": 3,
  "expected_frequency_observations": 132,
  "frequency_spread_ratio": 0.0,
  "max_aggregate_core_interference_ratio": 0.004743010381276924,
  "max_arm_mean_frequency_khz": 3150000.0,
  "max_attempts_per_pair": 32,
  "max_concurrent_lake_lean_count": 16,
  "max_core_interference_ratio": 0.005,
  "max_cpu_pressure_some_delta_us": 1730579,
  "max_effective_core_interference_ratio": 0.005000000000000001,
  "max_frequency_spread_ratio": 0.15,
  "max_interference_allowance_seconds": 0.08391322905000001,
  "max_load_1m_per_cpu": 0.0926971435546875,
  "max_measurement_cpu_foreign_ratio": 0.0028492462765177945,
  "max_measurement_cpu_interrupt_ratio": 0.006056308518763107,
  "max_preflight_wait_seconds": 18.010332511970773,
  "max_smt_sibling_busy_ratio": 0.0045192559891560884,
  "measurement_cpu": 1,
  "min_arm_mean_frequency_khz": 3150000.0,
  "observed_frequency_observations": 132,
  "smt_sibling_cpus": [
    49
  ],
  "total_exhausted_pairs": 0,
  "total_preflight_failures": 0,
  "total_rejected_pair_attempts": 122,
  "total_rejected_preflight_windows": 126,
  "violations": []
}
```

### Rejected pair-attempt index

| pair | round | slot | attempt | issues | rejected preflight windows |
|---|---|---|---|---|---|
| irreducible-4 | 1 | 5 | 1 | irreducible-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.035s exceeds 0.034s | 0 |
| irreducible-4 | 1 | 5 | 2 | irreducible-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.067s exceeds 0.034s; irreducible-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.069s exceeds 0.035s | 0 |
| irreducible-4 | 1 | 5 | 3 | irreducible-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.057s exceeds 0.033s; irreducible-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.038s exceeds 0.035s | 0 |
| irreducible-4 | 1 | 5 | 4 | irreducible-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.052s exceeds 0.034s; irreducible-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.035s | 7 |
| irreducible-4 | 1 | 5 | 5 | irreducible-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.100s exceeds 0.034s; irreducible-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.047s exceeds 0.035s | 0 |
| irreducible-4 | 1 | 5 | 6 | irreducible-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.034s exceeds 0.033s | 6 |
| irreducible-4 | 1 | 5 | 7 | irreducible-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.035s | 0 |
| irreducible-16 | 1 | 7 | 1 | irreducible-16 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.053s exceeds 0.034s | 0 |
| irreducible-16 | 1 | 7 | 2 | irreducible-16 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.046s | 0 |
| irreducible-16 | 1 | 7 | 3 | irreducible-16 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.069s exceeds 0.033s | 0 |
| irreducible-16 | 1 | 7 | 4 | irreducible-16 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.096s exceeds 0.034s; irreducible-16 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.054s exceeds 0.045s | 0 |
| kernel-4 | 1 | 8 | 1 | kernel-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.038s | 0 |
| multiplicity-8 | 1 | 10 | 1 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.035s exceeds 0.034s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.108s exceeds 0.034s | 2 |
| multiplicity-8 | 1 | 10 | 2 | multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.043s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 3 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.046s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 4 | multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.042s exceeds 0.034s | 1 |
| multiplicity-8 | 1 | 10 | 5 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.034s | 1 |
| multiplicity-8 | 1 | 10 | 6 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 7 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.177s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 8 | multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.080s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 9 | multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.035s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 10 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.057s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.043s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 11 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.066s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.064s exceeds 0.035s | 2 |
| multiplicity-8 | 1 | 10 | 12 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 13 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.051s exceeds 0.034s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.084s exceeds 0.034s | 3 |
| multiplicity-8 | 1 | 10 | 14 | multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.078s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 15 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.106s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 16 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.055s exceeds 0.034s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.043s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 17 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.051s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.053s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 18 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.056s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 19 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.076s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.105s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 20 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.078s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 21 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.066s exceeds 0.034s | 2 |
| multiplicity-8 | 1 | 10 | 22 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.067s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 23 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.034s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.034s | 1 |
| multiplicity-8 | 1 | 10 | 24 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.053s exceeds 0.034s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.047s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 25 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.144s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 26 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.043s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.097s exceeds 0.034s | 1 |
| multiplicity-8 | 1 | 10 | 27 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.091s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 28 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.039s exceeds 0.034s | 0 |
| multiplicity-8 | 1 | 10 | 29 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.046s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 30 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.035s | 0 |
| multiplicity-8 | 1 | 10 | 31 | multiplicity-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.035s; multiplicity-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.088s exceeds 0.034s | 0 |
| factor-4 | 2 | 1 | 1 | factor-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.042s exceeds 0.033s | 0 |
| factor-8 | 2 | 2 | 1 | factor-8 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.035s; factor-8 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.491s exceeds 0.036s | 1 |
| irreducible-4 | 2 | 4 | 1 | irreducible-4 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.294s exceeds 0.037s; irreducible-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.033s | 0 |
| irreducible-4 | 2 | 4 | 2 | irreducible-4 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.039s exceeds 0.035s | 0 |
| irreducible-4 | 2 | 4 | 3 | irreducible-4 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.084s exceeds 0.035s | 1 |
| irreducible-4 | 2 | 4 | 4 | irreducible-4 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.056s exceeds 0.035s; irreducible-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.045s exceeds 0.033s | 1 |
| irreducible-4 | 2 | 4 | 5 | irreducible-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.090s exceeds 0.033s | 4 |
| irreducible-4 | 2 | 4 | 6 | irreducible-4 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.046s exceeds 0.035s | 0 |
| irreducible-4 | 2 | 4 | 7 | irreducible-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.089s exceeds 0.033s | 5 |
| irreducible-4 | 2 | 4 | 8 | irreducible-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.042s exceeds 0.033s | 1 |
| fresh-build-null | 2 | 10 | 1 | fresh-build-null round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.054s exceeds 0.033s | 0 |
| irreducible-4 | 3 | 3 | 1 | irreducible-4 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.033s | 0 |
| irreducible-4 | 3 | 3 | 2 | irreducible-4 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.044s exceeds 0.034s; irreducible-4 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.090s exceeds 0.035s | 1 |
| irreducible-8 | 3 | 4 | 1 | irreducible-8 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.055s exceeds 0.033s | 2 |
| kernel-4 | 3 | 6 | 1 | kernel-4 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.118s exceeds 0.034s; kernel-4 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.042s exceeds 0.038s | 0 |
| kernel-8 | 3 | 7 | 1 | kernel-8 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.034s exceeds 0.033s; kernel-8 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.162s exceeds 0.082s | 0 |
| kernel-8 | 3 | 7 | 2 | kernel-8 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.035s exceeds 0.034s; kernel-8 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.141s exceeds 0.082s | 0 |
| kernel-8 | 3 | 7 | 3 | kernel-8 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.113s exceeds 0.082s | 0 |
| kernel-8 | 3 | 7 | 4 | kernel-8 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.045s exceeds 0.033s | 0 |
| kernel-8 | 3 | 7 | 5 | kernel-8 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.071s exceeds 0.033s | 0 |
| multiplicity-8 | 3 | 8 | 1 | multiplicity-8 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.154s exceeds 0.035s | 0 |
| multiplicity-8 | 3 | 8 | 2 | multiplicity-8 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.073s exceeds 0.034s | 0 |
| kernel-8-null | 3 | 10 | 1 | kernel-8-null round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.104s exceeds 0.081s | 0 |
| kernel-8-null | 3 | 10 | 2 | kernel-8-null round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.152s exceeds 0.082s | 0 |
| kernel-8-null | 3 | 10 | 3 | kernel-8-null round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.548s exceeds 0.083s | 0 |
| factor-8 | 4 | 0 | 1 | factor-8 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.065s exceeds 0.034s; factor-8 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.049s exceeds 0.033s | 0 |
| factor-8 | 4 | 0 | 2 | factor-8 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.035s | 6 |
| factor-12 | 4 | 1 | 1 | factor-12 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.065s exceeds 0.036s | 0 |
| factor-12 | 4 | 1 | 2 | factor-12 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.076s exceeds 0.035s | 1 |
| factor-12 | 4 | 1 | 3 | factor-12 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.055s exceeds 0.035s; factor-12 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.062s exceeds 0.033s | 0 |
| factor-12 | 4 | 1 | 4 | factor-12 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.066s exceeds 0.033s | 0 |
| multiplicity-8 | 4 | 7 | 1 | multiplicity-8 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.144s exceeds 0.034s; multiplicity-8 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.035s | 0 |
| multiplicity-8 | 4 | 7 | 2 | multiplicity-8 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.034s; multiplicity-8 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.081s exceeds 0.034s | 0 |
| fresh-build-null | 4 | 8 | 1 | fresh-build-null round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.063s exceeds 0.033s | 1 |
| factor-4 | 4 | 10 | 1 | factor-4 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.079s exceeds 0.034s | 0 |
| factor-4 | 4 | 10 | 2 | factor-4 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.056s exceeds 0.033s | 0 |
| factor-12 | 5 | 0 | 1 | factor-12 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.125s exceeds 0.034s; factor-12 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.061s exceeds 0.035s | 0 |
| irreducible-16 | 5 | 3 | 1 | irreducible-16 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.078s exceeds 0.046s | 0 |
| irreducible-16 | 5 | 3 | 2 | irreducible-16 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.045s exceeds 0.033s; irreducible-16 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.138s exceeds 0.045s | 0 |
| irreducible-16 | 5 | 3 | 3 | irreducible-16 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.051s exceeds 0.045s | 0 |
| kernel-8 | 5 | 5 | 1 | kernel-8 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.062s exceeds 0.034s | 1 |
| multiplicity-8 | 5 | 6 | 1 | multiplicity-8 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.035s; multiplicity-8 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.063s exceeds 0.034s | 0 |
| multiplicity-8 | 5 | 6 | 2 | multiplicity-8 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.035s | 2 |
| multiplicity-8 | 5 | 6 | 3 | multiplicity-8 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.067s exceeds 0.034s | 0 |
| fresh-build-null | 5 | 7 | 1 | fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.092s exceeds 0.033s | 0 |
| fresh-build-null | 5 | 7 | 2 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.074s exceeds 0.034s; fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.118s exceeds 0.034s | 5 |
| fresh-build-null | 5 | 7 | 3 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.038s exceeds 0.034s; fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.068s exceeds 0.033s | 0 |
| fresh-build-null | 5 | 7 | 4 | fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.053s exceeds 0.033s | 0 |
| fresh-build-null | 5 | 7 | 5 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.034s | 0 |
| fresh-build-null | 5 | 7 | 6 | fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.033s | 1 |
| fresh-build-null | 5 | 7 | 7 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.056s exceeds 0.033s | 0 |
| fresh-build-null | 5 | 7 | 8 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.033s | 0 |
| fresh-build-null | 5 | 7 | 9 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.033s; fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.081s exceeds 0.033s | 0 |
| fresh-build-null | 5 | 7 | 10 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.078s exceeds 0.033s; fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.034s | 0 |
| fresh-build-null | 5 | 7 | 11 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.045s exceeds 0.033s; fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.055s exceeds 0.034s | 0 |
| fresh-build-null | 5 | 7 | 12 | fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.034s | 0 |
| fresh-build-null | 5 | 7 | 13 | fresh-build-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.057s exceeds 0.034s; fresh-build-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.033s | 0 |
| kernel-8-null | 5 | 8 | 1 | kernel-8-null round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.083s exceeds 0.083s | 0 |
| factor-4 | 5 | 9 | 1 | factor-4 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.034s exceeds 0.033s; factor-4 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.069s exceeds 0.034s | 0 |
| factor-4 | 5 | 9 | 2 | factor-4 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.064s exceeds 0.034s; factor-4 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.047s exceeds 0.034s | 6 |
| factor-4 | 5 | 9 | 3 | factor-4 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.076s exceeds 0.034s | 0 |
| irreducible-4 | 6 | 0 | 1 | irreducible-4 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.045s exceeds 0.035s | 5 |
| irreducible-8 | 6 | 1 | 1 | irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.056s exceeds 0.034s | 0 |
| irreducible-8 | 6 | 1 | 2 | irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.047s exceeds 0.034s | 1 |
| irreducible-8 | 6 | 1 | 3 | irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.065s exceeds 0.034s | 0 |
| irreducible-8 | 6 | 1 | 4 | irreducible-8 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.046s exceeds 0.036s | 3 |
| irreducible-8 | 6 | 1 | 5 | irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.071s exceeds 0.033s | 0 |
| irreducible-8 | 6 | 1 | 6 | irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.086s exceeds 0.034s | 0 |
| irreducible-8 | 6 | 1 | 7 | irreducible-8 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.036s; irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.071s exceeds 0.033s | 0 |
| kernel-8-null | 6 | 7 | 1 | kernel-8-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.360s exceeds 0.083s | 2 |
| kernel-8-null | 6 | 7 | 2 | kernel-8-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.116s exceeds 0.081s | 0 |
| kernel-8-null | 6 | 7 | 3 | kernel-8-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.122s exceeds 0.082s | 4 |
| kernel-8-null | 6 | 7 | 4 | kernel-8-null round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.144s exceeds 0.082s | 0 |
| factor-4 | 6 | 8 | 1 | factor-4 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.066s exceeds 0.034s; factor-4 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.033s | 0 |
| factor-8 | 6 | 9 | 1 | factor-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.076s exceeds 0.033s | 1 |
| factor-8 | 6 | 9 | 2 | factor-8 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.090s exceeds 0.035s; factor-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.043s exceeds 0.033s | 5 |
| factor-8 | 6 | 9 | 3 | factor-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.038s exceeds 0.033s | 8 |
| factor-12 | 6 | 10 | 1 | factor-12 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.165s exceeds 0.034s | 0 |
| factor-12 | 6 | 10 | 2 | factor-12 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.096s exceeds 0.035s; factor-12 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.052s exceeds 0.033s | 2 |


## Comparator Ratios

`no-comparable-surface-in-named-comparator`: no external tool emits and kernel-checks the same Lean proof term.

Executable integer-polynomial factorization belongs to the Mathlib-free `HexBerlekampZassenhaus` benchmark, whose headline report (`reports/hex-berlekamp-zassenhaus-performance.md`) records the FLINT, NTL, PARI, and Isabelle comparator ratios for the compiled factorizer these elaborators call as untrusted search. The `HexBerlekampZassenhausMathlib` bridge declarations have no separable compiled runtime kernel, so there are no external comparator ratios for these proof-emitting elaborators.

## Profile

Fresh-module elaboration, tactic, emitted-proof, and kernel-checking probes have no LeanBench timed region and therefore no sampling-profile obligation. Timed-region sampling does not apply.

The replacement evidence is the raw rotated fresh-build artifact cited above, including compiler/proof artifact sizes, exact source hashes, repository and dependency provenance, axiom validation, host accounting, rejected attempts, and accepted adjacent pairs.

## Concerns

None.
