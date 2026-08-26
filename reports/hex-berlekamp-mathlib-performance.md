# HexBerlekampMathlib Performance Report

## Bench Targets

`HexBerlekampMathlib` is proof-only: it has no LeanBench executable or compiled runtime benchmark surface. These build-only fresh-module probes replace a compiled complexity registration for `factor_poly`/`irreducibility` elaboration, proof emission, and ordinary kernel checking of the emitted certificates.
Accordingly, this surface has no LeanBench registration, executable,
`list`/`verify` entry, complexity verdict, or timed-region sampling profile.

| probe | reference | candidate | case |
|---|---|---|---|
| `fresh-build-null` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Baseline` | baseline, calibration-only |
| `irreducible-16-null` | `HexBerlekampMathlib.ProofProbe.Irreducible16` | `HexBerlekampMathlib.ProofProbe.Irreducible16` | irreducible-16, calibration-only |
| `factor-4` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Factor4` | factor-distinct, degree 4, 2 factors |
| `factor-8` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Factor8` | factor-distinct, degree 8, 4 factors |
| `factor-12` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Factor12` | factor-distinct, degree 12, 6 factors |
| `irreducible-4` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Irreducible4` | irreducibility, degree 4 |
| `irreducible-8` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Irreducible8` | irreducibility, degree 8 |
| `irreducible-16` | `HexBerlekampMathlib.ProofProbe.Baseline` | `HexBerlekampMathlib.ProofProbe.Irreducible16` | irreducibility, degree 16 |
| `multiplicity-8` | `HexBerlekampMathlib.ProofProbe.Factor8` | `HexBerlekampMathlib.ProofProbe.Repeated8` | multiplicity-attribution, degree 8, 4 factors |

All `factor_poly` inputs are products of distinct monic irreducible quadratics over `F_5` except `multiplicity-8`'s candidate, the fourth power of one irreducible quadratic (same degree and factor count as `factor-8`'s candidate, all multiplicity). All `irreducibility` inputs are the irreducible binomials `X^d + 2` over `F_5`.

`HexBerlekampMathlibProofProbe` supplies reduced CI coverage; `HexBerlekampMathlibProofProbeScientific` owns the larger release arms.

## Verdicts

Scientific fresh-module run at commit `b2435d4b824ac3fa42c464e943c933a50d116945` on designated host `chungus2`, logical CPU `1` (physical core `1`, SMT sibling CPU `49`).

Exact command invoked:

```sh
python3 scripts/bench/berlekamp_mathlib_sweep.py --samples 6 \
  --timeout 240 --warm-timeout 600 \
  --shared-host --expected-host chungus2 --cpu 1 \
  --max-core-interference-ratio 0.005 \
  --preflight-timeout-seconds 1800 \
  --output /tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/berlekamp-release-a1-cpu1.json
```

The artifact below is the byte-for-byte committed copy of that output.

| field | artifact value |
|---|---|
| artifact | `reports/bench-results/hex-berlekamp-mathlib-b2435d4b-chungus2.json` |
| artifact SHA-256 | `f489b912d81e508f07bb5ec3d3199dcc2f146bceaafaa30f9532ec314a3d4342` |
| embedded source-hash map | `source_sha256` in the cited artifact |
| schema | `hex-berlekamp-mathlib-proof-probe-v1` |
| measurement | `paired-fresh-module-olean-wall-robust-null-v2` |
| measurement state | `complete` |
| release quality | `True` |
| host protocol | `designated-shared-host-v3` |
| accepted paired samples | 54 |
| rejected pair attempts | 40 |
| rejected preflight windows | 878 |
| preflight failures | 0 |
| exhausted pairs | 0 |
| maximum admitted aggregate core-interference ratio | 0.013918 |
| maximum effective quantized core-interference ratio | 0.014862 |
| maximum core-interference allowance | 0.030000000 s |
| maximum preflight wait | 869.240740822 s |

The preregistered `--max-core-interference-ratio 0.005` governs each arm's
allowance as `max(quantization, ratio x wall)`. At these short (~2 s) arm
walls the three-tick accounting quantization floor (0.030 s) dominates, so
the maximum admitted aggregate ratio (0.013918) and the maximum effective
quantized ratio (0.014862) both reflect that floor, not an over-admitted
0.005-scaled arm.

Every sample cell is `reference / candidate / signed candidate-reference`; wall times are exact nanosecond values rendered as seconds. `R->C` and `C->R` record build orientation, and `aN` records the admitted complete-pair attempt.

Null controls are descriptive only: their medians are not subtracted, their ranges do not widen a budget, and they are neither significance tests nor scientific evidence. Under the `robust-null-v2` contract each robust null envelope is floored by the maximum observed absolute null delta, and substantive envelopes are interpolated between the two controls by build magnitude.

### Null-control raw samples

| control | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `fresh-build-null` | a4, R→C; 2.026639634 s / 2.030446920 s / +0.003807286 s | a1, C→R; 2.026126543 s / 2.025750252 s / -0.000376291 s | a1, R→C; 2.054684800 s / 2.042389496 s / -0.012295304 s | a1, C→R; 2.046247258 s / 2.050229933 s / +0.003982675 s | a1, R→C; 2.044978704 s / 2.042533191 s / -0.002445513 s | a2, C→R; 2.068802144 s / 2.045703014 s / -0.023099130 s |
| `irreducible-16-null` | a1, R→C; 4.243034180 s / 4.439197425 s / +0.196163245 s | a1, C→R; 4.356889947 s / 4.364686530 s / +0.007796583 s | a1, R→C; 4.247036884 s / 4.329333894 s / +0.082297010 s | a2, C→R; 4.355046443 s / 4.241007645 s / -0.114038798 s | a2, R→C; 4.244905230 s / 4.347165543 s / +0.102260313 s | a4, C→R; 4.252116013 s / 4.249968879 s / -0.002147134 s |

### Null-control ranges and medians

| control | signed range | absolute span | per-sample Δ/reference relative range | median relative delta | median signed delta | zero-centred robust envelope | build magnitude |
|---|---|---|---|---|---|---|---|
| `fresh-build-null` | -0.023099130 s … +0.003982675 s | 0.027081805 s | -1.116546% … +0.194633%; span 1.311179% | -0.069079% | -0.001410902 s | 0.028724229 s | 2.045612981 s |
| `irreducible-16-null` | -0.114038798 s … +0.196163245 s | 0.310202043 s | -2.618544% … +4.623183%; span 7.241727% | +1.058350% | +0.045046796 s | 0.242665526 s | 4.338249718 s |

### Substantive raw samples

| proof pair | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `factor-4` | a2, R→C; 2.062011045 s / 2.230268943 s / +0.168257898 s | a3, C→R; 2.055863170 s / 2.155533603 s / +0.099670433 s | a1, R→C; 2.024568369 s / 2.126646740 s / +0.102078371 s | a1, C→R; 2.068236315 s / 2.156768918 s / +0.088532603 s | a3, R→C; 2.050295053 s / 2.139180179 s / +0.088885126 s | a1, C→R; 2.054355896 s / 2.141477452 s / +0.087121556 s |
| `factor-8` | a1, R→C; 2.040102582 s / 2.223449058 s / +0.183346476 s | a1, C→R; 2.058904820 s / 2.250570826 s / +0.191666006 s | a2, R→C; 2.041181527 s / 2.236698209 s / +0.195516682 s | a1, C→R; 2.043113786 s / 2.238578292 s / +0.195464506 s | a4, R→C; 2.042791019 s / 2.311672073 s / +0.268881054 s | a1, C→R; 2.055666700 s / 2.245219183 s / +0.189552483 s |
| `factor-12` | a1, R→C; 2.072140078 s / 2.455897620 s / +0.383757542 s | a2, C→R; 2.080099726 s / 2.450359057 s / +0.370259331 s | a1, R→C; 2.076501341 s / 2.442845300 s / +0.366343959 s | a1, C→R; 2.038367824 s / 2.461025945 s / +0.422658121 s | a2, R→C; 2.053701605 s / 2.432962461 s / +0.379260856 s | a1, C→R; 2.067552415 s / 2.447512456 s / +0.379960041 s |
| `irreducible-4` | a1, R→C; 2.049480732 s / 2.142172765 s / +0.092692033 s | a1, C→R; 2.066841514 s / 2.267493866 s / +0.200652352 s | a4, R→C; 2.060559165 s / 2.146031141 s / +0.085471976 s | a1, C→R; 2.024206071 s / 2.124338707 s / +0.100132636 s | a1, R→C; 2.041065307 s / 2.157545662 s / +0.116480355 s | a1, C→R; 2.048393644 s / 2.249980693 s / +0.201587049 s |
| `irreducible-8` | a2, R→C; 2.048365608 s / 2.456266738 s / +0.407901130 s | a5, C→R; 2.018519637 s / 2.431152331 s / +0.412632694 s | a1, R→C; 2.033898932 s / 2.422381202 s / +0.388482270 s | a1, C→R; 2.020387757 s / 2.422620257 s / +0.402232500 s | a1, R→C; 2.059497146 s / 2.479212827 s / +0.419715681 s | a4, C→R; 2.201385811 s / 2.429544669 s / +0.228158858 s |
| `irreducible-16` | a5, R→C; 2.063767131 s / 4.356415804 s / +2.292648673 s | a2, C→R; 2.121081725 s / 4.358331465 s / +2.237249740 s | a2, R→C; 2.032940284 s / 4.234804459 s / +2.201864175 s | a1, C→R; 2.053827189 s / 4.239490373 s / +2.185663184 s | a1, R→C; 2.049479705 s / 4.242266374 s / +2.192786669 s | a1, C→R; 2.058379669 s / 4.342759130 s / +2.284379461 s |
| `multiplicity-8` | a1, R→C; 2.255538803 s / 2.147921854 s / -0.107616949 s | a3, C→R; 2.255161385 s / 2.177002716 s / -0.078158669 s | a1, R→C; 2.333405598 s / 2.161468349 s / -0.171937249 s | a1, C→R; 2.246251261 s / 2.144697942 s / -0.101553319 s | a2, R→C; 2.312261937 s / 2.148531594 s / -0.163730343 s | a1, C→R; 2.271206873 s / 2.144512293 s / -0.126694580 s |

### Substantive summaries

| proof pair | median reference | median candidate | median signed delta | control | magnitude ratio | raw control span | raw control envelope | scaled span | scaled envelope | resolution |
|---|---|---|---|---|---|---|---|---|---|---|
| `factor-4` | 2.055109533 s | 2.148505527 s | +0.094277779 s | fresh-build-null + irreducible-16-null | 1.050299 | 0.016379232 s | 0.038325822 s | 0.016379232 s | 0.038325822 s | resolved |
| `factor-8` | 2.042952402 s | 2.241898737 s | +0.193565256 s | fresh-build-null + irreducible-16-null | 1.095954 | 0.019814774 s | 0.047040969 s | 0.019814774 s | 0.047040969 s | resolved |
| `factor-12` | 2.069846246 s | 2.448935756 s | +0.379610448 s | fresh-build-null + irreducible-16-null | 1.197165 | 0.027430794 s | 0.066360980 s | 0.027430794 s | 0.066360980 s | resolved |
| `irreducible-4` | 2.048937188 s | 2.151788401 s | +0.108306495 s | fresh-build-null + irreducible-16-null | 1.051904 | 0.016499995 s | 0.038632169 s | 0.016499995 s | 0.038632169 s | resolved |
| `irreducible-8` | 2.041132270 s | 2.430348500 s | +0.405066815 s | fresh-build-null + irreducible-16-null | 1.188078 | 0.026747047 s | 0.064626479 s | 0.026747047 s | 0.064626479 s | resolved |
| `irreducible-16` | 2.056103429 s | 4.292512752 s | +2.219556957 s | fresh-build-null + irreducible-16-null | 1.010655 | 0.095248222 s | 0.238397504 s | 0.095248222 s | 0.238397504 s | resolved |
| `multiplicity-8` | 2.263372838 s | 2.148226724 s | -0.117155764 s | fresh-build-null + irreducible-16-null | 1.106452 | 0.020604716 s | 0.049044861 s | 0.020604716 s | 0.049044861 s | resolved |

The `factor-4`, `factor-8`, and `factor-12` candidate medians are
2.148505527 s, 2.241898737 s, and 2.448935756 s over the 2.05 s import-only
baseline: elaboration deltas of +0.094277779 s, +0.193565256 s, and
+0.379610448 s, growing roughly linearly in the distinct-quadratic count.
The `irreducibility` deltas are +0.108306495 s, +0.405066815 s, and
+2.219556957 s at degrees 4, 8, and 16; the degree-16 arm's growth is
dominated by the kernel-replayed Rabin divisibility checks at `p^16`. The
direct degree-8 multiplicity attribution is -0.117155764 s: the fourth power
of one quadratic elaborates faster than four distinct quadratics at the same
degree and factor count, consistent with the emitted certificate carrying one
irreducibility sub-certificate (with multiplicity four) instead of four
distinct ones. Every arm completed far below the 240 s timeout. These are
raw proof-track timings, never complexity verdicts. The reported timing is
not corrected. Only wholly clean adjacent pair attempts enter the tables;
rejected attempts and preflight windows remain in the cited artifact.

### Axiom validation and emitted artifact sizes

| module | expected axioms | observed axioms | ilean_bytes | olean_bytes | olean_private_bytes | olean_server_bytes | source_bytes |
|---|---|---|---|---|---|---|---|
| `HexBerlekampMathlib.ProofProbe.Baseline` | null | null | 325 | 1840 | 808 | 1576 | 582 |
| `HexBerlekampMathlib.ProofProbe.Factor12` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1638 | 12232 | 48064 | 1632 | 816 |
| `HexBerlekampMathlib.ProofProbe.Factor4` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1186 | 10648 | 30992 | 1632 | 715 |
| `HexBerlekampMathlib.ProofProbe.Factor8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1403 | 11384 | 37432 | 1632 | 762 |
| `HexBerlekampMathlib.ProofProbe.Irreducible16` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1529 | 9784 | 47472 | 1472 | 733 |
| `HexBerlekampMathlib.ProofProbe.Irreducible4` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1518 | 9784 | 27928 | 1464 | 718 |
| `HexBerlekampMathlib.ProofProbe.Irreducible8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1518 | 9784 | 34352 | 1456 | 716 |
| `HexBerlekampMathlib.ProofProbe.Repeated8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1313 | 9984 | 30520 | 1800 | 813 |

### Provenance and configuration

| environment field | artifact value |
|---|---|
| git commit | b2435d4b824ac3fa42c464e943c933a50d116945 |
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
  "head": "b2435d4b824ac3fa42c464e943c933a50d116945",
  "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7",
  "state_sha256": "0ee4d4b5b8636bb32cde9861d376e39582dd1a4fe81a17bd39ebc9578f431c37",
  "status": "",
  "tree": "9a08c4489d232126015d3b0ad2a84356c7b76e26"
}
```

Dependency checkouts:
```json
{
  "Cli": {
    "dirty": false,
    "head": "ab3a82db9fea14cf0fd7f5a2de650f4b534640af",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/Cli",
    "state_sha256": "65df434312cafbe625f7c255f523575c7ac14dd658fe7d755edcf376634406e2",
    "status": "",
    "tree": "9f7b5faae284be737c556b3b205043b293061fd2"
  },
  "LeanSearchClient": {
    "dirty": false,
    "head": "ba67e212be1197b84c1f1f6299488a10a3002713",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/LeanSearchClient",
    "state_sha256": "4554659b2b9ebedb58446b1c8d0c3b4439940cd9b4d92c081036ca51b3c4d1dc",
    "status": "",
    "tree": "89abb77cd7d9344beed0f5e041b444c5458674f7"
  },
  "MD4Lean": {
    "dirty": false,
    "head": "31907cc18f48a95384f99cee5582c00fb39e0f67",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/MD4Lean",
    "state_sha256": "371e7dd0e12c88d3bf727066e87ba96e0b3630c1b381e30f80bb86d2d3d98b01",
    "status": "",
    "tree": "968ae7de50111d78c47ecf0682e9de2dfd257f67"
  },
  "Qq": {
    "dirty": false,
    "head": "507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/Qq",
    "state_sha256": "a98d09e28230aad983f781592db94732afd1c3f6ee89665f5381a4a523c24cd7",
    "status": "",
    "tree": "22ba3c95e36bbc7d0aa9d55677ffebf0be90cccd"
  },
  "aesop": {
    "dirty": false,
    "head": "18889deb9e83ea7420ef51c160d6f88552e744e3",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/aesop",
    "state_sha256": "6f95bf2c6fe0e9d21f222f7894115224789824d945de6e03ebb05077c5c6035e",
    "status": "",
    "tree": "ef71b806106b107d2b259d9b50077d4786aefb66"
  },
  "batteries": {
    "dirty": false,
    "head": "d54dddc581e08be364c278052863524bff7a99a9",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/batteries",
    "state_sha256": "d147fd1a7a237e14711c7d53bbac46f83e1df7f386e6368dde5dfcd3274aa6b9",
    "status": "",
    "tree": "f7460b599b386df89d85bfdf1a7465cd44ff0861"
  },
  "illuminate": {
    "dirty": false,
    "head": "6e558472c981dbee8cb9fcde92fa9593daf04228",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/illuminate",
    "state_sha256": "a98eb6e62a445ff4d98e457669bdcf6fbd215cfb275333232cef9833329a925a",
    "status": "",
    "tree": "6fe64d8f2c0a64d7b7a3647f555f465fb636a55b"
  },
  "importGraph": {
    "dirty": false,
    "head": "d8823026ac7ef130c253089d95685f9877b95323",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/importGraph",
    "state_sha256": "24ea70ed738b9b9a3e6f6e4fb49174b541e5fe5f285b730163cd3cba093193b4",
    "status": "",
    "tree": "d5d88b13966b0a4d89a5d04e5cf9f8f5bf25dfeb"
  },
  "lean-bench": {
    "dirty": false,
    "head": "fa30c2763cf523f3ac8e46dc3a1dad0845a40098",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/lean-bench",
    "state_sha256": "689f9504c42512f18b20bb58391f1b3026e7a114591037ba1c2e4400db003ff9",
    "status": "",
    "tree": "5e2c6d004439e19a8fc005e136fea4beb9f28c5b"
  },
  "mathlib": {
    "dirty": false,
    "head": "85e3a25e006c35636f0e53b0e9296caca2685bc0",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/mathlib",
    "state_sha256": "40b120f09ff47e9ca7d54b6aca919463d61cb27f1ad58ee07362fe7b54bf3c23",
    "status": "",
    "tree": "955cb3928b885a10e8deb4e1f293f8f50d82664e"
  },
  "plausible": {
    "dirty": false,
    "head": "d9598f07b1bc701f1e3aae163d2681c1fd978793",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/plausible",
    "state_sha256": "9bd4c1e4cd877b3bdc974e50fc27789ab6a80107ae139a051d3f467037d4e16e",
    "status": "",
    "tree": "81f195d87b0f1efa7b9430b6d21034ed51bd2006"
  },
  "proofwidgets": {
    "dirty": false,
    "head": "a8acbfd87375ff4abe14ce09db5b7664d383bc7f",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/proofwidgets",
    "state_sha256": "cb5d130298c96a2f42742dc55b5ca802ee6703fb70147c39d23a10ffaecc8687",
    "status": "",
    "tree": "7c0d97efaaf9c6b9faeed6c863b8c4085cc989a2"
  },
  "subverso": {
    "dirty": false,
    "head": "847084e80500726e4331dded5f17007ddaf89c31",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/subverso",
    "state_sha256": "1ce57a39bc7eb6e755cb1a46f70ea6022bfdf80c5436ff2108efa77c6e9918e6",
    "status": "",
    "tree": "653a5d4a775e9b68056f0f8b9b253da8c65c286f"
  },
  "verso": {
    "dirty": false,
    "head": "90c688db9db7280364c8bd7f8264c82a01582fd4",
    "path": "/tmp/claude-1003/-home-kim-worktrees-hex-dev-hex-dev-future-work/89518927-81bd-474c-82a2-02d9e7f81d9e/scratchpad/wt-b7/.lake/packages/verso",
    "state_sha256": "a5dfe8c36b946d57874bafe6ebdd4477bf0415624f31e324f4f733587b76810d",
    "status": "",
    "tree": "a8e1171167bee808e429a0bf3492a96bd54c5c1a"
  }
}
```

The complete per-source SHA-256 map is retained under `source_sha256` in the cited artifact; the artifact file itself is anchored above by SHA-256 `f489b912d81e508f07bb5ec3d3199dcc2f146bceaafaa30f9532ec314a3d4342`.

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
    "scaling_cur_freq_khz": "4159636",
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
  "max_pair_retries": 8,
  "measurement_cpu_foreign_accounting": "busy-minus-child-minus-runner-minus-irq-softirq",
  "minimum_control_magnitude_ratio": 2.0,
  "null_magnitude_factor": 3.0,
  "order": [
    "fresh-build-null",
    "irreducible-16-null",
    "factor-4",
    "factor-8",
    "factor-12",
    "irreducible-4",
    "irreducible-8",
    "irreducible-16",
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
  "timeout_seconds": 240.0,
  "warm_command_template": "lake build +<module>:deps",
  "warm_timeout_seconds": 600.0
}
```

### Shared-host interference observations
```json
{
  "accounting_quantization_ticks": 3,
  "expected_frequency_observations": 108,
  "frequency_spread_ratio": 0.004865556978232988,
  "max_aggregate_core_interference_ratio": 0.01391766751316101,
  "max_arm_mean_frequency_khz": 3150000.0,
  "max_attempts_per_pair": 5,
  "max_concurrent_lake_lean_count": 20,
  "max_core_interference_ratio": 0.005,
  "max_cpu_pressure_some_delta_us": 385865,
  "max_effective_core_interference_ratio": 0.014862377085707788,
  "max_frequency_spread_ratio": 0.15,
  "max_interference_allowance_seconds": 0.03,
  "max_load_1m_per_cpu": 0.5543111165364584,
  "max_measurement_cpu_foreign_ratio": 0.008843036275386615,
  "max_measurement_cpu_interrupt_ratio": 0.009798804541632435,
  "max_preflight_wait_seconds": 869.2397408219986,
  "max_smt_sibling_busy_ratio": 0.01391766751316101,
  "measurement_cpu": 1,
  "min_arm_mean_frequency_khz": 3134747.7064220184,
  "observed_frequency_observations": 108,
  "smt_sibling_cpus": [
    49
  ],
  "total_exhausted_pairs": 0,
  "total_preflight_failures": 0,
  "total_rejected_pair_attempts": 40,
  "total_rejected_preflight_windows": 878,
  "violations": []
}
```

### Rejected pair-attempt index

| pair | round | slot | attempt | issues | rejected preflight windows |
|---|---|---|---|---|---|
| fresh-build-null | 1 | 0 | 1 | fresh-build-null round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.170s exceeds 0.030s | 433 |
| fresh-build-null | 1 | 0 | 2 | fresh-build-null round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 1.301s exceeds 0.030s; fresh-build-null round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.073s exceeds 0.030s | 29 |
| fresh-build-null | 1 | 0 | 3 | fresh-build-null round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.240s exceeds 0.030s | 7 |
| factor-4 | 1 | 2 | 1 | factor-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.149s exceeds 0.030s | 10 |
| irreducible-8 | 1 | 6 | 1 | irreducible-8 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.030s; irreducible-8 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.675s exceeds 0.030s | 0 |
| irreducible-16 | 1 | 7 | 1 | irreducible-16 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.030s | 0 |
| irreducible-16 | 1 | 7 | 2 | irreducible-16 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.038s exceeds 0.030s | 0 |
| irreducible-16 | 1 | 7 | 3 | irreducible-16 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.086s exceeds 0.030s | 5 |
| irreducible-16 | 1 | 7 | 4 | irreducible-16 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.038s exceeds 0.030s | 0 |
| factor-4 | 2 | 1 | 1 | factor-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.030s | 1 |
| factor-4 | 2 | 1 | 2 | factor-4 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.043s exceeds 0.030s | 1 |
| factor-12 | 2 | 3 | 1 | factor-12 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.038s exceeds 0.030s | 1 |
| irreducible-8 | 2 | 5 | 1 | irreducible-8 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.031s exceeds 0.030s | 13 |
| irreducible-8 | 2 | 5 | 2 | irreducible-8 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.034s exceeds 0.030s | 1 |
| irreducible-8 | 2 | 5 | 3 | irreducible-8 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.032s exceeds 0.030s; irreducible-8 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.037s exceeds 0.030s | 8 |
| irreducible-8 | 2 | 5 | 4 | irreducible-8 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.032s exceeds 0.030s; irreducible-8 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.046s exceeds 0.030s | 0 |
| irreducible-16 | 2 | 6 | 1 | irreducible-16 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.057s exceeds 0.030s | 0 |
| multiplicity-8 | 2 | 7 | 1 | multiplicity-8 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.444s exceeds 0.030s | 18 |
| multiplicity-8 | 2 | 7 | 2 | multiplicity-8 round 2 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.030s; multiplicity-8 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.062s exceeds 0.030s | 33 |
| factor-8 | 3 | 1 | 1 | factor-8 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.053s exceeds 0.030s | 0 |
| irreducible-4 | 3 | 3 | 1 | irreducible-4 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.051s exceeds 0.030s | 4 |
| irreducible-4 | 3 | 3 | 2 | irreducible-4 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.033s exceeds 0.030s | 0 |
| irreducible-4 | 3 | 3 | 3 | irreducible-4 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.030s exceeds 0.030s | 1 |
| irreducible-16 | 3 | 5 | 1 | irreducible-16 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.030s | 0 |
| irreducible-16-null | 4 | 7 | 1 | irreducible-16-null round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 1.112s exceeds 0.030s | 1 |
| factor-12 | 5 | 0 | 1 | factor-12 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.057s exceeds 0.030s | 0 |
| multiplicity-8 | 5 | 4 | 1 | multiplicity-8 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.064s exceeds 0.030s | 0 |
| irreducible-16-null | 5 | 6 | 1 | irreducible-16-null round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.030s | 3 |
| factor-4 | 5 | 7 | 1 | factor-4 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.030s | 0 |
| factor-4 | 5 | 7 | 2 | factor-4 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.032s exceeds 0.030s | 1 |
| factor-8 | 5 | 8 | 1 | factor-8 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.081s exceeds 0.030s | 2 |
| factor-8 | 5 | 8 | 2 | factor-8 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.070s exceeds 0.030s | 0 |
| factor-8 | 5 | 8 | 3 | factor-8 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.058s exceeds 0.030s | 0 |
| irreducible-8 | 6 | 1 | 1 | irreducible-8 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.031s exceeds 0.030s | 5 |
| irreducible-8 | 6 | 1 | 2 | irreducible-8 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.030s exceeds 0.030s; irreducible-8 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.030s | 0 |
| irreducible-8 | 6 | 1 | 3 | irreducible-8 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.030s | 2 |
| fresh-build-null | 6 | 4 | 1 | fresh-build-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.032s exceeds 0.030s | 0 |
| irreducible-16-null | 6 | 5 | 1 | irreducible-16-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.033s exceeds 0.030s; irreducible-16-null round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.030s exceeds 0.030s | 0 |
| irreducible-16-null | 6 | 5 | 2 | irreducible-16-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.045s exceeds 0.030s; irreducible-16-null round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.133s exceeds 0.030s | 0 |
| irreducible-16-null | 6 | 5 | 3 | irreducible-16-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.050s exceeds 0.030s | 0 |

## Comparator Ratios

`no-comparable-surface-in-named-comparator`: no external tool emits and kernel-checks the same Lean proof term.

Executable factorization arithmetic belongs to the Mathlib-free `HexBerlekamp` benchmark, whose headline report records the FLINT comparator ratios for the compiled kernels. The `HexBerlekampMathlib` bridge declarations have no separable compiled runtime kernel, so there are no external comparator ratios for these proof-emitting elaborators.

## Profile

Fresh-module elaboration, tactic, emitted-proof, and kernel-checking probes have no LeanBench timed region and therefore no sampling-profile obligation. Timed-region sampling does not apply.

The replacement evidence is the raw rotated fresh-build artifact cited above, including compiler/proof artifact sizes, exact source hashes, repository and dependency provenance, axiom validation, host accounting, rejected attempts, and accepted adjacent pairs.

## Concerns

None.
