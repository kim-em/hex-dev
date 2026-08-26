# HexRealRootsMathlib Performance Report

## Bench Targets

`HexRealRootsMathlib` is proof-only: it has no LeanBench executable or compiled runtime benchmark surface. These build-only fresh-module probes replace a compiled complexity registration for `isolate_roots` elaboration, proof emission, certificate replay, and ordinary kernel checking.
Accordingly, this surface has no LeanBench registration, executable,
`list`/`verify` entry, complexity verdict, or timed-region sampling profile.

| probe | reference | candidate | case |
|---|---|---|---|
| `fresh-build-null` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Baseline` | baseline, calibration-only |
| `natural-10-null` | `HexRealRootsMathlib.ProofProbe.Natural10` | `HexRealRootsMathlib.ProofProbe.Natural10` | natural-10, calibration-only |
| `natural-6` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Natural6` | natural-width, degree 6 |
| `natural-8` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Natural8` | natural-width, degree 8 |
| `natural-10` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Natural10` | natural-width, degree 10 |
| `refined-2` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Refined2` | width-2^-20, degree 2, width bits 20 |
| `refined-4` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Refined4` | width-2^-20, degree 4, width bits 20 |
| `refined-6` | `HexRealRootsMathlib.ProofProbe.Baseline` | `HexRealRootsMathlib.ProofProbe.Refined6` | width-2^-20, degree 6, width bits 20 |
| `refine-6` | `HexRealRootsMathlib.ProofProbe.Natural6` | `HexRealRootsMathlib.ProofProbe.Refined6` | refinement-attribution, degree 6, width bits 20 |

`HexRealRootsMathlibReplayProbe` supplies reduced CI coverage; `HexRealRootsMathlibReplayProbeScientific` owns the larger release arms.

## Verdicts

Scientific fresh-module run at commit `980aa6cb35ca38f804e308c05aca3e1c98d1c8b6` on designated host `chungus2`, logical CPU `19`.

Exact command invoked:

```sh
python3 scripts/bench/real_roots_mathlib_sweep.py --samples 6 \
  --timeout 180 --warm-timeout 600 \
  --shared-host --expected-host chungus2 --cpu 19 \
  --max-core-interference-ratio 0.005 \
  --output /tmp/real-roots-mathlib-shared-980aa6cb-cpu19-r005.json
```

The artifact below is the byte-for-byte committed copy of that `/tmp` output.

| field | artifact value |
|---|---|
| artifact | `reports/bench-results/hex-real-roots-mathlib-980aa6cb-chungus2.json` |
| artifact SHA-256 | `599a14c3971313d86ae23005d96b3484b963ef17535205a7012cd3be672cec3c` |
| embedded source-hash map | `source_sha256` in the cited artifact |
| schema | `hex-real-roots-mathlib-proof-probe-v4` |
| measurement | `paired-fresh-module-olean-wall-v1` |
| measurement state | `complete` |
| release quality | `True` |
| host protocol | `designated-shared-host-v3` |
| accepted paired samples | 54 |
| rejected pair attempts | 29 |
| rejected preflight windows | 56 |
| preflight failures | 0 |
| exhausted pairs | 0 |
| maximum admitted aggregate core-interference ratio | 0.004852 |
| maximum effective quantized core-interference ratio | 0.005581 |
| maximum core-interference allowance | 0.070840472 s |
| maximum preflight wait | 16.007267453 s |

This artifact predates the shared runner's
`paired-fresh-module-olean-wall-robust-null-v2` contract and remains a
historical v4/v1 record; it has not been retrospectively reclassified. Future
HexRealRootsMathlib captures use schema v5 and floor each robust null envelope
by the maximum observed absolute null delta.

Every sample cell is `reference / candidate / signed candidate−reference`; wall times are exact nanosecond values rendered as seconds. `R→C` and `C→R` record build orientation, and `aN` records the admitted complete-pair attempt.

Null controls are descriptive only: their medians are not subtracted, their ranges do not widen a budget, and they are neither significance tests nor scientific evidence.

### Null-control raw samples

| control | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `fresh-build-null` | a1, R→C; 5.592209936 s / 5.533458716 s / -0.058751220 s | a1, C→R; 5.444541821 s / 5.396453762 s / -0.048088059 s | a1, R→C; 5.377861840 s / 5.408055623 s / +0.030193783 s | a1, C→R; 5.440203345 s / 5.427048728 s / -0.013154617 s | a1, R→C; 5.422219460 s / 5.410256667 s / -0.011962793 s | a3, C→R; 5.415899069 s / 5.405701573 s / -0.010197496 s |
| `natural-10-null` | a1, R→C; 14.029235500 s / 14.009825989 s / -0.019409511 s | a1, C→R; 14.168094401 s / 13.905708794 s / -0.262385607 s | a1, R→C; 13.996509930 s / 13.988265522 s / -0.008244408 s | a1, C→R; 14.107348172 s / 13.892291469 s / -0.215056703 s | a1, R→C; 13.995542233 s / 13.912509150 s / -0.083033083 s | a1, C→R; 14.147974333 s / 14.092522261 s / -0.055452072 s |

### Null-control ranges and medians

| control | signed range | absolute span | per-sample Δ/reference relative range | median relative delta | median signed delta | zero-centred envelope | build magnitude |
|---|---|---|---|---|---|---|---|
| `fresh-build-null` | -0.058751220 s … +0.030193783 s | 0.088945003 s | -1.050590% … +0.561446%; span 1.612036% | -0.231215% | -0.012558705 s | 0.058751220 s | 5.431211402 s |
| `natural-10-null` | -0.262385607 s … -0.008244408 s | 0.254141199 s | -1.851947% … -0.058903%; span 1.793044% | -0.492613% | -0.069242577 s | 0.262385607 s | 14.068291836 s |

### Substantive raw samples

| proof pair | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `natural-6` | a1, R→C; 5.406263264 s / 7.719611977 s / +2.313348713 s | a1, C→R; 5.445058923 s / 7.730131454 s / +2.285072531 s | a1, R→C; 5.413837706 s / 7.739279478 s / +2.325441772 s | a1, C→R; 5.426402671 s / 7.720836410 s / +2.294433739 s | a1, R→C; 5.454486095 s / 7.829473694 s / +2.374987599 s | a2, C→R; 5.407957685 s / 7.700949318 s / +2.292991633 s |
| `natural-8` | a1, R→C; 5.408429304 s / 10.090289348 s / +4.681860044 s | a1, C→R; 5.415701786 s / 9.994418987 s / +4.578717201 s | a1, R→C; 5.388675369 s / 10.003936595 s / +4.615261226 s | a1, C→R; 5.410977621 s / 10.087155971 s / +4.676178350 s | a1, R→C; 5.420620375 s / 9.967137423 s / +4.546517048 s | a1, C→R; 5.431320377 s / 10.055889497 s / +4.624569120 s |
| `natural-10` | a3, R→C; 5.430992041 s / 14.148779516 s / +8.717787475 s | a1, C→R; 5.399323731 s / 14.078188855 s / +8.678865124 s | a2, R→C; 5.391809845 s / 13.983664428 s / +8.591854583 s | a2, C→R; 5.437915920 s / 13.910004293 s / +8.472088373 s | a2, R→C; 5.381381128 s / 14.082009273 s / +8.700628145 s | a1, C→R; 5.409544528 s / 14.146734419 s / +8.737189891 s |
| `refined-2` | a1, R→C; 5.392219433 s / 5.860059392 s / +0.467839959 s | a1, C→R; 5.385903783 s / 5.826010272 s / +0.440106489 s | a2, R→C; 5.475259330 s / 5.895317954 s / +0.420058624 s | a1, C→R; 5.397891676 s / 5.873718502 s / +0.475826826 s | a1, R→C; 5.427142718 s / 5.932320495 s / +0.505177777 s | a1, C→R; 5.385626497 s / 5.864198710 s / +0.478572213 s |
| `refined-4` | a4, R→C; 5.400468358 s / 6.537041473 s / +1.136573115 s | a2, C→R; 5.395939151 s / 6.582755167 s / +1.186816016 s | a1, R→C; 5.394786006 s / 6.527139042 s / +1.132353036 s | a1, C→R; 5.389144171 s / 6.512718804 s / +1.123574633 s | a2, R→C; 5.411283028 s / 6.590521033 s / +1.179238005 s | a1, C→R; 5.471002770 s / 6.564418368 s / +1.093415598 s |
| `refined-6` | a3, R→C; 5.375350914 s / 7.924665729 s / +2.549314815 s | a2, C→R; 5.390052662 s / 7.906636114 s / +2.516583452 s | a1, R→C; 5.399859130 s / 7.926537386 s / +2.526678256 s | a1, C→R; 5.401521213 s / 7.895242957 s / +2.493721744 s | a1, R→C; 5.395109360 s / 7.928253526 s / +2.533144166 s | a2, C→R; 5.454379478 s / 7.882223476 s / +2.427843998 s |
| `refine-6` | a2, R→C; 7.706459520 s / 7.912982704 s / +0.206523184 s | a1, C→R; 7.775535234 s / 7.935257549 s / +0.159722315 s | a3, R→C; 7.739454907 s / 7.919626520 s / +0.180171613 s | a1, C→R; 7.712374337 s / 7.925957366 s / +0.213583029 s | a2, R→C; 7.711063227 s / 7.941502349 s / +0.230439122 s | a8, C→R; 7.752394631 s / 7.914290969 s / +0.161896338 s |

### Substantive summaries

| proof pair | median reference | median candidate | median signed delta | control | magnitude ratio | raw control span | raw control envelope | scaled span | scaled envelope | resolution |
|---|---|---|---|---|---|---|---|---|---|---|
| `natural-6` | 5.420120188 s | 7.725483932 s | +2.303891226 s | fresh-build-null | 1.422424 | 0.088945003 s | 0.058751220 s | 0.126517483 s | 0.083569129 s | resolved |
| `natural-8` | 5.413339703 s | 10.029913046 s | +4.619915173 s | natural-10-null | 1.402633 | 0.254141199 s | 0.262385607 s | 0.254141199 s | 0.262385607 s | resolved |
| `natural-10` | 5.404434129 s | 14.080099064 s | +8.689746634 s | natural-10-null | 1.000839 | 0.254141199 s | 0.262385607 s | 0.254354495 s | 0.262605822 s | resolved |
| `refined-2` | 5.395055554 s | 5.868958606 s | +0.471833392 s | fresh-build-null | 1.080598 | 0.088945003 s | 0.058751220 s | 0.096113833 s | 0.063486478 s | resolved |
| `refined-4` | 5.398203754 s | 6.550729920 s | +1.134463075 s | fresh-build-null | 1.206127 | 0.088945003 s | 0.058751220 s | 0.107278957 s | 0.070861425 s | resolved |
| `refined-6` | 5.397484245 s | 7.915650921 s | +2.521630854 s | fresh-build-null | 1.457437 | 0.088945003 s | 0.058751220 s | 0.129631779 s | 0.085626229 s | resolved |
| `refine-6` | 7.725914622 s | 7.922791943 s | +0.193347398 s | fresh-build-null | 1.458752 | 0.088945003 s | 0.058751220 s | 0.129748725 s | 0.085703476 s | resolved |

Every practical-limit case in the SPEC completed well below the 180 s arm
timeout. The `natural-6`, `natural-8`, and `natural-10` candidate medians are
7.725483932 s, 10.029913046 s, and 14.080099064 s. At width `2^-20`, the
`refined-2`, `refined-4`, and `refined-6` candidate medians are 5.868958606 s,
6.550729920 s, and 7.915650921 s. The direct degree-6 refinement attribution is
+0.193347398 s. These results support the stated “cost seconds” practical
limits through natural degree 10 and refined degree 6; they do not extrapolate
beyond those cases or constitute an asymptotic verdict.

These are raw proof-track timings, never complexity verdicts. The reported timing is not corrected. Only wholly clean adjacent pair attempts enter the tables; rejected attempts and preflight windows remain in the cited artifact.

### Axiom validation and emitted artifact sizes

| module | expected axioms | observed axioms | ilean_bytes | olean_bytes | olean_private_bytes | olean_server_bytes | source_bytes |
|---|---|---|---|---|---|---|---|
| `HexRealRootsMathlib.ProofProbe.Baseline` | null | null | 168 | 1584 | 96 | 912 | 422 |
| `HexRealRootsMathlib.ProofProbe.Natural10` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 2348 | 12528 | 684008 | 1200 | 803 |
| `HexRealRootsMathlib.ProofProbe.Natural6` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1872 | 10576 | 393360 | 1200 | 717 |
| `HexRealRootsMathlib.ProofProbe.Natural8` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 2095 | 11552 | 529280 | 1200 | 757 |
| `HexRealRootsMathlib.ProofProbe.Refined2` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1486 | 8624 | 203792 | 1184 | 628 |
| `HexRealRootsMathlib.ProofProbe.Refined4` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1706 | 9600 | 313536 | 1184 | 678 |
| `HexRealRootsMathlib.ProofProbe.Refined6` | [propext, Classical.choice, Quot.sound] | [propext, Classical.choice, Quot.sound] | 1928 | 10576 | 442928 | 1184 | 732 |

### Provenance and configuration

| environment field | artifact value |
|---|---|
| git commit | 980aa6cb35ca38f804e308c05aca3e1c98d1c8b6 |
| git dirty | False |
| toolchain | leanprover/lean4:v4.32.0-rc1 |
| hostname | chungus2 |
| platform | Linux-6.12.95-x86_64-with-glibc2.42 |
| machine ID | 8be29815875342aeaae06e62d60f6b03 |
| architecture | x86_64 |
| CPU model | AMD EPYC 9455 48-Core Processor |
| Python | 3.13.13 |
| GNU time | /run/current-system/sw/bin/time |

Repository checkout:

```json
{
  "dirty": false,
  "head": "980aa6cb35ca38f804e308c05aca3e1c98d1c8b6",
  "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2",
  "state_sha256": "588ab971c00b5937815878498fd50d0a388cd0a4d238145f1ee355bb17759f73",
  "status": "",
  "tree": "544c1f111ae30d11b35769b66d652f469aaf6f9d"
}
```

Dependency checkouts:

```json
{
  "Cli": {
    "dirty": false,
    "head": "406ebb8c8e2f7e852a1b47764b42494022ce652c",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/Cli",
    "state_sha256": "fb2685089426172e1b49f64e334d41075b6e97d0252efe3d1df5a75814dd691f",
    "status": "",
    "tree": "11e883f1e68348ff48d70ea6d9a1585003ab637a"
  },
  "LeanSearchClient": {
    "dirty": false,
    "head": "c5d5b8fe6e5158def25cd28eb94e4141ad97c843",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/LeanSearchClient",
    "state_sha256": "8b9080c6fd5f0b3dac562f7a58b88dec467e78a184f04bfa705c093472d80169",
    "status": "",
    "tree": "d0224b6df6c90cc0b4ed2db6218037d31bfd6f52"
  },
  "MD4Lean": {
    "dirty": false,
    "head": "6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/MD4Lean",
    "state_sha256": "56401822ddb0ee856118cc0d88e47de19c48802beed7c54e082f8a8dcf0563ff",
    "status": "",
    "tree": "5d02fb3fef67944b3dd4242b7fc16170d258a260"
  },
  "Qq": {
    "dirty": false,
    "head": "7a62bd13860cd39ac98da16ffc8c24d601353f69",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/Qq",
    "state_sha256": "8e892eae3878af5d430b1bbcafc17664658d4a2502e353e53aec776a911a9122",
    "status": "",
    "tree": "31d436cbc8e28daf7c850d80738cab0e25a47e35"
  },
  "aesop": {
    "dirty": false,
    "head": "b5b9e2bb45ce91e4bc44eaa738c3a8910404ab82",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/aesop",
    "state_sha256": "07d9db85cd9e004c7ff5e9bb0d500f10675cac6579c00984aa2a60764623db99",
    "status": "",
    "tree": "7ba23c52c2f9919b48c85b15f1ea36d916336d0a"
  },
  "batteries": {
    "dirty": false,
    "head": "77d3cc514f987c1f42f2bbd8a8d56855012dc115",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/batteries",
    "state_sha256": "7e4fba14b402b73d6dbdbc8dc24f856c5d2a4aba1486b5dec093e599d72fb3f0",
    "status": "",
    "tree": "bbe05462df1fbe6974b8c22012f3d6d5d40f3d07"
  },
  "illuminate": {
    "dirty": false,
    "head": "ae95e7e7d01c072421732d0b84cf63ff903f4f0e",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/illuminate",
    "state_sha256": "4e09f250a3dbb90216dd81eac9cd81fa63bcc452c035007feee4cdee17360d0f",
    "status": "",
    "tree": "2ef0cbaea821858d59680c9f8cbbe3d63ba031b0"
  },
  "importGraph": {
    "dirty": false,
    "head": "41f407a8e85b0fdc00910633a8f14754139b63f4",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/importGraph",
    "state_sha256": "1e52ae39caffca1f19a5659523096b1c89c6472be660b3e95e202baee1b14657",
    "status": "",
    "tree": "7f8fb8b03b5681128ed3b0351290c9a44b79215d"
  },
  "lean-bench": {
    "dirty": false,
    "head": "fa30c2763cf523f3ac8e46dc3a1dad0845a40098",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/lean-bench",
    "state_sha256": "689f9504c42512f18b20bb58391f1b3026e7a114591037ba1c2e4400db003ff9",
    "status": "",
    "tree": "5e2c6d004439e19a8fc005e136fea4beb9f28c5b"
  },
  "mathlib": {
    "dirty": false,
    "head": "aaedc74a09fbe1da58b11cf4d27806a6fa1a86eb",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/mathlib",
    "state_sha256": "22581931070b9bea48e4d573b0d7eb193825a874c7c225e6b993e58750244e59",
    "status": "",
    "tree": "64f34bbc25b6bf7dd3a36524438065214d0518a4"
  },
  "plausible": {
    "dirty": false,
    "head": "f3c7bd5061bd81b4480295c524d4f245c8b7e4e2",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/plausible",
    "state_sha256": "770da451657fb96675011f952038b40e5c49a0e967bb841f2617a924e920a5c3",
    "status": "",
    "tree": "751b1c6d14208cb74ccbd501d3015ef6c1ee7fc9"
  },
  "proofwidgets": {
    "dirty": false,
    "head": "e6518a674e62de322b8f79eebeda7bcae2a36bc3",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/proofwidgets",
    "state_sha256": "16a41a3fef265fc102fd81c2e0f1dd00a3f02df5d86b0baa9004116935633a4a",
    "status": "",
    "tree": "af612c47c0ddeea7a0bbaee7d3fd69ddab46a903"
  },
  "subverso": {
    "dirty": false,
    "head": "0bd508e8362f56d4a05cbf63614d4c97db954041",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/subverso",
    "state_sha256": "e41d0e99844c299108a75ab96d2e988105f3792abf3664870f3a4692101214ef",
    "status": "",
    "tree": "f85ca946cf9618c87d4cf25a77089968e8504c4f"
  },
  "verso": {
    "dirty": false,
    "head": "8cb04559a9b9feb8efab43e135f662514561f668",
    "path": "/home/kim/worktrees/hex-dev/hex-dev-shared-host-v2/.lake/packages/verso",
    "state_sha256": "7cd0b36c7bd143024db6539906d00ac9431a2b9a668099cbdc204734701465ee",
    "status": "",
    "tree": "1e41fb0014e5125403fb09290628faecfc37ed70"
  }
}
```

The complete per-source SHA-256 map is retained under `source_sha256` in the cited artifact; the artifact file itself is anchored above by SHA-256 `599a14c3971313d86ae23005d96b3484b963ef17535205a7012cd3be672cec3c`.

Recorded configuration:

```json
{
  "accounting_quantization_ticks": 3,
  "allow_busy": false,
  "allow_dirty": false,
  "command_template": "lake build +<module>:olean",
  "core_interference_accounting": "measurement-cpu-foreign-plus-all-SMT-sibling-busy",
  "cpu_affinity": [
    19
  ],
  "cpu_topology": {
    "core_id": "49",
    "logical_cpu": 19,
    "physical_package_id": "0",
    "scaling_cur_freq_khz": "4447033",
    "scaling_governor": "schedutil",
    "thread_siblings_list": "19,67"
  },
  "expected_host": "chungus2",
  "frequency_measurement": "cpufreq-time-in-state-arm-mean",
  "lean_num_threads": "1",
  "max_core_interference_ratio": 0.005,
  "max_frequency_spread_ratio": 0.15,
  "max_load_per_cpu": 0.5,
  "max_pair_retries": 8,
  "measurement_cpu_foreign_accounting": "busy-minus-child-minus-runner-minus-irq-softirq",
  "minimum_control_magnitude_ratio": 2.0,
  "null_magnitude_factor": 3.0,
  "order": [
    "fresh-build-null",
    "natural-10-null",
    "natural-6",
    "natural-8",
    "natural-10",
    "refined-2",
    "refined-4",
    "refined-6",
    "refine-6"
  ],
  "pairing": "adjacent measured reference and candidate fresh modules; contamination retries the complete oriented pair",
  "preflight_max_busy_ticks": 2,
  "preflight_timeout_seconds": 300.0,
  "preflight_window_seconds": 2.0,
  "requested_cpu": 19,
  "rotation": "pairs left by round index; pair orientation alternates",
  "samples": 6,
  "shared_host": true,
  "timeout_seconds": 180.0,
  "warm_command_template": "lake build +<module>:deps",
  "warm_timeout_seconds": 600.0
}
```

### Shared-host interference observations

```json
{
  "accounting_quantization_ticks": 3,
  "expected_frequency_observations": 108,
  "frequency_spread_ratio": 0.0,
  "max_aggregate_core_interference_ratio": 0.004852309734784782,
  "max_arm_mean_frequency_khz": 3150000.0,
  "max_attempts_per_pair": 8,
  "max_concurrent_lake_lean_count": 26,
  "max_core_interference_ratio": 0.005,
  "max_cpu_pressure_some_delta_us": 1572218,
  "max_effective_core_interference_ratio": 0.005581030983831318,
  "max_frequency_spread_ratio": 0.15,
  "max_interference_allowance_seconds": 0.070840472005,
  "max_load_1m_per_cpu": 0.09314473470052083,
  "max_measurement_cpu_foreign_ratio": 0.002764602542622663,
  "max_measurement_cpu_interrupt_ratio": 0.005581030983831318,
  "max_preflight_wait_seconds": 16.007267453009263,
  "max_smt_sibling_busy_ratio": 0.004261911856558909,
  "measurement_cpu": 19,
  "min_arm_mean_frequency_khz": 3150000.0,
  "observed_frequency_observations": 108,
  "smt_sibling_cpus": [
    67
  ],
  "total_exhausted_pairs": 0,
  "total_preflight_failures": 0,
  "total_rejected_pair_attempts": 29,
  "total_rejected_preflight_windows": 56,
  "violations": []
}
```

Rejected pair-attempt index:

| pair | round | slot | attempt | issues | rejected preflight windows |
|---|---|---|---|---|---|
| natural-10 | 1 | 4 | 1 | natural-10 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.037s exceeds 0.030s | 0 |
| natural-10 | 1 | 4 | 2 | natural-10 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.034s exceeds 0.030s | 5 |
| refined-4 | 1 | 6 | 1 | refined-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.035s exceeds 0.030s | 7 |
| refined-4 | 1 | 6 | 2 | refined-4 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.370s exceeds 0.030s; refined-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.130s exceeds 0.033s | 0 |
| refined-4 | 1 | 6 | 3 | refined-4 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.036s exceeds 0.033s | 0 |
| refined-6 | 1 | 7 | 1 | refined-6 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.040s | 0 |
| refined-6 | 1 | 7 | 2 | refined-6 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.034s exceeds 0.030s; refined-6 round 1 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.087s exceeds 0.040s | 0 |
| refine-6 | 1 | 8 | 1 | refine-6 round 1 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.040s exceeds 0.039s | 0 |
| refined-4 | 2 | 5 | 1 | refined-4 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.061s exceeds 0.030s | 0 |
| refined-6 | 2 | 6 | 1 | refined-6 round 2 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.042s exceeds 0.030s | 0 |
| natural-10 | 3 | 2 | 1 | natural-10 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.072s exceeds 0.070s | 0 |
| refined-2 | 3 | 3 | 1 | refined-2 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.047s exceeds 0.030s | 0 |
| refine-6 | 3 | 6 | 1 | refine-6 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.041s exceeds 0.040s | 0 |
| refine-6 | 3 | 6 | 2 | refine-6 round 3 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.055s exceeds 0.040s; refine-6 round 3 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.083s exceeds 0.041s | 0 |
| natural-10 | 4 | 1 | 1 | natural-10 round 4 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.170s exceeds 0.070s; natural-10 round 4 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.071s exceeds 0.030s | 0 |
| natural-10 | 5 | 0 | 1 | natural-10 round 5 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.101s exceeds 0.070s | 0 |
| refined-4 | 5 | 2 | 1 | refined-4 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 1.274s exceeds 0.030s | 0 |
| refine-6 | 5 | 4 | 1 | refine-6 round 5 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.145s exceeds 0.039s | 0 |
| refined-6 | 6 | 2 | 1 | refined-6 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.030s | 0 |
| refine-6 | 6 | 3 | 1 | refine-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.042s exceeds 0.040s; refine-6 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.044s exceeds 0.039s | 1 |
| refine-6 | 6 | 3 | 2 | refine-6 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.055s exceeds 0.039s | 0 |
| refine-6 | 6 | 3 | 3 | refine-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.090s exceeds 0.040s; refine-6 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.085s exceeds 0.039s | 1 |
| refine-6 | 6 | 3 | 4 | refine-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.051s exceeds 0.040s | 4 |
| refine-6 | 6 | 3 | 5 | refine-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.040s; refine-6 round 6 reference: aggregate measurement-CPU foreign and SMT-sibling busy time 0.060s exceeds 0.040s | 0 |
| refine-6 | 6 | 3 | 6 | refine-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.140s exceeds 0.041s | 2 |
| refine-6 | 6 | 3 | 7 | refine-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.209s exceeds 0.041s | 2 |
| fresh-build-null | 6 | 4 | 1 | fresh-build-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.061s exceeds 0.030s | 0 |
| fresh-build-null | 6 | 4 | 2 | fresh-build-null round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.033s exceeds 0.030s | 0 |
| natural-6 | 6 | 6 | 1 | natural-6 round 6 candidate: aggregate measurement-CPU foreign and SMT-sibling busy time 0.436s exceeds 0.040s | 1 |

## Comparator Ratios

`no-comparable-surface-in-named-comparator`: no external tool emits and kernel-checks the same Lean proof term.

Executable isolation arithmetic belongs to the Mathlib-free `HexRealRoots` benchmark. The `HexRealRootsMathlib` bridge declarations have no separable compiled runtime kernel, so there are no external comparator ratios for this proof-emitting elaborator.

## Profile

Fresh-module elaboration, tactic, emitted-proof, and kernel-checking probes have no LeanBench timed region and therefore no sampling-profile obligation. Timed-region sampling does not apply.

The replacement evidence is the raw rotated fresh-build artifact cited above, including compiler/proof artifact sizes, exact source hashes, repository and dependency provenance, axiom validation, host accounting, rejected attempts, and accepted adjacent pairs.

## Concerns

None.
