# HexLLL Performance Report

## Bench Targets

- `Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum`: fixed
  fpLLL comparator for the BZ recombination input.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum`: fixed
  fpLLL comparator for the random-bounded bottom rung at `n = 30`.
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum`: fixed fpLLL
  comparator for the harsh-cubic bottom rung at `n = 15`.

## Verdicts

Informational fpLLL comparator run at commit
`ed9da7537e96cee75f395e46962d41775f615a53` on `carica` (Apple M2 Ultra,
macOS), command:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench run \
  Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum \
  --export-file reports/bench-results/hex-lll-fpylll-ed9da7537e96.json
```

The run used `fpylll 0.6.4`, `python-flint 0.8.0`, and deterministic benchmark
inputs from `HexLLL/Bench.lean`; no random seeds are involved. The harness
recorded `ed9da75-dirty` because this worktree carried a pre-existing local
`.claude/CLAUDE.md` modification outside this evidence package. Export
artefact: `reports/bench-results/hex-lll-fpylll-ed9da7537e96.json`, SHA-256
`9a2d74112dd5581db820854019a4ff9941dfd7b806678b4aae310cadf3e666e9`.

- `Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum`: median
  `84.919 ms`, min `84.325 ms`, max `94.951 ms`, observed hash
  `0x3c0064007a0036`.
- `Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum`: median
  `85.203 ms`, min `84.539 ms`, max `98.094 ms`, observed hash
  `0xf977db3a0120001a`.
- `Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum`: median
  `85.075 ms`, min `83.981 ms`, max `94.704 ms`, observed hash
  `0x949fde47fa1fffb4`.

All three fixed fpLLL registrations matched their expected hashes.

## Comparator Ratios

`SPEC/Libraries/hex-lll.md` classifies the fpLLL comparator as informational.
The ratios below are fixed bottom-rung comparisons of Lean's first-short-vector
checksum target against the process-call fpLLL target, with Lean as the
baseline:

```sh
PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench compare \
  Hex.LLLBench.runFirstShortVectorBZRecombinationChecksum \
  Hex.LLLBench.runFpylllFirstShortVectorBZRecombinationChecksum

PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench compare \
  Hex.LLLBench.runFirstShortVectorRandomBounded30Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorRandomBounded30Checksum

PATH="$PWD/.venv-oracles/bin:$PATH" lake exe hexlll_bench compare \
  Hex.LLLBench.runFirstShortVectorHarshCubic15Checksum \
  Hex.LLLBench.runFpylllFirstShortVectorHarshCubic15Checksum
```

- BZ recombination: Lean median `8.833 us`, fpLLL median `83.531 ms`, fpLLL
  relative median `9456.748x`; hashes agreed.
- Random-bounded `n = 30`: Lean median `5.752 ms`, fpLLL median `86.261 ms`,
  fpLLL relative median `14.996x`; hashes agreed.
- Harsh-cubic `n = 15`: Lean median `1.247 ms`, fpLLL median `84.130 ms`,
  fpLLL relative median `67.475x`; hashes agreed.

The fpLLL figures include Python process startup and oracle parsing overhead
for each fixed call, as specified by the process-call comparator registration.
They are therefore useful as traceable external-comparator checks for the
headline report, but they are not a gating performance signal for HexLLL.

## Profile

No HexLLL profiling artefacts are recorded in this snapshot.

## Concerns

None for the informational fpLLL comparator snapshot. The fixed comparator
hashes agreed with Lean on all three bottom-rung families.
