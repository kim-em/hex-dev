# Scalar characteristic-two subtraction

The scalar sparse-row update keeps its existing validation and failure prefix. For modulus two, validation gives source coefficient one and target/factor values in {0,1}; subtraction then uses exact XOR. The runtime change adds only this shortcut. Ordinary polynomial powers, including squares, retain their usual meaning.

These manual shared-host measurements use one algorithm thread, automatically leased CPUs and adjacent AB followed by BA. Every completed process is retained. The inconclusive prime control has exactly one unchanged repeat; the F2 comparison has no repeat. Native C uses Clang 21.1.8 and Lean-generated C uses SDK Clang 23.1.0. Production AVX-512 is disabled. Candidate production, native verification, certificate generation and kernel checking are distinct; only candidate/process times appear below.

| Comparison | Process B/A | Candidate B/A | Equal-family B/A | Process pair range |
|---|---:|---:|---:|---:|
| f2-false | 0.881637 | 0.888794 | 0.934809 | 0.589295–1.251525 |
| prime-control | 1.004511 | 1.002884 | 1.004511 | 0.832635–1.215639 |
| prime-control-repeat | 1.005832 | 0.998731 | 1.005832 | 0.860519–1.220921 |

All 152 processes (76 pairs) return equal complete bases, with no failures or timeouts. The F2 development suite improves; the prime controls do not establish a general timing benefit. These inputs are not the fixed balanced acceptance suite or held-out inputs. No fastest-open-source milestone is claimed.

| Family | F2 | Prime first | Prime repeat |
|---|---:|---:|---:|
| cyclic | 0.917751 | 0.998451 | 0.998330 |
| kat | 0.958701 | 1.001051 | 1.005822 |
| eco | 0.935936 | 1.012317 | 1.004113 |
| noon | 1.058693 | 1.004992 | 1.007519 |
| reimer | 0.987919 | 0.996081 | 1.002356 |
| minrank | 1.002277 | 0.999865 | 1.020194 |
| dense-quadratic | 0.968489 | 1.019024 | 1.002634 |
| mq | 0.697519 | — | — |

| Comparison | Leased CPU | Peak RSS A/B (KiB) |
|---|---:|---:|
| f2-false | 42 | 89500/90416 |
| prime-control | 45 | 79940/80176 |
| prime-control-repeat | 90 | 79964/80028 |
| msolve | 43 | 90416/18024 |

The ten F2 systems comprise seven centered signed lifts of the existing prime-field families and three seeded quadratic systems (8, 9 and 10 variables) including squares. Degenerations and zero terms are retained in the A/B inputs. The comparator receives canonical generators for the same ideals. These are development observations, with unequal input counts by family; both input-weighted and equal-family aggregates are shown.

A separate current comparison with msolve `3672113ee2c696a2ac9c637636e0f7214f500ba1` completes forty processes with twenty equal full bases. Hex/msolve process ratios are 1.423340 by input and 1.234546 with equal family weights, with pair range 0.589214–3.160436. msolve uses Clang 23.1.3, `-O3 -march=native`, and `-g 2 -l 2 -t 1`. This leaves a performance gap.

| F2 family | Hex/msolve |
|---|---:|
| cyclic | 2.595471 |
| kat | 0.691523 |
| eco | 2.715833 |
| noon | 0.658867 |
| reimer | 0.706020 |
| minrank | 0.848708 |
| dense-quadratic | 1.114927 |
| mq | 2.514858 |

All twelve Clang 23.1.3/GCC 16.2.0 ASan+UBSan variants and all nine project checks pass. Existing conformance covers native/portable sparse updates, malformed prefixes, aliases, budgets, resumptions and complete F4 outputs. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. The `compute-reference` executable is the full-initialization build of the same native driver; its name does not imply portable arithmetic.

Baseline runtime `701fdd34b8f2`; XOR runtime `6e1a5fc2e06a`; checks `8d2ff7062fe1`. The capsule includes both full runtime source trees, the check source tree, compiler identities, raw process output, complete bases, memory, variability and collector scripts.
`f4-scalar-xor-6e1a5fc2e06a.tar.xz`: SHA-256 `a6178d1003119b70624b5431d868cf4dee12226e123e4be2ed865ad4fa157ef9`.

Regenerate with `python3 scripts/bench/groebner_xor_report.py --capsule reports/bench-results/raw/f4-scalar-xor-6e1a5fc2e06a.tar.xz --report reports/bench-results/hexgroebner-xor.md --check`. Add `--current` to bind the checkout.
