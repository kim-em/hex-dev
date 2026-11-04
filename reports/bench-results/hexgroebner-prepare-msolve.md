# F₂ comparator gap after batched preparation

The frozen implementation `3d6488148183` remains slower than pinned msolve overall on this diagnostic suite: process geometric mean 1.169067×, equal-family geometric mean 1.135642×. The largest family ratios are `cyclic` (2.272471×) and `eco` (2.219818×). These observations do not establish performance leadership or identify a necessary language/runtime change. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.

CPU 12, one algorithm thread, adjacent AB/BA comparisons. All forty processes completed and all twenty paired complete reduced bases agree. Inputs use ordinary F₂, grevlex and explicit degree scheduling for Hex; msolve uses full reduced output (`-g 2`), linear algebra mode 2 and one thread. This is the first observation of this implementation against this comparator. No unchanged repeat is collected.

Both arms use the same GNU time wrapper for peak RSS. Process time includes launch, initialization, parsing, computation and complete output. Candidate production returns unchecked candidates. Certificate generation, independent final verification and kernel replay remain distinct and are excluded from these timing ratios. This ten-case diagnostic suite does not satisfy the SPEC’s field coverage, balanced/held-out suite or fastest-open-source acceptance requirements.

Hex native C uses `clang version 21.1.8`; generated C uses `clang version 23.1.0` (SDK). The comparator is msolve commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built using Clang 23.1.3 with `-O3 -march=native`. The source state, engine/shared-library and executable digests, recorded compile commands, toolchain and ISA context are retained. Compiler/tuning differences are part of this measured gap.

| Process Hex / msolve | Equal-family Hex / msolve | Min / median / max | Peak RSS Hex / msolve (KiB) |
|---:|---:|---|---|
| 1.169067 | 1.135642 | 0.621512 / 1.051565 / 2.326233 | 88008 / 17992 |

| Family | Hex / msolve process time |
|---|---:|
| cyclic | 2.272471 |
| kat | 0.713004 |
| eco | 2.219818 |
| noon | 0.720871 |
| reimer | 0.744053 |
| minrank | 0.870188 |
| dense-quadratic | 1.255211 |
| mq | 1.312902 |

Every completed sample, outlier, full output, resource failure and memory observation is retained. There were no failed or timed-out processes. The capsule also binds the implementation to all twelve Clang/GCC ASan/UBSan variants and all nine project checks, including independent basis oracles and downstream kernel replay. Timing ratios from different implementation stages are not multiplied to infer cumulative gains.

Raw capsule `f4-prepare-msolve-3d6488148183.tar.xz`: SHA-256 `fd34b004cadc9200bd25b3f953abee542b100520c4585c8abf8d4afaf107d5ad`.

```bash
python3 scripts/bench/groebner_prepare_comparator.py \
  --archive reports/bench-results/raw/f4-prepare-msolve-3d6488148183.tar.xz \
  --report reports/bench-results/hexgroebner-prepare-msolve.md --check
```
