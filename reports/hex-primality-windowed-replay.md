# Windowed primality certificate replay

Hex checks the complete Curve25519 certificate in **9.65 ms**, compared with
**19.16 ms** for PrimeCert in the adjacent comparison: a **1.99×** advantage.
Hex is faster on five of the seven inputs with certificates in both systems.
The 31-bit case is effectively tied; PrimeCert is faster at 61 bits and
supplies a Curve448 certificate that Hex's current construction profile does not find.

## Implementation

Both changes matter: on the 511-bit family input, windowed powering alone
takes 21.61 ms; adding raw bounded multiplication brings this to 6.02 ms.
For Curve25519 the corresponding figures are 9.28 and 8.87 ms. These
separately collected runs show which part of the checker remains costly;
they are not adjacent before/after comparisons.

`HexArith.powModNat` uses fixed windows of four bits through 512-bit moduli,
three bits through 1024-bit moduli, and narrower windows for small reduced
bases above that (two bits through 4096-bit moduli, then one bit for exponents
at least `2^64`). Other large inputs use the raw binary accumulator. The
certificate comparison below uses moduli through 512 bits.
The raw `Nat.rec` and `Bool.rec` loops avoid repeated match/instance reductions;
small `Nat.pow` operations within each window use the kernel's existing
arithmetic reductions. Its positive-modulus correctness theorem and zero-modulus
convention are preserved. This uses the same windowed algorithm as
[lean4#15167](https://github.com/leanprover/lean4/pull/15167), available here
without waiting for a toolchain upgrade.

`boundedPowMul` uses the same raw-recursion technique. Its equality with the
original compiled loop is proved for all inputs. The early multiplication-bound
checks remain in place, including for malformed certificates with enormous
exponents. This matters for the family inputs with factors such as `2^504`.

Compiled modular exponentiation still dispatches to Montgomery arithmetic and
the original reducing Nat fallback. Compiled bounded multiplication uses its
original loop. This change improves kernel checking; it does not claim a native
certificate-construction improvement. Certificates, witnesses, and search budgets
are unchanged, including the complete Curve25519 `#guard_msgs` literal.

## Complete-proof measurements

| Input | Hex kernel (ms) | PrimeCert kernel (ms) | PrimeCert / Hex |
|---|---:|---:|---:|
| family-31 | 1.588 | 1.578 | 0.99× |
| family-61 | 1.380 | 1.180 | 0.86× |
| family-123 | 1.923 | 2.339 | 1.22× |
| family-256 | 3.119 | 6.544 | 2.10× |
| family-511 | 6.238 | 10.109 | 1.62× |
| family-512 | 5.461 | 17.344 | 3.18× |
| Curve25519 | 9.648 | 19.162 | 1.99× |
| Curve448 | No certificate | 34.285 | — |

Each figure is the median of four samples from two runs, with reversed system
order within each run and an automatically selected CPU (CPU 1 in both runs). Every completed sample is retained, with
host load, complete proof source, source hashes, toolchains, and implementation
diffs. Both systems check complete local proof bodies after expanding local
auxiliary definitions and opaque theorems. A fresh kernel checker verifies each
proof against its declared goal. Pending asynchronous checks are drained before
timing. False-equality and corrupted-subject controls must fail. Imports,
construction, literal elaboration, and auxiliary expansion are outside this timer.

The initial final-implementation run measured Curve25519 at 10.33 and 36.58 ms
for Hex, versus 19.75 and 27.98 ms for PrimeCert. Both systems slowed late in
that run; recorded host load rose from 19 to 24. The cause is not established.
The one unchanged repeat measured Hex at 8.59 and 8.97 ms versus PrimeCert at
18.13 and 18.57 ms. All four samples contribute to the medians above and appear
in the plot; no completed sample was discarded. The wide range limits the
precision of a speedup claim.

Hex uses Lean 4.34.0; the unmodified PrimeCert checkout uses its pinned Lean
4.33.0. This is a comparison of those complete packages, not an isolated claim
about their algorithms on an identical kernel. Native decision and fresh-build
measurements remain separately documented in
[the construction report](hex-primality-construction.md).

![Full certificate kernel comparison](figures/hex-primality-kernel-direct.svg)

## Reproduction and retained experiments

```sh
python scripts/bench/primality_kernel_direct.py \
  reports/bench-results/hex-primality-cactus-native-executable-issue-10268.json \
  --primecert-checkout /path/to/PrimeCert \
  --output /tmp/primality-kernel.json --blocks 2
```

- [Windowed powering alone](bench-results/hex-primality-window-kernel.json):
  all 30 checks and two missing-certificate outcomes. Curve25519 is 9.28 ms
  for Hex versus 18.36 ms for PrimeCert. Hex wins only at 512 bits and
  Curve25519; PrimeCert leads on the other five shared inputs. Raw bounded
  multiplication then flips the 123-, 256-, and 511-bit cases in Hex's favor.
- [Windowed powering and raw bounded multiplication](bench-results/hex-primality-window-product-kernel.json):
  all 30 checks and two missing-certificate outcomes; the intermediate policy
  before the dispatch for large moduli and small bases.
- [Final implementation](bench-results/hex-primality-base-aware-kernel.json) and
  [its one unchanged repeat](bench-results/hex-primality-base-aware-repeat-kernel.json):
  all 60 checks and four missing-certificate outcomes. The
  [combined record](bench-results/hex-primality-base-aware-combined-kernel.json)
  supplies the table and plot above, preserving the original run identifiers.
- [Earlier checker comparison](bench-results/hex-primality-direct-kernel-checked-issue-10268.json):
  retained historical measurements, including 128.93 ms for Curve25519.
  This is not an adjacent before/after run against the new implementation.

## Validation

- `lake build`: all 14,400 jobs pass, including the manual and downstream libraries.
- Focused HexArith and HexPrimality conformance: window cutoffs at and around
  `2^512`, `2^1024`, and `2^4096`, reduced-base and exponent cutoffs at
  `2^64`, a 5001-bit exponent, modulus zero/one, Meta reduction, bounded-product overflow
  and zero cases, exact construction suggestions, and standalone literal replay.
- Existing HexArith, HexPrimality, and HexIntFactor benchmark verification:
  all pass within the wrapper's time budget (9 seconds on this host).
- Existing HexPrimality oracle script: fresh emission matches committed fixtures;
  PARI/FLINT and the independent certificate checker accept all 64 cases.
