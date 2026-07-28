# Berlekamp Factor Phase Profile

Current compiled diagnostic at revision
`5c371a5abb85ca6ef6510ec60888f3048db71719`, 2026-07-28, on
`chungus2`, pinned to CPU 0.

The rebuilding baseline reconstructs the kernel for each basis vector. The
shared baseline builds it once. The fixed path is the current optimized
implementation.

| Fixture | Rebuilding baseline | Shared baseline | Fixed path | Rebuild/fixed |
|---|---:|---:|---:|---:|
| split degree 6 | 165.135 µs | 44.235 µs | 30.766 µs | `5.37x` |
| split degree 12 | 1.367 ms | 215.309 µs | 118.636 µs | `11.53x` |
| split degree 18 | 5.672 ms | 598.949 µs | 289.440 µs | `19.60x` |
| split degree 24 | 16.077 ms | 1.280 ms | 577.347 µs | `27.85x` |
| `Phi_15` | 215.019 µs | 55.031 µs | 55.112 µs | `3.90x` |
| `SD_3` | 325.994 µs | 73.509 µs | 71.587 µs | `4.55x` |
| `SD_4` | 4.879 ms | 439.953 µs | 414.275 µs | `11.78x` |

The dominant avoided work is repeated kernel reconstruction. The optimized
path is close to the shared baseline on low-split fixtures and substantially
better on fully split families.

Reproduce with:

```sh
taskset -c 0 env RELIFT_PROFILE=berlekamp \
  .lake/build/bin/hex_recursive_relift_spike
```
