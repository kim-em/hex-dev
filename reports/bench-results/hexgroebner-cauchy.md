# Packed Macaulay elimination

The scalar prime-field kernel over `p = 65537` was measured on the shared
`chungus2` host with Lean `v4.35.0-rc3`, one automatically leased CPU and three
trial-major outer trials. Inputs are full-rank Cauchy matrices of dimension
`n`, with half the rows supplied as reducers. Input preparation is excluded;
validation, workspace allocation, elimination, output decoding and structural
hashing are included. Provenance is disabled. This is a matrix kernel and
contains no polynomial symbolic preprocessing or full F4 computation.

| n | Median | Min | Max |
| --- | ---: | ---: | ---: |
| 32 | 0.3480 ms | 0.3475 ms | 0.3501 ms |
| 64 | 2.045 ms | 2.042 ms | 2.090 ms |
| 128 | 13.922 ms | 13.913 ms | 13.924 ms |
| 256 | 102.749 ms | 102.700 ms | 102.814 ms |

The [500 ms target sweep](hexgroebner-cauchy-71383709ad2f.json) has source
fingerprint `71383709ad2f`; its [manifest](hexgroebner-cauchy-71383709ad2f.manifest),
[host/command metadata](hexgroebner-cauchy-71383709ad2f.measurement.json) and
[complete output](hexgroebner-cauchy-71383709ad2f.log) are retained. All twelve
rows completed. Reported per-process peak RSS ranges from 71,688 to 73,736 KiB.
These are host-specific observations, including runtime and prepared input.

The registered model is cubic. The harness verdict is **inconclusive**, with
normalized residual slope `β = -0.262`. The actual sparse pivot update count
on this family is `(n³ - n)/3`; validation and scatter visit `n²` entries each,
pivot scans visit `n²` positions, and output extraction visits `n(n+1)/2`
positions. These quadratic terms predict growth below the leading cubic law
over finite dimensions. Their timing contributions have not been separately
attributed, so this sweep does not establish the declared asymptotic timing
law. No library phase completion is recorded.

The [100 ms target sweep](hexgroebner-cauchy-76b276ff26f8.json),
[manifest](hexgroebner-cauchy-76b276ff26f8.manifest),
[metadata](hexgroebner-cauchy-76b276ff26f8.measurement.json) and
[output](hexgroebner-cauchy-76b276ff26f8.log) retain all twelve completed rows.
They are below the harness's ten-times-spawn-floor threshold and supply no
verdict-eligible rows. The larger target changes sampling duration while
preserving matrices, dimensions, trial count and the cubic model. Neither
sweep discards a completed sample based on host load.

There are no external comparator measurements or correctness-theorem timings.
The fastest-open-source and overall-fastest F4 gaps remain unmeasured under
[#10987](https://github.com/kim-em/hex-dev/issues/10987). Full F4, finite
extensions, certificate generation, independent complete-basis verification
and kernel soundness proofs remain separate deliverables.
