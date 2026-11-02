# Strided Mersenne-prime vector products

Build/snapshot identifiers may be capsule-only identifiers after rebasing.
The capsule retains exact source overlays and artifact digests independently.

At modulus 2^31−1, exact product folding now applies to strided as well as
contiguous vectors. The stored coefficients stay canonical. Modular halving
recovers the existing factor from its Montgomery multiplier; the fold depends
on coefficient values, not column positions. Bounds, canonical-value checks,
scalar replay, quantum ticks and charge prefixes are unchanged.

Baseline fingerprint `1e1015abfc77`; candidate `bd103dc595b5`,
commit `3691f668093d01a8193b9cb739f5f069e223ed9f`, snapshot `543b0d004f71f18ae734748120972b17ebb10487`.
Candidate compute/reference SHA256: `956731c2fb6873ab9cc05ff01ec7f90193cab9179ec2befc4ee298f178d1cb19` /
`b58e2ab8af8923b77fc2cf81b2260fcd873721514ddd4270589150d9f70968c4`. Exact baseline digests, both
compiler commands and all raw inputs/outputs are in the capsule.

Each full-system suite has its first adjacent AB/BA campaign and one allowed
unchanged diagnostic repeat after the first result was inconclusive. One
algorithm thread, automatically leased CPUs, default degree scheduling,
grevlex, primes 32003 and 2147483647. Every complete reduced-basis output and
algorithm/resource counter agrees in all 120 pairs (240 processes), without
failures or timeouts. Every completed sample and outlier remains; campaigns
are separate and no further unchanged repeat is used.

| Campaign | Suite | Pairs | Candidate GM B/A | Median | Range | Process GM B/A |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| first | small | 32 | 1.0315 | 1.0204 | 0.9767–1.2093 | 0.9898 |
| first | medium | 28 | 1.0035 | 0.9995 | 0.9593–1.0679 | 0.9907 |
| repeat | small | 32 | 1.0627 | 1.0361 | 0.1273–15.5108 | 1.0463 |
| repeat | medium | 28 | 0.9520 | 0.9996 | 0.3053–1.1497 | 0.9888 |

The repeat has large outliers in both directions, including a 15.51× small
candidate ratio and a 0.305× medium ratio. Medians remain near one. These
observations do not establish a broad F4 improvement or the cause of the
variation. The unaffected prime-32003 cases remain as controls in the data.
Candidate and process times are separate; certificate generation, independent
verification and kernel checking are excluded.

Direct Cauchy31 comparisons use fresh benchmark executables for both sources,
prepared inputs outside timing, all decoded output entries consumed, one
algorithm thread and automatic CPU lease. Each operation has one whole-sweep
AB/BA campaign at 64/128/256/512, one trial per sweep, 32 completed points total.
All complete output hashes agree. Full repeats, RSS, floor flags, host activity
and normalized-slope fits remain in the exports.

| Kernel | Size | Block 0 B/A | Block 1 B/A |
| --- | ---: | ---: | ---: |
| cauchy31 | 64 | 0.9973 | 0.9925 |
| cauchy31 | 128 | 1.0011 | 1.0047 |
| cauchy31 | 256 | 1.0077 | 1.0096 |
| cauchy31 | 512 | 0.9891 | 0.9897 |
| cauchy31Strided | 64 | 0.9604 | 0.9867 |
| cauchy31Strided | 128 | 0.9515 | 0.9543 |
| cauchy31Strided | 256 | 0.9211 | 0.9217 |
| cauchy31Strided | 512 | 0.8999 | 0.8883 |

The 512-row strided case improves about 10–11% in both blocks; the contiguous
control stays around one. This supports the specialized kernel, with the
full-system limits above. All nine checks and eight Clang/GCC ASan/UBSan
variants pass. Independent scalar-modulo and generic-Montgomery tests cover
boundary factors/coefficients and strides 1/2/7, with a positive fold-path count
for each stride. Guard pages, malformed prefixes and native/portable complete
F4 comparisons remain covered. ASan is limited by mimalloc; leaks are disabled.

[Raw capsule](raw/matrix-m31-strided-bd103dc595b5.tar.gz), SHA256
`b6a6a4277a28f60a58d9c8432d34dc168677d20109616e1ea71caf7fa98e3c5b`; 158 baseline and 158 candidate source
blobs, 1238 verified payload digests. No fastest-open-source milestone
or external performance leadership is demonstrated.
