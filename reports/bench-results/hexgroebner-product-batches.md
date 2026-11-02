# Batched existing monomial products

The bounded native operation looks up at most 64 products within 4096 total
charged exponent/link visits. Every product must already exist; misses, errors,
long chains and unsupported geometry defer the unchanged table to the scalar
operations. Only the final prepared workspace and result slice need fresh
storage. Polynomial multiplication retains the original scalar route when
`nativeMonomials := false`; other calls process bounded slices against the
remaining parent allowances. The original support allocation is reserved once.
`productsWith_spec` proves equality of the pure wrapper with its scalar model.
Native conformance checks the exact admission decision, complete table bytes,
shared aliases and failure-prefix work separately.

This measurement source precedes integration of the strided M31 optimization.
Baseline family fingerprint `1e1015abfc77`; candidate `cac2d00b46b7`,
commit `6a743306ac5389e9a7ee0021357841df90234795`, snapshot `41f1ecc91de1ea34f3e107ae836a5f770afa03f1`.
Compute/reference SHA256: `937caf8bf60b3bf4ec9ed4a37ad59826d991fe662d1c514788d4dff0d1e898a1` /
`f7283fcfd197ab62d53421905d2c6858e824966bbb0d60f1550d512a93645e56`. Build and snapshot identifiers may
be capsule-only identifiers after rebasing; exact source overlays and artifact
digests remain independently available.

The first adjacent AB/BA campaigns use one algorithm thread, automatically
leased CPUs, grevlex, degree scheduling and primes 32003 and 2147483647. All
60 complete reduced-basis and algorithm/resource-counter pairs agree, without
failures or timeouts. Every completed sample and outlier remains; no unchanged
repeat was collected. The means below weight each pair equally. These are
development-suite observations, not the SPEC's leadership acceptance suite.

| Suite | Pairs | Candidate GM B/A | Median | Range | Process GM B/A |
| --- | ---: | ---: | ---: | ---: | ---: |
| small | 32 | 0.8639 | 0.8570 | 0.5497–1.4859 | 0.9094 |
| medium | 28 | 0.8292 | 0.8178 | 0.7202–1.0237 | 0.8672 |

Candidate time includes normalization, F4 and final interreduction. Process
time also includes initialization, parsing and full output under identical
GNU-time wrappers. Certificate generation, independent verification and kernel
checking are excluded. The small-suite 1.486× regression remains in the result;
the medium suite includes a 1.024× regression. Host activity and all raw samples
remain recorded, without filtering or quiet-host selection.

The direct lookup comparison uses scalar per-term native lookup and batched
native lookup in the same fresh benchmark executable. Prepared tables contain
all requested products at fixed arity three, with ordinary hashes. Output
assembly, independent identifier validation, complete output support/final
workspace consumption, count and work are included. This benchmark does not
measure insertion. All output hashes agree across both AB/BA blocks.

| Products | Block 0 B/A | Block 1 B/A |
| ---: | ---: | ---: |
| 256 | 0.2192 | 0.2240 |
| 512 | 0.2244 | 0.2243 |
| 1024 | 0.2272 | 0.2267 |
| 2048 | 0.2299 | 0.2298 |
| 4096 | 0.2339 | 0.2361 |

All nine project checks and eight Clang 23.1.3 / GCC 16.2 ASan/UBSan variants
pass. An additional GCC AVX2 run with seed 1 covers the polynomial comparison
with ordinary hashes and different coefficients. ASan is limited by mimalloc;
leak checking is disabled. Each seed-0 variant confirms 4692 accepted batches
covering 11786 products in complete F4 computations; the public portable route
makes zero calls to this provider. The CLI comparison checks 1134 complete
corpus outputs/counters and input/resource boundaries for each executable.
Malformed geometry, arbitrary Nat metadata/allowances, exact collision handling,
width growth, shared workspace aliases and original scalar-loop allowance
prefixes remain covered. Kernel axiom audits contain no new axioms.

[Raw capsule](raw/product-batches-cac2d00b46b7.tar.gz), SHA256
`c521a9e752f4341e9a91886c5ee564b72684722306d1ebff6d50f122423bb7fd`; 158 baseline / 159 candidate family
source blobs, 153 verification source blobs and 1025 verified payload digests.
No fastest-open-source milestone or external leadership is demonstrated.
