# Matrix primitives with a fully portable disabled route

The existing F4 matrix loop uses bounded validation and zero-buffer primitives
when native rows are enabled. Disabling native rows uses the original Lean
validation and allocation models as well as scalar row operations. Neither
route selects the separate matrix continuation.

This first corrected-source campaign binds source fingerprint `16c437c35eac`,
commit `99dcd85b6d7b8b23d1ba89f2e3aabcc2b4ea72d6`, snapshot
`248db728dffaea2fad9e39a83751dff996415228`.
Compute SHA256: `9ac8cfb740dfa1c07fbbee47a86e2c64692b3fdebfc3c9a445ae22afa360c3be`;
reference SHA256: `93b93b8dd241c6bf7b038c9bc3abef646e72de5abc6f91c23003b268b3ee3902`.
The unchanged baseline is fingerprint `bf218f1c520b`, compute SHA256
`0ff6b19199681cf4d6f375992b665c338a391b5f8ef95d4771c2f76d735bfe34`.
Exact baseline sources are in the [original capsule](raw/matrix-primitives-e096f91a0bf1.tar.gz).

Each suite has one adjacent AB/BA campaign (block 0 AB, block 1 BA), with one
algorithm thread, an automatically leased CPU on the shared EPYC 9455 host,
grevlex, primes 32003 and 2147483647, and default scheduling. All 60 pairs
(120 processes) have equal complete reduced bases and every algorithm/resource
counter. No failures, timeouts, sample filtering or unchanged repeat. These
observations are separate from earlier source campaigns and are not pooled.

| Suite | Pairs | Candidate GM B/A | Median | Range | Process GM B/A | Family-balanced process GM |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 32 | 0.9724 | 0.9804 | 0.7831–1.0260 | 0.9592 | 0.9586 |
| medium | 28 | 0.9635 | 0.9644 | 0.9265–1.0169 | 0.9611 | 0.9611 |

Candidate time covers candidate production. Process wall time includes startup,
parsing and output. Certificate generation, independent certification and kernel
checking are separate and are not timed here. Complete outputs, every completed
sample, process RSS, variability, CPU leases, host activity and build context
remain in the capsule. Small-suite CPU 51 loads are 3.49/2.58/3.53 at start
and end; medium-suite CPU 48 loads are 3.49/2.58/3.53 → 2.94/2.51/3.49.
These modest local effects do not demonstrate external
leadership or identify the remaining bottleneck. The fastest-open-source
milestone remains open.

This source predates the expanded independent-limit tests, runtime integration
counter checks, admission diagnostics and short-row benchmark registration.
Those changes have [separate validation](hexgroebner-matrix-primitives-validation.md).
A fresh driver build is byte-identical to this measured source; the new kernel
benchmark executable has separate timing evidence.

[Raw capsule](raw/matrix-primitives-portable-16c437c35eac.tar.gz), SHA256
`0344e56ba8b9873e70c17f993e9f8962958169ecee3c8c148c40f3ae043dd231`;
158 verified Git source blobs and 591 verified payload digests.
