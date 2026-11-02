# F4 CPU profiles

Diagnostic source fingerprint `1e1015abfc77`, snapshot
`8672bd465e0262b22a29f22c975c22d9cfe8aaa2`, compute SHA256 `9844bd85e3d231c6440de965fc611e62abe681f2b404372a6bd1dad67cdfbf82`.
The artifact digest is unchanged after profiling. Build identifiers may be
capsule-only identifiers; the referenced manifest retains exact source overlays.

User-cycle profiles use perf version 7.3.1, frequency 997 Hz, fixed grevlex
inputs at modulus 2147483647, default degree scheduling, one algorithm thread
and automatically leased CPU 32 on the shared host. Eco-11 runs four
processes, Cyclic-7 eight and Reimer-6 sixteen. All outputs and statuses remain.
The reports show zero lost samples. Profiles include process startup/output;
weights are diagnostic self-symbol percentages, not candidate latency estimates.
No host activity or completed sample is filtered and no profile is repeated.

| Input | Mersenne scan | Constructor field writes | Refcount slow path | Monomial hit |
| --- | ---: | ---: | ---: | ---: |
| eco11-31 | 31.28% | 4.24% | 5.29% | 4.19% |
| cyclic7-31 | 13.44% | 9.81% | 5.32% | 8.05% |
| reimer6-31 | 9.05% | 8.74% | 6.21% | 8.13% |

The scan is prominent, especially on Eco-11. Monomial processing, allocation,
constructor work and reference counting also matter; the profile does not
establish a single cause for the remaining external performance gap. Instruction
annotation motivated testing the existing Mersenne fold on strided vectors.
That experiment has [separate source-bound measurements](hexgroebner-matrix-m31-strided.md).

The capsule retains every symbolized sample stream, self-symbol reports,
instruction annotation, process outputs, CPU/host metadata and runner. Stack
memory bytes are not repository artifacts. Timing fields in profiled outputs
are retained but are not scientific timing evidence. Certificate generation,
independent verification and kernel checking are not measured.

[Profile capsule](raw/f4-cpu-profile-1e1015abfc77.tar.gz), SHA256
`8c9a50a89d74bfd9e47cfdd6da9674940d8f2abad7e50ca69c2b349fae52ef7f`; 75 verified payload digests. No external leadership claim
or fastest-open-source milestone follows from these profiles.
