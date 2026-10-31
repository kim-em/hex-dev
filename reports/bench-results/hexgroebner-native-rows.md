# Bounded native sparse row updates

Source fingerprint `1c423e2b8a95` compares scalar Lean row loops (A) with bounded
native row updates (B) in the same executable. Field, inputs, ordering,
allowances, matrix construction, pivot selection and output contracts are
identical. Both routes retain the existing native wide-word arithmetic
foundation. The native route replaces only sparse updates of the packed dense
accumulator; each foreign call handles at most 4096 entries.

Measurements use Lean `v4.35.0-rc3` on shared host `chungus2`, with one
computational thread pinned to automatically leased CPU 26. The protocol is
adjacent AB followed by BA, retaining every completed sample. The
[metadata and exact script](hexgroebner-native-rows-1c423e2b8a95.measurement.json)
record compiler/binary identity, commands, affinity and load. The
[source manifest](hexgroebner-native-rows-1c423e2b8a95.manifest) identifies the
measured implementation. The [analysis](hexgroebner-native-rows-1c423e2b8a95.analysis.json)
records every paired ratio. The twelve matching `-b{0,1}-{cauchy,sparse,cyclic6}-{A,B}.json`
and `.log` files retain all samples, memory, variability, floor flags and
verdicts. All 44 scheduled measurements complete successfully. Every matrix
and complete basis hash agrees between routes.

## Dense matrices

The full-rank Hilbert family over p = 65,537 has exactly `(n³−n)/3` sparse
entry updates. Validation, scans, decoding and output hashing add quadratic
work. Input preparation is excluded; all those other operations and workspace
allocation are included. Both routes use a nonbinding one-billion-unit work
allowance. Cauchy registrations also admit n = 1024; this paired observation
uses the declared doubling subdomain n = 64 through 512.

| n | AB medians A → B | BA medians A → B | Paired geometric mean B/A |
| ---: | ---: | ---: | ---: |
| 64 | 1.576 → 1.096 ms | 1.587 → 1.089 ms | 0.691 |
| 128 | 10.263 → 6.598 ms | 10.298 → 6.567 ms | 0.640 |
| 256 | 73.720 → 43.776 ms | 73.761 → 43.783 ms | 0.594 |
| 512 | 558.735 → 318.521 ms | 559.485 → 318.422 ms | 0.570 |

The largest case shows about 43% less whole-call time. Dividing by its
44,739,072 entry updates gives approximately 12.5 ns per update for A and
7.1 ns for B. These are whole-call quotients, not isolated instruction timings.

Both cubic timing verdicts remain **inconclusive**: normalized slopes are
−0.175/−0.177 for A and −0.272/−0.269 for B. The source still performs the
stated cubic number of updates, with quadratic ancillary work. The relative
timing contributions have not been separately fitted, so these observations
do not establish the asymptotic timing law. The output includes all below-floor
and warmup flags; no sample is removed because of host activity.

## Sparse matrices and full F4

The clustered sparse family has `256*n` columns, `2*n` rows and six nonzeros
per row, over the same field. Known reducer pivots install directly; dependent
targets cancel in one update. Workspace initialization and scanning remain
scalar Lean operations. Both source work and the timing verdict are linear
over n = 32,64,128,256; slopes range from −0.031 to −0.026 across the arms.
Paired B/A ratios are 0.981, 0.985, 0.991 and 0.988 respectively. The observed
effect is small, about 1–2%, on this family.

Cyclic-6 uses six variables, p = 65,537 and grevlex with the written variable
precedence. Each arm retains three repetitions with a 0.5-second inner floor.
Input generation is excluded. Canonicalization through final interreduction,
interchange decoding and complete structural hashing are included. Output
remains an **unchecked candidate**; certificate generation, independent native
verification and kernel checking are absent.

| Call | AB medians A → B | BA medians A → B | Paired geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-6 | 109.436 → 102.700 ms | 108.673 → 103.198 ms | 0.944 |

The approximately 6% whole-system reduction is much smaller than the dense
kernel improvement. Monomial operations, symbolic preprocessing, pair handling
and matrix setup remain substantial work. This measurement supports retaining
the useful native kernel while continuing algorithm and representation work.
It establishes no fastest-open-source milestone or language barrier.

A separate [diagnostic sampling profile](hexgroebner-native-rows-1c423e2b8a95.profile.txt)
with [capture metadata](hexgroebner-native-rows-1c423e2b8a95.profile.json)
attributes about 4.1% of sampled cycles to the native update. Reducer-trie
lookup and divisor enumeration together account for about 13.1%; monomial
interning/product loops and allocation/reference-count work account for much
more. These samples identify optimization targets; they are excluded from
the paired timing comparison.

## Native contract validation

The C provider reads explicit little-endian 1/2/4-byte residues and u32 column
indices. It checks geometry, slices, selected indices and canonical residues,
uses copy-on-write for shared storage, and preserves original borrowed buffers
when they alias the dense input. Products are below 2^62. The uint128 Barrett
path and exact-remainder fallback agree with the structurally recursive Lean
specification. No floating point or CPU extension is required.

Conformance includes 630 generated primitive cases across nine boundary
moduli, both ownership paths, explicit aliases, malformed slices, and the
inclusive 4096-entry bound. A 5000-entry matrix pivot spans multiple native
calls. All 175 matrix fixtures match the scalar route including pivots,
provenance and counters. All 567 F4 systems match the scalar route including
complete bases and cumulative counters, and still agree with Singular and
SymPy F5B. A downstream literal row update reduces in the ordinary Lean kernel
and depends on no axioms.

`bash scripts/ci/check_groebner_rows.sh` checks 4500 C cases and malformed
boundaries for each compiled arithmetic path. The same checks pass with
`HEX_GROEBNER_SANITIZE=1` under address and undefined-behavior sanitizers. This
helper extends the existing conformance runner; no additional CI job is added.
