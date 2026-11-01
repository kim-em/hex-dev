# Compact monomial hash index on degree-scheduled F4

Monomial bucket heads and collision links use packed `UInt32` buffers with
stable identifiers. Power-of-two capacity grows before exceeding half load;
rebuilding visits identifiers deterministically and charges both work and peak
packed storage, including the old index. Hashes only filter candidates: complete
exponent equality decides identity. Exponent arenas keep their typed widths and
overflow-safe widening, and identifiers remain stable.

A bounded owned native operation combines preparation, exact lookup and
in-capacity insertion. This snapshot checks an arity ceiling of 2048, while
the 4096-unit work bound can force earlier fallback. Unsupported geometry, widening, rehashing, arithmetic/representation
bounds and insufficient allowances return the unchanged owned table. Portable
continuation starts after the native frame returns. Shared and aliased buffers
retain their original contents; compiled tests instrument actual exclusive
reuse, native insertion and hits inside F4. Portable-model theorems justify
the reference semantics, while native equality remains separately tested.

Measured source `78e8924c19cb`, computational commit `e83f46930c`, is frozen
by a fresh detached 272-job build. Its compute SHA256 is
`cb2269d67f3285dfc3902251975631e1fa988a10f05e20b73cdc1adb7273ab24`.
Baseline source `0cb80bf73a4a` has the same executable as earlier scheduling
source `6ede9cb261a4`, SHA256
`2ece3bf2646f90393331ce349043b8a19adb02d236ee1bf300337ceaf9e9bd67`.
Exact source blobs, manifests, build/initialization evidence, executable hashes,
helpers, inputs and complete outputs are retained. The native test registration
changes the source fingerprint from initial port `e6135b9c755a`; the two
snapshots are retained separately and are not pooled.

Each small/medium/fixed observation uses adjacent AB then BA, one algorithm
thread and one automatically leased CPU of the shared EPYC 9455 host. There
is one initial campaign per observation and no unchanged repeat. All completed
samples, outliers, failures and host context remain. The small suite has 16
inputs in seven families; the medium suite has 14, with the same seven families
at larger sizes. Both use grevlex and explicit fields 32003/2147483647.
They are fixed development corpora, not held-out or SPEC acceptance suites.

Candidate time includes canonical packing, F4 and final interreduction;
process time adds initialization, parsing, full output and identical GNU-time
wrappers. Peak child RSS is measured after exec. Certificate generation,
independent final certification and kernel replay are excluded. All 120 CLI
processes succeed, with 60 equal complete reduced-basis pairs and zero failures
or timeouts. Deterministic matrix/pair/round counters remain equal; work and
byte charges change to include the packed index explicitly.

| Observation | Candidate B/A | Median | Range | Process B/A | Equal-family process |
| --- | ---: | ---: | --- | ---: | ---: |
| small | 0.9787 | 0.9758 | 0.8491–1.0468 | 0.9830 | 0.9857 |
| medium | 0.9802 | 0.9707 | 0.9513–1.2376 | 0.9795 | 0.9795 |

The small/medium CPUs are 39/7. Peak child RSS for baseline/new is
42552/56360 KiB (small) and 97844/100740 KiB (medium). The source and generated
code change can affect runtime behavior beyond logical payload size; no
allocator-level cause is isolated by these observations.

| Family | Small candidate | Small process | Medium candidate | Medium process |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 0.9728 | 0.9641 | 0.9581 | 0.9593 |
| dense-quadratic | 0.9913 | 0.9918 | 0.9786 | 0.9821 |
| eco | 0.9728 | 0.9774 | 0.9704 | 0.9728 |
| kat | 0.9916 | 0.9986 | 0.9737 | 0.9766 |
| minrank | 0.9751 | 0.9983 | 1.0402 | 1.0061 |
| noon | 0.9886 | 0.9964 | 0.9771 | 0.9911 |
| reimer | 0.9651 | 0.9739 | 0.9656 | 0.9693 |

The registered fixed sweep retains 120 points, five declared repetitions per
case, normalizing actual inner repeats. All complete structural output hashes
agree. Its CPU86 placement and exact benchmark binary hashes are retained.

| Fixed case | B/A mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.9925 | 0.9922 | 0.9499–1.0188 |
| cyclic5 | 0.9724 | 0.9708 | 0.9618–0.9917 |
| cyclic6 | 0.9578 | 0.9580 | 0.9520–0.9655 |
| katsura3 | 0.9696 | 0.9769 | 0.9432–0.9961 |
| reimer5 | 0.9512 | 0.9494 | 0.9430–0.9689 |
| cyclic6Small | 0.9543 | 0.9588 | 0.9257–0.9670 |

The initial `e6135b9c755a` port has separate 64-process small and 56-process
medium campaigns, with candidate means 0.9803/0.9736 and all complete bases
agreeing. Its native harness registration and final validation are supplied by
the later snapshot; those earlier timings do not substitute for final-source
validation and are not pooled. Earlier packed-index experiments against older
F4 implementations remain distinct and are not used to claim this gain.

All existing conformance/theory/bench targets pass in a 2141-job build, then
additional packed-search, native-attempt and instrumented native checks pass.
Four Clang and four GCC ASan/UBSan variants retain the existing trie, packed
comparison, M31-vector and zero-scan tests while adding hash collisions, shared
buffers, aliases, malformed links, arbitrary-precision allowances and native
failure/fallback checks. Instrumented totals include 6808 accepted operations (including 1269 insertions)
and 5134 exclusive table reuses, with real F4 exercising all three.

Independent oracles pass for 175 matrix cases, 567 unique SymPy/Singular bases
and 1288 division cases. All 1134 degree/sugar profiles agree, both CLI
initialization profiles match exact complete output/counters, and all 32 bench
smoke checks pass. Phase, release, copyright and size audits pass. The dependency audit in this
snapshot fails because the new native carrier is missing from its allowlist;
its error is retained in the capsule. The combined implementation supplies
that registration and stronger ownership coverage. The capsule's generic audit
success summary is overbroad; the retained dependency error is authoritative.
The exact packed-byte regression changes from 114 to 190 bytes and the next
insertion from 140 to 220 because the index is now charged. The initial
outdated-byte assertion and fixture comparison failures are retained alongside
corrected checks. Of 1134 F4 fixture profiles, 1050 change only work,
serialWork and referenceWork; mathematical output, metadata and all other
counters remain equal. Division fixtures are identical.

This component observation does not measure combination with leading-column
target ordering. That combination requires its own validation and measurements.
The fastest-open-source milestone, finite-extension/parallel coverage,
probabilistic/trace support and remaining producer proofs remain required. No
compiler/runtime impossibility is established, and the issue stays open.

- [compact-current-e6135b9c755a.tar.gz](raw/compact-current-e6135b9c755a.tar.gz): `0e1082c1faa24b2a6c885cab34cde304abc2ff4104730aee24f72d5acd7dd574`.
- [compact-validated-78e8924c19cb.tar.gz](raw/compact-validated-78e8924c19cb.tar.gz): `61de3228c57ee63123864c874c4dd3ddd8c9125f1fcdd3a2f253b0993b8592d0`.
