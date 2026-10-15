# Complete-cell serialization composition

[`CellFootprint.read_packet`](../adapters/HexRCF/RealCoefficients/CellFootprint.lean)
proves exact full cell-payload restoration from finite coverage of its stored
coefficient inventory and validity of the original guards. Point-descriptor
restoration is derived from the actual owner laws; it is not an additional
success premise. The result retains every section/sector row, ordinary point
and dependent index.

[`RootCodec.read_covered`](../adapters/HexRCF/RealCoefficients/RootCodec.lean)
restores the exact raw descriptor and evidence under finite head/endpoint/graph
coverage, retaining arbitrary producer hashing. It composes the owner's
`Codec.bindings_of_check`, `Codec.Shape.of_validate`, graph replay/encoding laws,
finite graph reader and public descriptor constructors. The checked-node binding
law is supplied by merged PR #10936 at
`db46b363438e1b22c4487770298e60447074579c`. No private node-binding proof is
copied into the adapter, and the reader runs no root/sign producer.

`SectorEncode.read_of_descriptor` and `CellCodec.read_of_descriptors` retain the
lower-level conditional composition interfaces. `CellFootprint` derives their
row/point coverage from one finite payload inventory and uses the actual
`Signature.codec_lawful` for context literals. Every stored graph entry is
included, even when unreachable, with duplicates retained. This inventory does
not collect all intermediate arithmetic requests or separately authenticate
source/provider histories.

`CellEncode.packet` contains the existing complete-cell serializer, independently
of `CellBuild`, `RootBuild` and `CellDiscover`. Native `CellBuild.packet` delegates
to it with the native context codec. `CellCodec.packet_eq` requires identical
encoders before changing decoders: coverage of a reader's own encoding does not
justify decoding different native bytes. `CellBuild.packet_read` composes that
identity with finite payload coverage. The frozen algebraic fixture remains
byte-identical.

`CellDiscover.run_replay` binds literal acceptance to the actual public native
producer, retaining both original shared-sentence verdicts. It uses the returned
native context's proved codec law. This does not reconstruct a general frozen
predecessor history through a partial codec or prove strict compiled replay
with arbitrary missing intermediate scalar records.

The fresh `CellCodecProofs` target checks thirteen actual serialization proof
bodies using only the standard three axioms. It requires the actual new owner
binding/finite-reader laws and excludes the adapter's three producer modules
from imports. `CellExecutionProofs` additionally audits the actual native
producer/restoration bridge. These exclusions do not claim all owner producer
definitions are absent from the imported environment.

The finite-covered descriptor question at #10378 comment 6189246677 is addressed
by this composition. Full #10358 completion still needs general frozen
source/provider/context/reached-data assembly, all-live transport, automatic
common-field certification, strict missing-record compiled replay, general
frontend acceptance/completeness and the remaining realization obligations.

## Source-scoped validation records

The [validation record](data/hexrcf-cell-codec/context.json) binds 19 source
files to implementation `d6c9b6df2b73167d7376328f067626abe3b4d113` and retains
26 raw build/check logs, including earlier proof attempts and the incorrect
combined unittest invocation. The corrected test invocations pass 11 + 11
checks. DAG/umbrella, copyright, literal matching and whitespace checks pass;
the admission scanner covers 635 cones and 1,535 local modules.

The six-target audit/regression build passes 10,970 jobs, including the six
new actual proof bodies and 50 retained construction/discovery/source audit
bodies. It peaks at 1.7 GiB with no swap. The selected optional-library,
quotation, discovery, requested-cell and affected-manual build passes 11,762
jobs, peaking at 2 GiB with no swap. The former takes 39.503 seconds and the
latter 53.535 seconds on the shared host with existing cached dependencies.
These are incremental operational observations, not a speedup or scaling
measurement. Every own build uses the aggregate 32 GiB/no-swap/two-thread
cgroup and runs serially. The existing manual's displayed text and styles are
unchanged, so no new rendering result is claimed.

## Current-main integration

The [integration record](data/hexrcf-cell-codec/current-main-context.json)
binds 26 source files and seven successful raw logs to
`01baf033cd6edcf3288e324cb735525fc1326564`. This tree includes main
`c7bd7e9047` and the issue branch at `b1dc2e1d8c`; the owner codec signatures
and their affected correspondence modules were rebuilt. The selected optional
adapter/conformance/manual build passes 11,768 jobs, including all six new
actual parser proof bodies, 50 retained audit entries, exact frozen-fixture
byte equality, original selected-field/guard tests, discovery/requested-cell
regressions, both fresh quotation modules and the importing manual chapter.
It takes 19 minutes 5.042 seconds and peaks at 17.1 GiB with zero swap under
the same aggregate 32 GiB/two-thread limit. This is an integration observation
with rebuilt dependencies, not a timing comparison with the earlier cached
builds.

DAG/umbrella, copyright, selected-literal matching and whitespace checks pass.
The admission scan covers 635 cones and 1,535 modules, and both checker suites
pass 11 tests. The displayed manual text and styles are unchanged. This
integration record predates the owner binding export and its consuming proofs;
the record alone does not discharge the remaining full extension requirements.

## Finite payload inventory

[`CellFootprint`](../adapters/HexRCF/RealCoefficients/CellFootprint.lean)
collects every serialized coefficient and full context from sections, boundary
rows, point descriptors and point rows. The traversal retains duplicates and
all stored graph entries, including unreachable entries. It performs no
coefficient arithmetic. The inventory excludes separately authenticated source
guards and does not claim to collect every intermediate arithmetic request.

`CellFootprint.read_covered` replaces the separate row and point coverage
premises with coverage of this one finite coefficient list. Context roundtrips
come from the actual owner's `Signature.codec_lawful`. Original guard validity
and point-descriptor restoration remain explicit in that conditional helper;
`read_packet` separately derives descriptor restoration through the owner laws. The generic `covered` and `descriptor_covered` laws retain
all individual components for subsequent owner integration.

The native regression decodes the existing complete algebraic matrix through
a reader restricted to exactly the collected coefficient literals. It retains
the original verdict and fixture bytes. Removing every stored zero literal
rejects with the evidence error; an original zero divisor still rejects first,
even with a malformed payload and empty reader. These compiled controls do
not replace the generic ordinary-kernel proofs or establish strict replay of
arbitrary missing intermediate scalar records.

The [inventory record](data/hexrcf-cell-codec/footprint-context.json) binds the
source at `f1ca215b5912c71652a3662017069651ef708c38` and retains the initial
proof/syntax failures. Ten actual parser/inventory proof bodies pass the fresh
kernel audit with standard axioms and the producer-module import exclusions.
The selected 11,769-job affected build passes at a 2.6 GiB peak with zero swap;
the final API/library/manual build passes 11,761 jobs at a 992.3 MiB peak.
The earlier affected build preceded removal of the unnecessary context-codec
premise from `read_covered`; the final audit/library build covers that exact
source. Both reuse cached dependencies and do not establish a performance
comparison. DAG/umbrella, copyright, literal and whitespace checks pass; the
source admission scan covers 636 cones and 1,536 local modules. The earlier
22 checker unit tests retain their separate unchanged source scope.

## Restoration through the merged owner binding law

The [restoration record](data/hexrcf-cell-codec/owner-restoration-context.json)
binds 21 source files to `1f319907c2ff0e8faa208c28f23ec8a8d1481fd1`,
including the actual owner binding export and descriptor APIs. It retains ten
raw logs, including the initial namespace error and the corrected build.
The selected affected build passes 11,770 jobs after integrating owner main
`446b7f2991`. All thirteen serialization and twelve execution proof-body audits
are actually rebuilt; the other retained groups contribute 28 + 9 + 3 entries.
The exact old frozen fixture, finite restricted-decoder controls, original
selected-field/guard cases, discovery/requested-cell tests, two fresh quotation
modules and importing manual chapter pass. The build takes 12 minutes 40.361
seconds, peaking at 13.3 GiB with no swap under the unchanged aggregate cap.

DAG/umbrella, copyright, selected-literal and whitespace checks pass. The source
scan covers 637 cones and 1,537 local modules. These observations include
rebuilding affected owner imports and make no performance comparison with the
earlier cached builds. Displayed manual text/styles remain unchanged. The
record establishes stored-payload and native-context restoration under the
stated laws, not the remaining general history/arithmetic/frontend obligations.
