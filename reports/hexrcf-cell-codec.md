# Complete-cell serialization composition

[`CellCodec.read_of_descriptors`](../adapters/HexRCF/RealCoefficients/CellCodec.lean) composes finite coefficient/context coverage of
all supplied section, boundary and point sign rows with the strict ordered
complete-cell parser. It derives the actual exact returned `Evidence`, retaining
all row data, original guard preflight, sector points and dependent indices.
The point descriptors' independent restoration equations remain explicit
premises. This helper does not establish those owner equations, construct a
predecessor fact inventory or prove general frontend acceptance/completeness.

`SectorEncode.read_of_descriptor` proves the six-field sector composition for
both exterior rays, interior sectors and the empty-root whole line. It reuses
`RowEncode.read_covered` and the owner's finite graph/selected-sign laws. It
copies no graph validation or root-selection proof.

`CellEncode.packet` contains the existing complete-cell serializer, independently
of `CellBuild`, `RootBuild` and `CellDiscover`. Native `CellBuild.packet` delegates
to it with the native context codec. `CellCodec.packet_eq` proves that changing
only a decoder leaves every packet unchanged when the encoding functions agree.
This condition matters: a codec that round-trips its own encoding need not read
a different producer's encoding. Arbitrary producer hashing remains explicit.
The exact layout is also checked against the existing frozen algebraic fixture.

The fresh `CellCodecProofs` target rechecks all six actual theorem bodies with
only the standard three axioms, requires the actual finite owner row laws, and
checks that the quotation-side imports exclude the three adapter producer
modules. It does not claim all owner producer definitions are absent from the
import closure.

The remaining owner prerequisite is the exact finite-covered descriptor
round trip recorded at #10378 comment 6189246677. Native globally-lawful codec
reconstruction with different hashing is not substituted for that statement.
Full #10358 completion additionally retains frozen source/provider/context/
reached-data assembly, all-live transport, automatic common-field certification,
strict missing-record compiled replay and the remaining realization obligations.

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
integration does not discharge the descriptor-restoration premise or the
remaining full extension requirements.
