# BKR tables over nested infinitesimal coefficient fields

The input fields iterate the existing canonical RationalFn field over the
rationals, with the existing positive-infinitesimal sign operation. The
registrations fix the extension depth at one or two. Within each
field, the query-count schedule is 8, 16, 32, 64 and 128.

The polynomial is P=X on the whole line, and every query is the constant
newest infinitesimal. There is exactly one root, zero, and its complete sign
pattern is all positive, with count one. The input validator checks the
actual recursively encoded polynomial and every query against this
elementary independent oracle. It does not reuse a Tarski query or matrix
algorithm. These cases complement the more complicated nested-field
conformance examples and the separate coefficient-sign measurements.

Production calls the actual buildPrepared operation. Tree replay checks its
supplied evidence using the ordinary coefficient arithmetic and signs.
Field construction, domain preparation, the input's retained reference tree,
graph construction and full input fingerprints happen outside timing.
The producer includes its own certificate checking. These timings are
overlapping operations and must not be summed as disjoint components.
Inspection also checks the actual graph; no graph timing model is claimed.

For each fixed depth, polynomial degrees, coefficient representations and
matrix dimensions are bounded independently of the query count s. Leaves
have three moment rows and every parent retains one row and one sign column.
The tree has 2s−1 nodes and 4s−1 moment slots. Its balanced arity volume is
s(log₂s+1); the actual construction and replay scan length-k query, sign and
exponent lists at a node. Inspection counts the query-reduction steps actually stored at every node:
s(log₂s+1). Replay also checks 4s−1 moment certificates and s leaf domains;
production adds s initial query normalizations. These linear terms can have
large constants. The asymptotic model is s(log₂s+1), but the range 8..128
may give an inconclusive verdict if it does not separate the two terms.
The harness fits per-parameter medians after dropping the first parameter,
so the fitted range is 16..128. No exponent or linear coefficient is fitted.
Depth-dependent arithmetic costs are fixed within each registration.
The measurements make no fitted exponential claim across depths.

Normalization changes the constant infinitesimal query to operand 1 and
stores the infinitesimal in its scale witness. The Tarski moments therefore
use 1 and X; infinitesimal arithmetic occurs in normalization and replay of
the query-reduction witnesses. At depth two, the lower-level coefficients
are only 0 and 1. These examples measure two layers of field arithmetic,
not interactions between infinitesimals from different levels. Field
operations use stored instance dictionaries, so absolute times need not
match a caller with specialized concrete coefficient types.

Run:

    lake build hexsigndet_bench
    .lake/build/bin/hexsigndet_bench inspect-nested-tables-small
    python3 scripts/bench/sign_det_nested_tables.py --output /path/to/new-captures

The collector uses one automatically leased CPU, six trial-major rounds
per registration, the shared 100 ms repeat target and a 300-second
operational child cap. It retains all scheduled outputs before judging
them, including inconclusive results or invalid points. Clean source,
binary, harness, input/result fingerprints and host context are recorded.
The timed producer mixes its table hash with the prepared input fingerprint;
successful replay returns that fingerprint. Both results distinguish the
field depth and supplied input. These fingerprints are reproducibility
checks, not independent mathematical proofs.
Its output must be outside the source checkout.

These supplied same-level graphs do not represent coefficient-sign proof
DAGs across field levels. That logical interface has separate kernel
examples. The native fields in this family use ordinary coefficient
arithmetic, without tower implementations or additional field instances.
This registration alone claims no timing result, allocation measurement
or Phase-4 completion.
