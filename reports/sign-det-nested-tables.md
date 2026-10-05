# BKR tables over nested infinitesimal coefficient fields

The input fields iterate the existing canonical RationalFn field over the
rationals, with the existing positive-infinitesimal sign operation. The
registrations fix the extension depth at one or two. Within each
field, the query-count schedule is 128, 256, 512, 1024 and 2048.

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
exponent lists at a node. Inspection counts the query-reduction steps
actually stored at every node: s(log₂s+1). Replay checks 4s−1 moment certificates. The s leaves each
replay their domain once under the current domain-cache policy; parent
moments also replay their domains. Production adds s initial query
normalizations, 4s−1 bounded-size moment-chain constructions, 2s−1 rank
certificates, s leaf inversions and s−1 scaled solves. These linear terms
can have large constants. The asymptotic model is s(log₂s+1), but the
fitted range 256..2048 may give an inconclusive verdict if it does not separate the two terms.
The harness fits per-parameter medians after dropping the first parameter,
so the fitted range is 256..2048. The model has no free exponent or linear
coefficient; the harness fits only the slope of time divided by that model.
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
The collector's output must be outside the source checkout.
The regression fixture is a compiled inventory snapshot, rather than a
freshness test against the current binary. Scientific collection always
regenerates and validates its own live inventories.

These supplied same-level graphs do not represent coefficient-sign proof
DAGs across field levels. That logical interface has separate kernel
examples. The native fields in this family use ordinary coefficient
arithmetic, without tower implementations or additional field instances.
This registration alone claims no timing result, allocation measurement
or Phase-4 completion.


The larger range retains the same source-derived s(log₂s+1) model, six
trial-major rounds, 100 ms target, 300-second operational cap and slope rule.
Only the fixed query-count ladder changes to 128,256,512,1024,2048. The complete
first range and its sole unchanged rerun remain source-bound evidence; their
inconclusive results are not discarded or relabeled. Historical validators
accept that exact earlier ladder only when it is explicitly requested.

The source has large linear terms from normalization and bounded-size
certificate, domain and matrix work, in addition to query-reduction replay at
every balanced node. A larger s range tests the declared model with those
terms still present; neither exponent nor a linear coefficient is fitted.
The 300-second cap is an operational limit, not a performance threshold.
For planning only, the earlier depth-two production median of about 2.6 seconds
at 128 queries scales to about 62 seconds at 2048 under the declared model.
Preparation and the multiple calls used by the harness add wall-clock work;
the complete collection may take tens of minutes. The actual recorded results
and cap outcomes determine acceptance. No quiet-host preflight or retry-until-
clean loop is used. Finite-range consistency cannot prove an asymptotic bound.
