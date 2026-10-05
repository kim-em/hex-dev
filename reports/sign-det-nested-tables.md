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
finite timing test does not distinguish the linear terms from the logarithmic factor.
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
Only the fixed query-count ladder changes to 128, 256, 512, 1024 and 2048.
On the fitted range 256..2048, pure linear cost has expected residual slope
about −0.138, s log s has slope zero, and s log² s has slope about +0.138.
All three fall within the unchanged acceptance interval |β| ≤ 0.15.
A consistent verdict therefore shows finite-range consistency with the
model; it neither confirms nor separates its logarithmic factor. The
source-derived operation count supplies the reason for that factor.
Neither an exponent nor a linear coefficient is fitted.

The earlier ladder was 8, 16, 32, 64 and 128, fitted at 16..128. Both complete
120-point collections used revision
39066b34e16620946959796b86d60c4af5b29e29. Their retained archives are supplied
by [PR #10785](https://github.com/kim-em/hex-dev/pull/10785) under
reports/data/sign-det-nested-tables/39066b34e1/first and unchanged-rerun.
The first/rerun residual slopes were −0.179223/−0.176575 for depth-one
production, −0.147045/−0.145991 for depth-one tree replay,
−0.178336/−0.181258 for depth-two production, and
−0.161606/−0.156667 for depth-two tree replay. Only depth-one tree replay
was consistent; the other three were inconclusive. All slopes were negative,
indicating growth slower than the model on that range. No observation is
discarded or relabeled. Historical validators accept that exact earlier
ladder only when it is explicitly requested.

The 300-second cap includes setup inside each child, as well as the timed
callback. Setup produces the reference certificate, checks tree and graph,
and computes their hashes. For planning only, the earlier depth-two
production median of 2597.92124 ms at 128 queries scales to about 62 seconds
at 2048 under the declared model. A production child also pays for setup:
approximately two productions plus two replays in total, rather than one
62-second operation. Once a callback takes at least 50 ms the harness uses
one timed call. Inspection records the elapsed setup-plus-callback work for
every depth and query count on stderr before scientific timing starts;
those records establish the actual operational margin under the cap.
The complete depth-two inspection at 2048 queries took 154.461 seconds
on the shared host: setup, production, tree replay and graph replay together.
This is an operational preflight observation, not a scientific timing point;
it is retained in nested-wide-review-fixes-inputs.stderr alongside the other
nine sizes under ~/.local/state/hex/issue-10377-session-progress/.
A cap hit is retained and reported as an invalid observation, not a
consistent or inconclusive scaling result. No quiet-host preflight or
retry-until-clean loop is used. Finite-range consistency cannot prove an
asymptotic bound.
