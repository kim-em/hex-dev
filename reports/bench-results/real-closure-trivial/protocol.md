# Rational complete-root route comparison

Compare `Trivial.Rational.roots` after conversion with the existing
`RealAlgebraicPoly.roots` backend on identical rational inputs. The generic arm
includes generic complete isolation and canonical conversion of each returned
selected descriptor. The canonical arm calls the existing complete backend.
This measures the generic route permitted by the SPEC; it introduces no new
trivial-base algorithm or fast path.

Inputs are zero, the nonzero constant 5, and `(X² - 2)^m` for
`m = 1,2,4,8`. Prepare both coefficient representations before timing. Each
call retrieves its input through an `IO.Ref`, constructs the complete result,
and forces the common exact consumer. Zero must return `all`; the nonzero
constant returns an empty finite set. The repeated-factor cases must return
the two ordered roots `-sqrt(2), sqrt(2)`, both with exact multiplicity `m`.
The consumer checks their signs and exact square identities. Input preparation,
canonical coefficient lifting, executable startup, one configured warmup,
functional printing and exact FLINT checking are outside timing.

Register six trial-major rounds. In each round visit the six inputs in the
order above, with adjacent generic/canonical arms. Alternate AB/BA between
rounds. Use the pinned lean-bench fixed-call harness with
`--repeats 1 --min-total-seconds 0.5`. Retain all 72 arm exports, complete batches,
repeat counts and any failures. Do not discard host-active samples, wait for a
quiet CPU or retry automatically. At most one unchanged rerun is permitted
if the completed comparison is inconclusive. Per-call and process timeouts are
operational safeguards: 120 and 3600 seconds respectively.

Lease one CPU using the shared selector and record host activity as context.
Freeze source and protocol, verify the clean pinned lean-bench package, record
compiler/executable identities and capture fresh twelve-arm functional output.
Require exact agreement with the committed fixture and independent FLINT checks
before timing. Require unchanged source at the end.

Report all six paired batch per-call estimates, medians, full ranges and paired
generic/canonical ratios. No significance test or asymptotic model is inferred
from this finite family. The growing repeated-factor degree primarily exercises
Yun decomposition while the two distinct roots remain fixed; it does not measure
all squarefree-root, selected algebraic coefficient or arbitrary tower families.
