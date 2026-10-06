# Small comparisons with a common irrational root

The fixed examples use P=X²−2 and Q=P(X−3)…(X−(n+2)) for n=1,2,3.
The open interval (0,2) selects sqrt(2) in both defining polynomials.
A half-integer interval around n+2 selects Q's largest integer root.
Each callback constructs all three descriptors and runs both actual
cross-polynomial comparisons: equality of the two descriptions of sqrt(2),
and strict ordering of sqrt(2) before the integer root.

These operations build their common products, remove the common factor P,
construct the joint sign tables and check the re-encodings. The source
intervals are finite and the common comparison domain is the whole line.
The coefficient operations are ordinary rational arithmetic; no Mathlib
proof package is required by the executable.

## Independent checks and measured work

The FLINT inventory validator reconstructs both input polynomials from their
explicit factors and checks their gcd and common polynomial using exact
rational arithmetic. The interval and order fields in the archived inventory
are expected literals, not independently observed descriptor fields. The
validator checks those literals for consistency; it does not independently
verify root isolation or ordering. The explicit factors give a direct
mathematical check: (0,2) contains only sqrt(2), and the half-integer interval
around n+2 contains only that integer root. Lean inspection requires the
actual comparisons to return equality and strict ordering, and all three
fixed benchmark correctness checks pass.

Four joint evidence trees are returned by each example. Their moment counts
are 43/40/43/34, 55/51/55/44 and 75/71/75/63; maximum matrix widths are
9/9/9/6, 12/12/12/8 and 16/16/16/16 respectively. These are inspected
certificate dimensions, not independent complexity bounds. The two
CommonProduct.build calls perform two polynomial gcd computations. This
same gcd is computed twice, and the left re-encoding is repeated. The four
trees therefore do not represent four independent inputs. The call count
comes from the source, not an independent instrumented counter. This
count concerns those constructors only: it does not count domain preparation,
coefficient-level gcds in rational normalization or allocation traffic.

The fixed callbacks use noinline and never_extract on the case constructor,
descriptor selection and wrappers. Generated compiler output was inspected
to confirm each wrapper calls the computation inside the measured loop,
instead of reading a cached closed result. No generated C was edited.

## Running time and resident memory

The [retained archive](data/sign-det-shared-roots/5b46a2db3b) contains all
18 successful observations, six trial-major rounds through the three cases.
Each child uses the existing fixed lean-bench runner with a 100 ms tuning
target. The collector, raw stdout/stderr, independent oracle result, exact
callback digests, source and binary hashes, source reconstruction patch,
harness revision, automatically leased CPU and host load are retained.
There is no asymptotic timing model, fitted exponent or unchanged rerun.

| Degree of Q | Median time (ms) | Minimum–maximum (ms) | Median whole-child peak RSS (MiB) |
| --- | ---: | ---: | ---: |
| 3 | 22.03 | 19.97–22.58 | 72.34 |
| 4 | 43.26 | 42.18–45.76 | 72.49 |
| 5 | 109.01 | 106.46–114.09 | 72.70 |

Time includes the actual descriptor validation and both comparisons.
Whole-child resident peaks additionally include startup and harness tuning;
they do not measure peak live heap or isolate callback memory. These small
examples have the observed running times on this host; they imply no
bound for arbitrary degrees, nested fields, quantifier elimination or `rcf`.

The measured source is base 97d1f24d02 plus the retained patch at
5b46a2db3b. Metadata supplies full revisions and exact file bindings so
squash merging does not lose reproducibility. This snapshot precedes the
polynomial-power correction in [PR #10810](https://github.com/kim-em/hex-dev/pull/10810). Its times are baseline observations,
not measurements of that correction or claims about its eventual speedup.

These examples have P dividing Q, so the common polynomial is Q itself.
They do not cover a common polynomial strictly larger than both inputs or
a common factor proper in both. Such comparisons remain a separate coverage
requirement.

Stored witness bits and peak intermediate bits have their separate evidence
requirements. This collection supplies common-root comparison coverage and
bounded time/resident-memory context; it does not claim to complete every
sign-determination performance obligation.
