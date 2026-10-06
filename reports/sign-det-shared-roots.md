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
explicit factors, checks their gcd and common polynomial, and checks the
selected intervals and orders against the known factor roots. It does not
reuse the BKR, query or root-isolation algorithms. Native inspection and all
three fixed benchmark correctness checks pass.

Four joint evidence trees are returned by each example. Their moment counts
are 43/40/43/34, 55/51/55/44 and 75/71/75/63; maximum matrix widths are
9/9/9/6, 12/12/12/8 and 16/16/16/16 respectively. These are inspected
certificate dimensions, not independent complexity bounds. The two
CommonProduct.build calls perform two polynomial gcd computations. This
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
examples are usable direct API demonstrations on this host; they imply no
bound for arbitrary degrees, nested fields, quantifier elimination or `rcf`.

The measured source is base 97d1f24d02 plus the retained patch at
5b46a2db3b. Metadata supplies full revisions and exact file bindings so
squash merging does not lose reproducibility. This snapshot precedes the
polynomial-power correction in PR #10810. Its times are baseline observations,
not measurements of that correction or claims about its eventual speedup.

Stored witness bits and peak intermediate bits have their separate evidence
requirements. This collection supplies common-root comparison coverage and
bounded time/resident-memory context; it does not claim to complete every
sign-determination performance obligation.
