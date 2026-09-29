# Joint Thom-query performance

This family compares the roots 1 and −1 of Xⁿ−1 and Xⁿ+1 for odd n. The
actual common head is −(X²ⁿ−1)/2. Each re-encoding has 3n+1 queries: the
2n target derivatives followed by the source equation and its n derivatives.
The [input inventory](sign-det-joint-inputs.md) describes the exact polynomial
and sign bindings and their independent rational-root oracle.

The timed bodies in `bench/HexSignDet/Joint.lean` exercise:

- completion of both original partial descriptors;
- cross-polynomial comparison of the completed sources, including the common
  product and both checked re-encodings;
- construction of both joint tables, separately with reduced and direct
  moment products;
- checking both supplied evidence trees in each production mode.

The table-production bodies each build two tables and replay both. They use
prepared domains. Completion builds two source tables and runs four tree
replays: `buildPrepared` checks each constructed tree, then
`Descriptor.ofReplay?` checks it again. Comparison builds four tables and runs
six tree replays: each re-encoding builds and checks a joint table, builds and
checks a target-descriptor table, then checks the joint tree again.
Completion and comparison construct the domains required by their actual APIs. Result
hashes include both returned derivative words or both table counts; the
comparison hash also includes its common head and ordering.

Preparation constructs and validates the source descriptors, completes them,
computes a comparison and both direct tables, and retains the supplied trees
and graphs. It is outside the timed loops. Untimed callback checks compare
answers with exact evaluation at the known roots before any measurement.
This family has realized support two, candidate matrices of width at most
four, infinite endpoints and no shared source roots. It does not cover maximal
support, finite endpoint constraints, common roots or nested coefficient fields.

## Cost model

The declared model is Θ(n³) polynomial coefficient operations for each timed
body on this family. It is not a unit-bit cost model or a bound for arbitrary
defining polynomials.

The target derivative degrees are 0,…,2n−1, the source derivative degrees are
0,…,n−1, and the source equation has degree n. Every leaf includes exponent
two. `DensePoly.mulImpl` visits every pair of stored coefficients, including
zeros. Consequently the sum of leaf square sizes is

```
(2n)(2n+1)(4n+1)/6 + n(n+1)(2n+1)/6 + (n+1)² = Θ(n³).
```

Positive preprocessing changes the scale of these monomials without changing
their degrees. The leaf products therefore give a cubic lower bound in both
production modes. Checking also reconstructs these products in the direct
moment identities or the supplied reduction identities. Every nonconstant
query also multiplies its moment polynomial by the head derivative and runs
pseudo-division. Those operations contribute O(n²) per row over O(n) rows.
Many visited coefficients are zero: this bound includes dense storage overhead
for sparse monomials, rather than work intrinsic to these particular roots.

The direct path uses `DensePoly.natPow`. In the measured implementation,
`natPow q 1` evaluates `q*q` before recursing to exponent zero, and discards
that square. Exponent two consequently also computes and discards a fourth
power. These additional dense products retain the cubic bound and contribute
to the direct timings. Reduced/direct ratios compare the complete current
implementations, including this work and their replay costs; they do not
isolate the mathematical benefit of reducing products modulo the head.

The complete child restrictions have at most two sign conditions. The retained
row basis starts with the constant row and, when two conditions occur, one
separating query row. Their tensor products have exponent sum at most two.
There are O(n) nodes and at most four moment rows per node. The inventory
requires maximum exponent sum two across both production modes and candidate
width at most four.

All moment operands have degree O(n). The head is a binomial, and the queries
are monomials apart from the one source equation. Reducing the source equation
or its square modulo the common head leaves a multiple of Xⁿ±1. After a
monomial shift, division of X²ⁿ−1 leaves that same binomial, which divides the
next remainder. Thus the remainder chains have bounded length rather than
the degree-dependent length possible for general heads. The inventory records
both modes' maximum chain lengths and rejects a length above eight. This check
describes the sparse family; it is not a claim that longer chains necessarily
violate the cubic coefficient-operation bound. Dense
query-kernel products and certificate identity products cost O(n²) per row,
giving O(n³) over all rows. Balanced query/exponent/sign slot work contributes
O(n² log n); the matrices have bounded dimensions and scalar sizes. Completion
uses source degree n instead of target degree 2n; comparison invokes a fixed
number of these tables and a binomial common-product calculation.

Raw rational coefficients grow with derivative factorials. Reduced witnesses
retain the scale (2n)!/2; the direct witness maximum includes n((2n)!/2)².
The inventories record these exact bit sizes. Actual timings include rational
arithmetic at those sizes, allocation and result hashing. Agreement with the
coefficient-operation model does not establish a bit-complexity bound, and
this family cannot separately identify degree and coefficient-height effects.
The coefficient-height family has its own measurements. A model mismatch is
retained and investigated rather than hidden by changing the model afterward.

## Collection protocol

The explicit degree schedule is 3, 7, 15, 31 and 63, with six trial-major
rounds. Reduced/direct production and replay use adjacent alternating AB/BA
arms. Completion and comparison each use the ordinary shared LeanBench
schedule. The target inner duration is 100 ms; a 60-second per-call cap is an
operational safeguard. Every completed observation is retained. One CPU is
automatically leased, and host activity is recorded without an idleness test
or sample filtering.

The independent input validator checks literal polynomials, both exact sign
tables and dimensions. Callback result hashes bind the measured answers to
those checked inputs. The collector retains source reconstruction, executable
identity, command output, exact schedules and the shared harness verdicts.
Inconclusive verdicts remain observations, not successful performance gates.
At most one unchanged rerun is allowed after an inconclusive result. A changed
implementation requires a separate collection with its own source identity.
The collector runs all scientific arms before validation, so a timeout or bad
point in one arm does not suppress later measurements; the raw records and
validation failures are retained. The harness checkout must be clean and match
the manifest pin before and after collection.

LeanBench records each child's peak resident set, including preparation,
calibration and repeated timed calls. It does not isolate one operation's live
memory. Its allocated-byte field is unavailable, so resident-set observations
do not complete the separate allocated-byte requirement. Stored witness bits
and serialized certificate sizes likewise do not measure temporary peak bits
or allocation. This family alone does not complete Phase 4 or #10377.
