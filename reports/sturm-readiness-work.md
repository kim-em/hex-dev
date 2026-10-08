# Source work for the Sturm readiness families

This derivation concerns `P=T_n`, query one and integral endpoints ±2
(retargeting uses ±3). It is not a bound for arbitrary ordered coefficient
oracles or arbitrary heads. The implementation uses primitive integer
normalization or positive absolute-leading-coefficient normalization over Rat;
unnormalized pseudo-remainder coefficient growth is outside this argument.

The standard identities are `T_n = X U_(n−1) − U_(n−2)` and
`U_k = 2 X U_(k−1) − U_(k−2)`. Each subsequent degree drops by one.
A consecutive-degree division has a degree-one quotient and at most two
leading cancellations. Across the chain this visits O(n²) coefficients.
The integer primitive entries remove content from U; Rat entries after the
literal head are positive-scaled monic U entries. U's explicit binomial
coefficients have O(k) bits, and its leading coefficient is 2^k. Monic
normalization thus has O(k)-bit numerators and power-of-two denominators.

The literal head and derivative have O(n+log n)=O(n) coefficient bits.
Pseudo-division between consecutive degrees raises the leading coefficient
to at most its square. Each cancellation multiplies bounded-width values and
adds at most two such products. The unnormalized remainder and the stored
quotient, multiplier and normalization factor consequently have O(n) bits.
Normalization returns the next bounded-width U entry; the argument starts
again at the next division, rather than accumulating uncancelled scales.
Terminal division and the initial lower-degree derivative reduction have the
same bounds. Endpoints ±2/±3 introduce at most O(n) additional bits.

GMP's schoolbook multiplication and classical quadratic gcd bounds therefore
cover each coefficient operation in O(n²) bit work. Summing O(n²) visits gives
O(n⁴) total bit work. Array/object traversal and hashing can scan O(n³) stored
bits, and unnormalized Horner evaluation at these fixed integral endpoints costs
at most O(n³). Final dyadic normalization can cost quadratic work per O(n)-bit
result and is also covered by O(n⁴); neither exceeds the quartic bound. This is an upper bound, not a claim
that multiplication or gcd dominates the measured range.

| Timed bodies | Work covered |
| --- | --- |
| Integer/rational query, rational domain preparation, integer chain production | A constant number of normalized derivative chains and endpoint passes |
| Prepared query/certification | One new query-one chain; retained domain chain reused |
| Fresh root count/certification | Domain validation and query-one chains |
| Prepared-count certification | Retained chains, endpoint passes and certificate hashing |
| Field/cached replay | O(n²) coefficient identity operations with degree-one quotients, endpoint checks and literal bindings |
| Denominator clearing / embedding | O(n²) stored coefficients; O(n)-bit power-of-two denominator lcm/scales and bounded-width numerators; hashing included |
| Infinite-endpoint query | Chain production with leading-coefficient signs replacing finite Horner |

These cover the fourteen retained quartic registrations. The preregistered
expression and samples remain unchanged. The faster residuals do not establish
tight quartic wall time; the completed schedules satisfy the independently
supported upper bound on their stated source families.

## Finite-range two-sided findings

For derivative/initial reduction and fixed-denominator clearing there are
Theta(n) coefficient-object visits plus Theta(n²) total coefficient bits.
Retargeting evaluates only the head twice and has the same pair of work
orders. On a fixed-word machine this gives dispatch/object work of order n
and limb work of order n²/word-width. Positive contributions predict finite-
range growth between linear and quadratic, rather than a tight quadratic
wall-time model throughout a small-limb range. The retained small ladder's
negative residuals have that direction and magnitude: effective exponents
1.207863 (initial), 1.186529 (clearing), 1.568819 (retarget). No coefficient is
fitted to timings. Wider predeclared ladders pass their unchanged quadratic
models; initial and clearing use aliases of the same functions. Retarget's
wide family is different and is corroborating operation evidence only.

Prepared counting and integer endpoint evaluation instead visit Theta(n²)
coefficient objects and Theta(n³) total coefficient/accumulator bits. The
resulting word/object and limb contributions predict growth between quadratic
and cubic on the finite ladder. The retained effective exponents 2.301893 and
2.147280 are inside that source-derived interval. This predicts downward
deviation by at most one exponent unit, without choosing an exponent from
timings or asserting an exact allocation/arithmetic split. The original
verdicts remain inconclusive. This is a finite-range explanation with explicit
limits, not a retrospective fitted pass or a universal runtime law.

The integer sign replacement removes limb-copy work; it does not add a new
leading-order cost to these paths. `evalDyadic` and its normalization loop are
unchanged since the retained head-wide source. The original head-wide binary
has limited dirty-tree provenance; every historical absolute time keeps that
scope. Current source/API and import-cone checks are separate evidence.

## Source and observation scope

The [compiled import-cone diff](bench-results/sturm-source-cone.json) and
[selected definitions](bench-results/sturm-selected-source.json) compare the
recorded clean checkout `62399ddd0` with `90c4f0e144`. Their reproduction scripts
accept those two commits. The toolchain and LeanBench pin are unchanged.
New domain/reduced APIs and external comparators do not execute in the old
timed bodies; proof edits are erased. `HexPoly.Instances` adds a polynomial
power shortcut, outside these Int/Rat timed paths. The integer-sign compiler
replacement removes copying without changing the sign result.

The growing-operand capture's executable hash matches the executable retained
for the clean-checkout `62399ddd0` profiles. This is a byte-identity observation
about those captures, not evidence of a hermetic build from that checkout. The
head-wide capture has older dirty-tree provenance. Selected timed definitions
are unchanged, but that metadata cannot attest every unrecorded dirty edit;
its absolute values retain that limitation. No current-binary timing identity
or universal polynomial family claim is made.

The older rational-chain profile attributes 52.06% of samples to allocation
and 33.64% to GMP. It supports mixed object/arithmetic work rather than a
general-multiplication-dominated range, but does not determine an exact split
for the five operations above. The finite-range explanation predicts only
direction and an interval of rough exponent size. No timing coefficients are
fitted. The complete consumer query curves cover degree 4–64, and retained
short-chain/growing-operand schedules cover independent axes. The dirty-tree
wide ladder is not the sole evidence of usable compiled Sturm queries.
