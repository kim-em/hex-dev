# Root extraction versus Berlekamp splitting for completely split modular images

Measurement gate for issue #9157. Driver:
`bench/HexBench/RootSplitProbe.lean` (`lake exe hexbz_root_split_probe`).
Record: `reports/bench-results/hexbz-root-split-probe-f87a0c7d.json`
(measured on `chungus2`, median of 3, baseline commit `f87a0c7d`).

## Question

A squarefree `f` over `F_p` is a product of distinct monic linear factors
exactly when it has `deg f` roots in `F_p`. When that holds, enumerating the
roots and emitting `X - r` for each is a complete factorization, and no
Berlekamp basis, no equal-degree separation, and no gcd recursion is needed.

Three costs decide whether that is worth doing:

* the residue scan, one Horner evaluation per element of `F_p`;
* building the monic linear factors from the roots found;
* what the current `Hex.Berlekamp.berlekampFactor` costs instead.

A fourth cost was priced and rejected: `X^p mod f`, the natural
complete-splitting certificate. It is *not* cheaper than the scan it would
guard (for example 295 µs against 237 µs at `d = 64`, `p = 67`), and it is
recomputed inside the fixed-space matrix afterwards, so paying for it would
add work in exactly the region where the fast path does not fire. The scan is
its own certificate instead: the result is used only when the scan finds
`deg f` roots.

## The fast path where it fires

The scan plus extraction against the current path, on the Wilkinson rows over
the primes the production planner selects for them:

| row | `p` | `deg` | scan + extract | `berlekampFactor` | reduction |
| --- | --- | --- | --- | --- | --- |
| `wilkinson_40` | 47 | 40 | 110.3 µs | 1728.3 µs | 93.6% |
| `wilkinson_40` | 41 | 40 | 93.9 µs | 1710.7 µs | 94.5% |
| `wilkinson_48` | 61 | 48 | 166.3 µs | 2753.0 µs | 94.0% |
| `wilkinson_48` | 53 | 48 | 143.3 µs | 2718.9 µs | 94.7% |
| `wilkinson_56` | 67 | 56 | 217.0 µs | 4181.6 µs | 94.8% |
| `wilkinson_56` | 59 | 56 | 191.5 µs | 4015.6 µs | 95.2% |

Both candidate primes of each Wilkinson row are completely split, so both
modular factorizations of the prime walk take the fast path.

Transfer to independent completely split inputs, built from deterministic
distinct residues rather than from any benchmark family, holds across the whole
degree and field-size grid measured (degrees 8 to 128, primes 11 to 32771): the
extraction is 30x to 320000x faster than `berlekampFactor` on the same input,
and every fast-path factor multiset was checked against the `berlekampFactor`
multiset before its time was recorded.

## The crossover

The production budget has two tests.

`deg f ≤ p` is necessary rather than economic: `F_p` has `p` elements, so a
polynomial of higher degree cannot have `deg f` distinct roots there and its
scan can never succeed. It costs nothing to check and it removes every corpus
row whose selected prime is small relative to its degree — which, on this
corpus, is nearly all of them.

`25 * p ≤ (deg f)^2` is the economic test. The scan costs `p · deg f` modular
multiplications; the fixed-space matrix it replaces multiplies `deg f`
polynomials modulo `f`, each product quadratic, so about `(deg f)^3`. The ratio
is about `p / (deg f)^2`, and the constant 25 puts the scan at about a
twenty-fifth of the matrix build.

Measured against controls that pass both tests and then fail the length test —
the only inputs that pay for a scan and get nothing — the wasted scan costs:

| control | `p` | `deg` | scan | `berlekampFactor` | overhead |
| --- | --- | --- | --- | --- | --- |
| `boundary_d32_p37` | 37 | 32 | 61.9 µs | 3365.1 µs | 1.84% |
| `generic_d64_p67` | 67 | 64 | 231.9 µs | 18877.1 µs | 1.23% |
| `boundary_d64_p163` | 163 | 64 | 586.1 µs | 25431.3 µs | 2.30% |
| `boundary_d128_p653` | 653 | 128 | 4906.6 µs | 348563.9 µs | 1.41% |
| `boundary_d240_p2297` | 2297 | 240 | 34563.2 µs | 4541341.3 µs | 0.76% |

The `boundary_*` rows sit immediately inside the economic test, so they bound
what the budget admits: between 0.8% and 2.3% of `berlekampFactor`.
`berlekampFactor` is itself a fraction of end-to-end factorization time (about
13% to 30% on the corpus rows profiled in
`reports/berlekamp-factor-phase-profile.md`), so the end-to-end cost of an
admitted-but-rejected scan stays well under 1%.

Everything else pays nothing at all, because no scan runs. The economic test
rejects the cases where a scan would be expensive relative to the work it might
save: `generic_d16_p1009` and `generic_d32_p1009` would have cost 24.4% and
25.7% of `berlekampFactor`, and the wide-field rows (`p` up to 1000003 with
`deg` 4 and 16) up to 37.8%. The necessary test rejects `boundary_d16_p7`
(which would have cost 2.43%) and every low-prime corpus row.

On the committed corpus the two tests together admit a scan on the Wilkinson
rows and on nothing else, so the measured end-to-end overhead outside the
selected region is zero.

## Verdict

The gate passes. Root extraction removes about 95% of the finite-field
factorization cost where it fires, transfers to independent completely split
inputs across the measured degree and field-size range, and the budget holds
the cost of a rejected scan under 2.5% of the `berlekampFactor` call it would
otherwise have joined.
