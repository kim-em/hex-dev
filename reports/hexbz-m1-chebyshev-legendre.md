# Original-Coordinate BZ Follow-up

This report records the resolution of the six Chebyshev/Legendre performance
issues #9104–#9109. The production result is clean revision
`d580b121292be127be33b312fe888b00573379ed`, measured on 2026-07-30 on
`chungus2` (AMD EPYC 9455, Linux x86-64), pinned to CPU 0. The comparison
baseline is clean revision `b0150d2b4a6154d7b9ed3c7cace4fee0ace64165`.

## Dependency outcomes

```text
                       ┌──────── #9106 degree bound (measured no-go) ────────┐
#9104 original M1 ─────┼──────── #9107 bounded modular certificate ─────────┼─→
                       │                                                     │
#9105 modular profile/reuse ─────────────────────────────────────────────────┘
                                                                             ↓
                                                        #9108 cost gate / policy
                                                                             ↓
                                                        #9109 relift decision
```

The measured no-go result for #9106 is a completed dependency, not an omitted
one. Likewise, #9105 supplies the modular-cost and reuse result consumed by
#9107/#9108 even though it does not justify a new native kernel.

| Issue | Resolution |
|---|---|
| #9104 | Implemented a proved original-coordinate M1 lift/recombination path with exact M2 fallback. |
| #9105 | Reused the selected modular factorization for M1. Per-prime timings do not justify a large specialized native kernel after reuse. |
| #9106 | Measured no-go: the current head-forced search admits only a very small safe degree reduction, and the resulting lift savings miss the issue gate. |
| #9107 | Implemented a bounded, proof-producing two-prime degree obstruction. Rejected a longer singleton/Rabin scan as too expensive. |
| #9108 | Retained the already-good bounded adaptive prime choice and added a deterministic downstream-cost gate for attempting M1; no second adaptive walk occurs. |
| #9109 | Selected the measured hybrid: direct full-precision M1 on favorable shapes, with the proved recursive M2 path retained for monic, wide, low-degree, or uncertified cases. |

## Verified M1 path

The new path:

1. runs the existing adaptive selector exactly once on `toMonic core`;
2. transports its selected modular factors back to the original coordinate by
   `c⁻ᵈ q(cX)`, preserving the prime and modular width;
3. Hensel-lifts `monicTarget core` at the original core's Mignotte precision;
4. reconstructs `primitivePart (centeredLift (lc(core) · ∏S))`;
5. checks product, primitivity, sign normalization, and positive degree;
6. accepts singleton pieces only through a modular irreducibility certificate,
   and independently refines split pieces through the proved M2 path;
7. falls back to the existing exact M2 route on any failed search or
   certificate.

The Mathlib layer proves modular transport, subset-degree obstruction
soundness, M1 recovery and factor shape, irreducibility, normalization, degree,
and the combined M1/M2 and public-dispatch specifications. No axiom,
`native_decide`, or new `sorry` is used.

## Precision and phase effect

The original-coordinate lift removes the coefficient-swollen M2 precision.
These are same-prime, same-modular-factor measurements made before production
integration:

| Case | Core bound log2 | M2 bound log2 | M2 `k` | M1 `k` | M2 lift | M1 lift |
|---|---:|---:|---:|---:|---:|---:|
| Chebyshev U24 | 50 | 573 | 363 | 33 | 4.23 ms | 0.24 ms |
| Legendre P24 | 69 | 1026 | 180 | 13 | 4.79 ms | 0.53 ms |
| Legendre P26 | 74 | 1189 | 203 | 13 | 5.53 ms | 0.84 ms |
| Legendre P30 | 86 | 1579 | 257 | 15 | 4.08 ms | 0.42 ms |
| Legendre P38 | 113 | 2640 | 419 | 19 | 5.22 ms | 0.64 ms |

M1 recombination itself was 0.02 ms on U24, 0.63 ms on P30, and 0.48 ms on
P38. After this change, modular selection/certification rather than lifting is
the dominant Legendre cost.

## Public before/after

The table uses the checked-in public sweeps. Times are persistent-service
median wall clocks; ratios below one are improvements.

| Row | Previous Hex | M1-gated Hex | New/old | Isabelle BZ | New/Isabelle |
|---|---:|---:|---:|---:|---:|
| Chebyshev T18 | 2.795 ms | 1.789 ms | 0.640× | 1.034 ms | 1.729× |
| Chebyshev T20 | 3.305 ms | 2.986 ms | 0.904× | 1.316 ms | 2.270× |
| Chebyshev T24 | 2.028 ms | 1.443 ms | 0.712× | 1.253 ms | 1.152× |
| Chebyshev U18 | 1.655 ms | 0.411 ms | 0.248× | 0.711 ms | 0.578× |
| Chebyshev U20 | 3.981 ms | 0.921 ms | 0.231× | 1.361 ms | 0.676× |
| Chebyshev U24 | 2.610 ms | 0.816 ms | 0.313× | 1.472 ms | 0.554× |
| Legendre P22 | 2.913 ms | 2.076 ms | 0.713× | 2.054 ms | 1.011× |
| Legendre P24 | 7.190 ms | 7.301 ms | 1.016× | 3.830 ms | 1.906× |
| Legendre P26 | 12.343 ms | 12.504 ms | 1.013× | 6.394 ms | 1.955× |
| Legendre P28 | 8.205 ms | 4.952 ms | 0.604× | 5.107 ms | 0.970× |
| Legendre P30 | 13.807 ms | 11.034 ms | 0.799× | 10.717 ms | 1.030× |
| Legendre P34 | 11.947 ms | 12.086 ms | 1.012× | 6.349 ms | 1.904× |
| Legendre P38 | 13.602 ms | 8.422 ms | 0.619× | 6.743 ms | 1.249× |

The P24/P26/P34 movements are below 1.6% and those rows remain on the unchanged
M2 path. The gate deliberately selects the rows where M1 plus its certificate
is cheaper, while avoiding both low-degree overhead and exponential searches
at large modular width.

Across overhead-eligible rows, the Chebyshev median falls from 1.619× to
1.260× Hex/Isabelle and the Legendre median from 1.435× to 1.249×.
Chebyshev moves from one Hex win to four. P28 now beats Isabelle, while the
P30/P38 gaps narrow to 1.030× and 1.249×.

## Modular scan and policy decision

The production M1 branch reuses the selected factorization. It does not repeat
the adaptive Berlekamp walk. Individual good-prime factorizations cost roughly
1.2–2.6 ms on P24/P28/P30 and 3.8–7.2 ms on P38; P30's complete production
walk costs about 8 ms. Sampling attributes the remaining modular time broadly
to dense-polynomial arithmetic, boxed `ZMod64` operations, matrix/splitting
work, conversions, reference counting, and allocation. No single
post-reuse phase was shown to contribute the required 25% of P30/P38 walk time,
so a large proof-equal native kernel would not clear #9105's gate.

The bounded degree-pair certificate does clear #9107's end-to-end gate:

- P28 combines `p=59`, degrees `[5,5,2,16]`, with `p=61`, degrees
  `[14,14]`, and falls from 8.205 ms to 4.952 ms.
- P30 reuses `p=71`, degrees `[22,2,3,3]`, then uses `p=73`, degrees
  `[13,13,4]`, and falls from 13.807 ms to 11.034 ms.
- P38 reuses `p=79`, degrees `[36,1,1]`, then uses `p=83`, degrees
  `[18,16,4]`, and falls from 13.602 ms to 8.422 ms.

The scan examines at most four later candidates and only after the M1 cost gate.
Each side of the exponential subset-degree comparison is capped at 12 modular
factors. Misses therefore cannot create an unbounded prime walk or admit an
unbounded subset computation.

A broader irreducibility scan is a measured no-go. P26 first becomes a
singleton at its eighth good prime (`p=83`); P30 at its eighteenth
(`p=149`); and P38 at its eleventh (`p=131`). The cumulative extra Berlekamp
cost already exceeds the work that would be avoided. Full Rabin/certificate
scans were slower still. P24 does not obtain the useful degree pair until
`p=103`, beyond the bounded horizon.

The existing adaptive selector is therefore retained. This is important: the
M1 implementation transports the selector's result rather than rerunning
selection against the core, so the coefficient-swell signal that preserves the
P26/P30 width reductions never disappears. The new M1 eligibility rule is the
small deterministic cost model:

- non-monic;
- degree at least 18;
- at least two selected modular factors;
- selected modular width at most 8; and
- either a small selected prime relative to degree, or a modular factor
  materially larger than half the input degree.

This keeps the current P26/P30 selected primes and factor widths, avoids a
second adaptive walk, and reserves the extra certificate probe for sparse
subset-degree partitions.

## Degree-aware-bound no-go

The current search forces the first modular factor into every candidate. Its
largest proper candidate therefore has degree
`D = n - min(tail modular degrees)`, not generally `n / 2`. The benchmark-only
diagnostic evaluates the most optimistic Mignotte bound sound for that search
shape and times its M1 lift:

| Case | `n` | `D` | Bound bits | `k` | Uniform lift | Capped lift |
|---|---:|---:|---:|---:|---:|---:|
| U24 | 24 | 22 | 51 → 49 | 33 → 32 | 0.238 ms | 0.193 ms |
| P24 | 24 | 22 | 70 → 68 | 13 → 12 | 0.522 ms | 0.512 ms |
| P26 | 26 | 24 | 75 → 73 | 13 → 13 | 0.624 ms | 0.634 ms |
| P28 | 28 | 23 | 82 → 77 | 14 → 14 | 0.504 ms | 0.506 ms |
| P30 | 30 | 28 | 87 → 85 | 15 → 14 | 0.453 ms | 0.445 ms |
| P38 | 38 | 37 | 114 → 113 | 19 → 18 | 0.515 ms | 0.519 ms |

Only U24 shows more than a few hundredths of a millisecond, and even its
end-to-end upper bound is about 5.5%. There are not three material rows with a
10% lift-time win, nor a material memory case whose lift remains at least 20%
of total time. A more aggressive `n/2` cap would require changing the search
orientation and proving a new recovery argument; it is not a free bound
improvement. #9106 therefore stops at its specified measured no-go.

## Relift decision

Eligible rows bypass the speculative M2 sub-floor ladder and go directly to
the now-cheap full M1 precision. U24 remains 3.20× faster than its pre-M1
baseline. Monic inputs, large modular widths, low degrees, and failed
certificates continue through the existing recursive M2 implementation.

This is the measured hybrid requested by #9109: it removes the ladder from the
rows for which M1 invalidates its cost rationale without deleting a proved path
that is still useful to monic/high-width families. The unchanged no-decline
diagnostic was not rerun.

## Full-sweep validation

The final public sweep solves 373 of 392 rows with 19 timeouts, a
401.114 µs solved-row median, 4.052 ms p90, and 8.900 s slowest solve. Every
returned factor-degree multiset and status agrees with the baseline.

The full `lake build`, all 16 non-scheduled `hexbz_bench verify` targets,
fresh fixture reproduction, the 106-case FLINT oracle, and the 54-case
anti-regression trace gate pass.

Against the first M1 record, 243 overhead-eligible pairs have median 0.990×
and p10–p90 0.965×–1.009×, with 187 rows faster and 56 slower. The review
identified that modular-factor coordinate transport was bound before the M1
gate, so strict evaluation paid that cost even on skipped paths. Moving the
transport into the taken branch corrects the earlier interpretation of eight
monic cyclotomic slowdowns: those rows now take 0.628×–0.684× of the first M1
record and return to 1.009×–1.041× of the pre-M1 baseline. The prior
frequency-drift attribution is withdrawn.

The first M1 record is
`reports/bench-results/hexbz-factor-sweep-hex-2ee33dc5-m1-chungus2.json`
(SHA-256
`a604aaaf492dacf726a0ae6315744f14a46dd21d124033b846a73e00f5511e89`).

The review also made the route directly observable (`notTried`, `accepted`, or
`fallback`), pins accepted M1 on U18 and P28, exercises certificate rejection
followed by exact M2 recovery, and adds a proved degree prefilter before
building original-coordinate candidates.

The final artifact is:

- `reports/bench-results/hexbz-factor-sweep-hex-d580b121-m1-review-chungus2.json`
  (SHA-256
  `455b5fc28681707357eda6c60fba25531937128c51f9c3065231adf73dbd959d`)

Reproduce the phase diagnostic with:

```sh
lake build hex_prime_policy_spike
taskset -c 0 lake exe hex_prime_policy_spike
```

Reproduce the public sweep with:

```sh
lake build hexbz_factor_service
taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep-hex.json
```
