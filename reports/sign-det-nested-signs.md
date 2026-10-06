# Nested coefficient signs

The benchmark signs the newest positive infinitesimal in an iterated canonical
rational-function field over the rationals. It consumes the existing
`HexOrderedFn.Infinitesimal.sign` with the existing `HexRationalFn` field
instances. It changes no arithmetic and imports no tower implementation.

The actual compiled sign rebuilds lower-field zero and one values during its
zero tests and lowest-coefficient scans. Let z_j and u_j be their construction
costs at depth j. `RationalFn.ofPoly` always constructs a denominator one;
polynomial numeral construction also evaluates lower numeral arguments. The
compiled field dictionaries therefore give

```
z_j = 2 z_(j−1) + u_(j−1) + Θ(1)
u_j = 2 z_(j−1) + 2 u_(j−1) + Θ(1).
```

The recurrence matrix has eigenvalues 2 ± √2. Both positive constructor costs
are Θ((2+√2)^j). Below the top level the sign of one invokes two predecessor
signs and constructs lower zeros for its numerator-zero test and scans. The top scan also compares two
nested zeros structurally, which costs Θ(2^d). Thus the whole coefficient sign
is Θ((2+√2)^d), although there are exactly 2^d rational sign calls. The
registration normalizes against `numeralCost`, a positive integer version of
the constructor recurrence. This derivation follows `RationalFn.instOfNat`, `DensePoly.instOfNat`,
`RationalFn.ofPoly` and the specialized `Infinitesimal.sign` compiled in
`NestedSigns.c`; it is not an exponent fitted to observations.

The compiler specializes the scanning function: a zero is constructed for
each visited coefficient. Its in-bounds coefficient access does not evaluate
the default zero. The distinction matters when attributing the cost. Existing
field dictionaries and numeral constructors are measured as they stand;
there is no caching optimization in this benchmark.

Construction of field dictionaries and the coefficient, complete recursive
coefficient encoding, and input hashing take place during preparation. Only
the existing sign operation is timed. The Hashable input includes its complete literal coefficient encoding and
depth. The runner does not export that input hash; the recorded executable
hash, deterministic preparation and inspected result tie the timed input to
the inspected literal. The inspection checks the positive
answer; an independent Python validator checks the entire recursively encoded
value against the literal newest infinitesimal, including its denominator.
`predictedBaseSigns` describes the derived call count, not an instrumented
runtime count or proof dependency count.

The fixed depth schedule is 2, 4, 6, 8, 10 and 12, with six trial-major rounds,
a 100 ms target inner duration and unchanged harness tolerances. A 30-second
child-process cap is an operational safeguard. Collection leases one CPU
without testing its activity, records host load, retains every completed
sample, and binds its clean source, binary, source reconstruction and pinned
harness. Inconclusive results remain findings. At most one unchanged rerun is
permitted.

Run:

```sh
lake build hexsigndet_bench
python3 scripts/bench/sign_det_nested_signs.py --output /path/to/new-captures
```

The output directory must be new and outside the worktree. The old
`hexsigndet_emit_nested_fields --profile local` exercises actual sign tables
and replay at depths one through four; this benchmark isolates the coefficient
sign work consumed by such computations. It does not establish their whole
production/checking complexity, nested certificate sharing, allocated bytes or
live memory. Child peak RSS includes preparation and runtime startup. Separate
proof examples check ordinary-kernel evidence; this benchmark checks no proof
and introduces no theorem-timing sweep.

## Retained finding

The [original 36 observations](data/sign-det-nested-signs/596ef4d810/timing/metadata.json)
retain their actual source and `2^d` declaration. All points succeeded, but the
verdict is inconclusive with residual slope +3.924. Their median per-call times
at depths 2,4,6,8,10,12 are 0.481 μs, 6.670 μs, 82.123 μs, 0.965 ms,
11.384 ms and 134.582 ms. Counting leaf sign calls alone omitted the
constructor costs above; these records are not rewritten under the corrected
declaration or counted as a successful required check.

An ad hoc operation-only diagnosis retained 1173 sampled instruction pointers
within the actual child’s monotonic-clock timed-region intervals, including its
calibration call and eight timed calls. It excludes preparation and startup.
43.05% of samples are in `lean_free_object`, 15.43% in `lean_dec_ref_cold`,
8.35% in polynomial trailing-zero normalization, and 7.93% in small-object
allocation. These are self samples. Stack unwinding failed inside the timed-region
intervals, so no inclusive caller attribution is claimed. The raw profile is retained at
`/home/kim/.local/state/hex/issue-10377-session-progress/nested-signs-profile/perf.data`
on `chungus2`, bound by its archive hash. Decoded samples, boundaries and
summaries are committed. This diagnosis is not a reproducible profiling
pipeline or a replacement for the separate required representative attribution.

## Corrected declaration measurements

The [new source-bound collection](data/sign-det-nested-signs/92056cad4a/timing/metadata.json)
uses the constructor recurrence above, with the same coefficient, sign operation,
depth schedule and harness settings. All 36 points completed successfully.
Its verdict is **consistent with declared complexity**, with normalized slope
+0.087018 and no advisories. The fitted range drops depth two and uses depths
4,6,8,10,12 with the pinned slope tolerance 0.15. This is a new collection
after correcting a demonstrably wrong declaration; the original observations
retain their original declaration and verdict. It does not measure a speedup.

| Extension depth | Median per-call time |
| --- | ---: |
| 2 | 0.000546 ms |
| 4 | 0.007635 ms |
| 6 | 0.094731 ms |
| 8 | 1.127748 ms |
| 10 | 13.232210 ms |
| 12 | 155.551184 ms |

The source and binary hashes, input guards, complete trial-major export,
source reconstruction and host loads are retained. The declaration models
this particular compiled scalar sign, not arbitrary nested arithmetic or the
whole sign-table producer. Higher-depth table production, nested evidence,
allocation and live-memory requirements remain separate.

The declaration keeps the dominant constructor term rather than every
lower-order sign call. At lower level j, the sign of one also obeys
`S(j) = 2 S(j−1) + 3 z_(j−1) + Θ(1)`. Dividing the complete sign cost by
`numeralCost` therefore includes a converging geometric sum. A finite positive
normalized slope is compatible with that source-derived lower-order term;
these data do not distinguish the exact constants of its components.

CI rechecks the archived raw/stored hashes, validates the corrected export
and rejects the original export under the current declaration. The isolated
timed sign is unchanged between the profiled and corrected source revisions;
only the registration model and recording safeguards changed.
