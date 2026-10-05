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
signs and constructs these zero defaults. The top scan also compares two
nested zeros structurally, which costs Θ(2^d). Thus the whole coefficient sign
is Θ((2+√2)^d), although there are exactly 2^d rational sign calls. The
registration normalizes against `numeralCost`, a positive integer version of
the constructor recurrence. This derivation follows the constructors and the
compiled sign; it is not an exponent fitted to observations.

The compiler specializes the scanning function: a zero is constructed for
each visited coefficient. Its in-bounds coefficient access does not evaluate
the default zero. The distinction matters when attributing the cost. Existing
field dictionaries and numeral constructors are measured as they stand;
there is no caching optimization in this benchmark.

Construction of field dictionaries and the coefficient, complete recursive
coefficient encoding, and input hashing take place during preparation. Only
the existing sign operation is timed. The input hash includes its complete
literal coefficient encoding and depth. The inspection checks the positive
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
declaration or counted as a successful gate.

The retained operation-only profile has 1173 sampled instruction pointers
within the actual child’s monotonic-clock kernel intervals, including its
calibration call and eight timed calls. It excludes preparation and startup.
43.05% of samples are in `lean_free_object`, 15.43% in `lean_dec_ref_cold`,
8.35% in polynomial trailing-zero normalization, and 7.93% in small-object
allocation. These are self samples. Stack unwinding failed inside the kernel
intervals, so no inclusive caller attribution is claimed. The raw profile is
retained externally and bound by its archive hash; decoded samples, boundaries
and summaries are committed.
