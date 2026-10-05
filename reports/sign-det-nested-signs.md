# Nested coefficient signs

The benchmark signs the newest positive infinitesimal in an iterated canonical
rational-function field over the rationals. It consumes the existing
`HexOrderedFn.Infinitesimal.sign` with the existing `HexRationalFn` field
instances. It changes no arithmetic and imports no tower implementation.

At depth d the actual sign calls the predecessor sign twice, for the first
nonzero numerator and denominator coefficients. Both selected coefficients are
one. Their predecessor signs again each call two lower signs, until exactly
2^d rational signs are reached. The arrays have bounded size; canonical zero
checks and finding the first nonzero coefficient cost at most O(d) at one
level on these constant inputs. Thus T(d)=2T(d−1)+O(d)=Θ(2^d). This model is
independently derived from the consumed sign operation and this particular
family, rather than from measured times.

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
