# Storage and context experiments

E1 compares four policies on exactly the same semantic inputs:

0. Unreduced nonzero representatives, generic gcd/Sturm zero test, reducible
   defining polynomial `(X²−2)(X²−3)` selecting positive sqrt(2).
1. Same descriptor and zero test, retaining the already-computed remainder.
2. Same retention policy, using `X²−2` with the generic zero test.
3. Same minimal polynomial and retention, exploiting irreducibility to test
   the remainder directly. Only this known fixture takes that fast path;
   there is no claimed general irreducibility oracle.

Compare adjacent pairs 0/1, 1/2 and 2/3 separately. Pair 0/1 isolates storage,
1/2 exposes the descriptor-degree effect, and 2/3 isolates the zero-test fast
path. At the second level use `Y²−sqrt(2)` and remainder zero, justified by
irreducibility of `X⁴−2` over Q. Both minimal polynomials are independently
factor-checked with FLINT. These are mathematical fixture facts, not new Lean
irreducibility proofs or a general root-selection algorithm.

Fixed before timing: ten cases, the division/gcd pair at base lengths 2,3,4,
then nested lengths 2,3. The divisor has one fewer coefficient. The shared
input rule is `Policy.coefficient`; result comparison uses complete canonical
field values. Six adjacent AB/BA blocks for each case and each of the three
policy pairs. lean-bench owns timing, warmup and adaptive inner repetition,
with one sample per arm per block and a 50ms floor. All 360 measured samples
are retained, with no rerun or activity-based filtering. This is an
informational policy comparison, not Phase-4 complexity evidence.

Preparation is outside timing; semantic output hashing is inside in all arms.
The digest cost can depend on the policy’s output representation; these timings
measure operation plus digest, not isolated division/gcd. The fixed generator
produces one- or two-cancellation division cases and one- or two-step gcd loops.
Pin to one automatically leased CPU and record source hashes, versions and
load. Untimed modes 4–7 execute the same policies with callback tracing,
counting actual zero tests at each level, including hashing. Their output
hashes must match the timed arms. An input structural hash is printed before
each BEGIN so preparation is forced outside the trace region. Record output representative degrees and
repeated-squaring growth separately; these are not peak intermediate sizes.

E2 splits the lower reducible descriptor to `X²−2`, explicitly transports the
upper defining polynomial and live values, and preserves positive selected
roots. Validate transport against independent arithmetic in Q[X]/(X⁴−2),
including an inverse. Check the wrong-root split is rejected, old handles
remain valid in the old context, and full literal context/operand bindings
reject stale tickets in the new one even when the operand literal is unchanged.
The tickets test binding discipline, not a full sign certificate checker.
No production API, arbitrary tower proof, Mathlib import or HexInterval change
is part of either experiment.
