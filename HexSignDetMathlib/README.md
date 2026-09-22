# hex-sign-det-mathlib

Algebraic correspondence for BKR moment reduction over the shared coefficient
interpretation. This development companion is not yet released.

`ReductionStep.check_sign`, `Reduction.check_sign` and `checkMoment_sign` prove
that arbitrary accepted reduction evidence preserves the full moment's sign at
every root of the head polynomial. They use checked zero-difference identities
and positive scales, with no field instance or injectivity assumption on the
coefficient representation.

`ReductionStep.build_checks` and `Reduction.build_checks` prove acceptance of
the actual producer using the shared pseudo-division and normalization
correspondence. No parallel polynomial algorithm or root-sum premise is used.
Conformance includes universal noncanonical instantiations, literal ordinary
kernel acceptance/rejection, and theorem axiom inventories.

`QueryReduction.build_checks` proves acceptance of the actual shared query
preprocessing. `QueryReduction.check_signs` proves preservation of the complete
indexed sign vector for arbitrary accepted witnesses. `Node.check_sign` composes
this fact with reduced-moment replay, identifying the sign of each actual Tarski
operand with the original moment. The finite `slice_checks` theorem verifies
the child-sublist restrictions used by the producer without rerunning division.

`System.retained_rank` proves that removing zero-count columns preserves full
column rank. `basis_checks`, `basis_rank`, `basis_columns` and `basis_inverse`
verify the actual integer rank producer's retained basis, exact column order
and scaled left inverse. `Node.basis_matrix` identifies the selected minor
with its actual retained exponent/sign vectors. `Node.product_inverse` proves
the tensor witness identity and identifies both vector orders with the exact
list products used by `buildTreeFrom`. `solveScaled_eq`
proves that the integer solver recovers any accepted system's counts without
rounding or sign clamping. These finite algebra results do not assume roots
or query semantics and do not yet prove completeness of the full constructor.

Complete sign-table and Thom semantics, total producer correspondence and
Phase-4 evidence remain required. The root-sum/replay bridge in #10389 and the
specified Tau Ceti BKR/Thom foundations remain separate proof gates; the
polynomial identities above do not discharge them. See the
[specification](SPEC/hex-sign-det-mathlib.md) for the complete assignment.

```sh
lake build HexSignDetMathlib +HexSignDetMathlib.Conformance
```
