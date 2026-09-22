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

Complete sign-table and Thom semantics, total producer correspondence and
Phase-4 evidence remain required. The root-sum/replay bridge in #10389 and the
specified Tau Ceti BKR/Thom foundations remain separate proof gates; the
polynomial identities above do not discharge them. See the
[specification](SPEC/hex-sign-det-mathlib.md) for the complete assignment.

```sh
lake build HexSignDetMathlib +HexSignDetMathlib.Conformance
```
