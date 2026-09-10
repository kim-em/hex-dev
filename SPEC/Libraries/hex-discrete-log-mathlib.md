# hex-discrete-log-mathlib

Correspondence between executable discrete logarithms and powers in Mathlib
finite-field unit groups. Dependencies are `HexDiscreteLog`, `HexGFqMathlib`
and `HexIntFactorMathlib`, plus Mathlib. The complete computational and
mathematical contracts are in
[hex-discrete-log](hex-discrete-log.md#certificates-and-mathlib-correspondence).

The headline `log_spec` identifies complete solver outputs with the unique
`x < orderOf g` satisfying `g^x = h`, and absence with nonmembership in
`Subgroup.zpowers g`. Identify the stored exact order with `orderOf` and
transport the BSGS coverage proof, PH digit/CRT equations, bounded rho
witness theorem and accepted certificate checks. Exhaustion implies no
negative mathematical conclusion. Raw finite-field target zero is handled
before passing to the units representation.

The computational and Mathlib group operations and powers must agree. Use
the existing finite-field correspondence and packed/generic equivalence;
record the chosen field embedding when comparing representations. Theorems
must cover bases generating proper subgroups as well as primitive bases.

This library is `correspondence_only: true`, with comparator absence class
**correspondence-only-layer**. Build-only examples in
`HexDiscreteLogMathlib/Tests.lean` cover exact order, canonical exponents,
a proper-subgroup nonmember, PH reconstruction and rho exhaustion. It owns
no runtime search, conformance driver or benchmark process.

Computational conformance owner: `HexDiscreteLog`.

Computational performance owner: `HexDiscreteLog`.
