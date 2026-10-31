# HexGroebnerTheory

The Mathlib companion for `HexGroebner`. Its governing contract is
[SPEC/Libraries/hex-groebner.md](../SPEC/Libraries/hex-groebner.md).

`Order` transports every lawful `Hex.IsMonomialOrder` into Mathlib's
`MonomialOrder (Fin n)` through `HexMvPolyTheory.monoEquiv`. It proves exact
strict and non-strict comparison agreement, leading monomial and coefficient
agreement for nonzero polynomials, and pointwise divisibility and LCM
correspondence. The construction carries the supplied well-foundedness and
multiplicative compatibility laws; it introduces no independent polynomial
interpretation.

`Examples` gives ordinary-kernel checks for lex, grlex and grevlex. Build with
`lake build HexGroebnerTheory +HexGroebnerTheory.Examples`.

Complete basis and membership certificate soundness, Buchberger's criterion,
reduced-basis uniqueness, deterministic F4 correctness and termination remain
required by the same contract. The executable candidate API remains unchecked.
