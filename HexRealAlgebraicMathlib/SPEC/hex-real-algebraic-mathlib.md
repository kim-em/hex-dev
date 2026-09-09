# hex-real-algebraic-mathlib

This library is a `correspondence-only-layer`.

Computational conformance owners: `HexRealAlgebraic`
Computational performance owners: `HexRealAlgebraic`

The companion shares the
[ordered real algebraic number specification](../../SPEC/Libraries/hex-real-algebraic.md)
with the computational library. It proves closure, arithmetic and order
correspondence, root completeness and multiplicities, rounding, approximation,
rational recognition, and real-closedness. Its semantic maps and polynomial
views are noncomputable; its field and order dictionaries explicitly retain
the computational library's executable data. The proof-only `Laws` witness
supplies the conditional core dictionaries without introducing a new algorithm.

Conformance fixtures and any performance measurements belong to
`HexRealAlgebraic`. This companion has no separate oracle, benchmark, checker,
reifier, or proof-generation interface. Its regression modules check theorems,
axiom dependencies, and dictionary coherence during compilation.
