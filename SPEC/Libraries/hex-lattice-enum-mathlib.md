# hex-lattice-enum-mathlib

Correspondence of exact lattice enumeration with integer spans in rational
and real coordinate spaces. The complete contracts, including the headline
theorems, packing radius, kissing number and proof examples, are specified in
[hex-lattice-enum, Mathlib companion](hex-lattice-enum.md#mathlib-companion).

Immediate dependencies are `HexLatticeEnum`, `HexLLLMathlib`,
`HexGramSchmidtMathlib` and `HexMatrixMathlib`, plus Mathlib. The executable
enumeration and certificate checkers remain in `HexLatticeEnum`.

At activation set `correspondence_only: true`. The comparator absence class
is **correspondence-only-layer**. This library has no runtime conformance or
benchmark targets. Build-only examples in `HexLatticeEnumMathlib/Tests.lean`
prove the transported statements without runtime commands.

Computational conformance owner: `HexLatticeEnum`.

Computational performance owner: `HexLatticeEnum`.
