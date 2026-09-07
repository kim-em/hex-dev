# hex-lattice-enum-mathlib

Correctness proofs for exact lattice enumeration and correspondence with
integer spans in rational and real coordinate spaces. The complete contracts,
including the headline theorems, packing radius, kissing number and proof
examples, are specified in
[hex-lattice-enum, Mathlib companion](../../HexLatticeEnum/SPEC/hex-lattice-enum.md#mathlib-companion).

Immediate dependencies are `HexLatticeEnum`, `HexLLLMathlib`,
`HexGramSchmidtMathlib` and `HexMatrixMathlib`, plus Mathlib. All executable
preparation, enumeration, optimization, budget handling, certificate production,
decoding and checking remain in `HexLatticeEnum`. Importing this companion
provides proofs about those same definitions; no runtime implementation is
duplicated here.

This library proves preparation validity for every accepted independent input,
using `StepWitness.ofGram`, `basis_normSq` and `scaledCoeffs_eq` from the existing
Gram-Schmidt companion. It proves coefficient injectivity, the exact distance
decomposition including the orthogonal target residual, and the unconditional
`enumerate_spec`, `shortest_spec` and `closest_spec` contracts. Any internal
prepared-data validity assumptions are discharged here, without adding witness
arguments or failure cases to the public computational API.

It also owns `checkEnumeration_sound`, optimum-checker soundness and the
theorems that completed native runs produce accepted certificates. Checker
soundness applies to arbitrary accepted certificates and does not assume native
provenance. Integer-span and real-distance correspondence and the packing-radius
and kissing-number consequences build on these correctness results. See
[execution and proof ownership](../../HexLatticeEnum/SPEC/hex-lattice-enum.md#execution-and-proof-ownership)
and [placement and implementation order](../../HexLatticeEnum/SPEC/hex-lattice-enum.md#placement-and-implementation-order)
for the division of files and proof obligations.

At activation set `correspondence_only: true`. The comparator absence class
is **correspondence-only-layer**. This library has no runtime conformance or
benchmark targets. Build-only examples in `HexLatticeEnumMathlib/Tests.lean`
exercise preparation validity, the unconditional search contracts, kernel
certificate replay, integer-span transport and geometric consequences without
runtime commands. Elementary computational lemmas may remain in the Mathlib-free
library; its execution and termination must not depend on this companion.

Computational conformance owner: `HexLatticeEnum`.

Computational performance owner: `HexLatticeEnum`.
