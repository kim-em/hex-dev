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

## Array and comparison correspondence

The [exact comparison contract](../../SPEC/Libraries/hex-real-algebraic.md#exact-comparison-strategies)
adds `sort_perm` and `sort_sorted`, identifying the array sort with a permutation
in nondecreasing `realCompare` order. On canonical values, equality of comparison
keys is equality of values, so no separate stability theorem is needed for an
untagged array. `min?_eq` and `max?_eq` identify Lean's array extrema with folds
of the reference scalar operations, including empty arrays. `compareArray_eq`
identifies the existing array `Ord` with lexicographic `realCompare` after
projecting to canonical algebraic numbers.

`compareIndex_eq` requires indices into a certified strictly increasing array
of distinct real values. Use the existing `realAlgebraicRoots_sorted` and
`realAlgebraicRoots_nodup` for the exact-sorted root view. To reuse raw
`algebraicRoots` order without sorting, require that all real entries share
one minimal polynomial and use the new number-field `rootLe_real` bridge.
Do not infer value order from `algebraicRoots_sorted` across different factors;
that theorem concerns stored centre keys. The initial exact sort for a general
reducible polynomial is part of the computational cost.

The number-field companion owns `realCompare_eq_exact` and all point, lazy,
and fixed-field correspondence. This companion transports those equations
through the real subtype and retains its existing `compare_eq`, order laws,
and executable dictionaries. The new array obligations have conformance and
performance evidence in `HexRealAlgebraic`; no proof-generation API is added.
