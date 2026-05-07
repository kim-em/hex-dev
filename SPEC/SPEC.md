# hex — Verified Computational Algebra in Lean 4

A collection of cooperating Lean 4 libraries providing performant, verified
algorithms for computational algebra: polynomial arithmetic, factoring,
irreducibility testing, finite field construction, lattice basis reduction,
and related tools.

## What we're building

The end state is a verified Berlekamp-Zassenhaus factoring pipeline for
polynomials over the integers, with LLL lattice basis reduction for the
factor recombination step. All algorithms are implemented and run natively
in Lean 4 — no external CAS in the loop. The pipeline produces machine-checked
proofs of correctness alongside its computational results.

The computational core is Mathlib-free: dense `Array`-backed polynomials with
`UInt64` coefficients for finite-field arithmetic, Barrett/Montgomery reduction
for modular operations, and GMP FFI for big-integer primitives. Separate
Mathlib bridge libraries prove correspondence with Mathlib's mathematical
definitions (e.g. `DensePoly R ≃+* Polynomial R`, `ZMod64 p ≃+* ZMod p`,
`GFq p n ≃+* GaloisField p n`), transferring deep correctness results from
Mathlib's abstract algebra without imposing Mathlib as a dependency on the
computational code.

The library DAG has three independent roots — polynomial arithmetic, integer
arithmetic, and matrix operations — meeting at the top in
Berlekamp-Zassenhaus. This structure allows parallel development: LLL has no
dependency on polynomial arithmetic, Hensel lifting is independent of LLL,
and all proof work is fully parallelizable once theorem statements are in
place.

## Project-wide proof policy

`native_decide` is banned throughout the project. Large computational
proofs must be carried by explicit verified checkers or tactics with
stable, benchmarked runtime characteristics, rather than by delegating
proof checking to `native_decide`.

`@[extern]` is allowed only for runtime hooks explicitly called for in
the SPEC. New trusted extern boundaries must not be invented during
implementation. For each approved extern, the corresponding library spec
should state the intended contract, any fallback path, and any relevant
platform assumptions.

**Property all `@[extern]` declarations must satisfy.** The C body of
every `@[extern]` declaration must do work that is not equivalent to
calling its Lean fallback. An `@[extern]` shim whose only effect is to
re-enter the Lean runtime — for example a `lean_hex_foo` whose body is
`return l_Hex_pureFoo___boxed(a, b);` — is not a valid extern boundary.
Until the C side performs work native to C (GMP call, CLMUL intrinsic,
`__uint128_t` arithmetic, etc.), ship only the pure-Lean definition
without `@[extern]`.

## Applications

**Cryptographic field construction:** To build `GF(2^128)` for AES, you
need an irreducible polynomial of degree 128 over `F_2`. With
hex-berlekamp, produce a Lean proof that it's irreducible.

**Coding theory:** Reed-Solomon and BCH codes need irreducible polynomials
over finite fields. Verified factoring provides certified generator
polynomials.

**Number theory:** Computing rings of integers requires factoring
polynomials over Z. The Baanen et al. project currently delegates to
SageMath with unverified certificates — this replaces that dependency.

**Cryptanalysis:** LLL is the core tool for lattice-based attacks. A
verified LLL gives confidence in attack results.

## Navigation

- [Design principles](design-principles.md)
- [Lean 4 stdlib inventory](lean4-stdlib-inventory.md)
- [Libraries](Libraries/) (DAG + per-library docs)
- [Tutorials](tutorials.md)
- [Testing](testing.md)
- [Benchmarking](benchmarking.md)
- [CI](CI.md)
- [Prior art](prior-art.md)
- [Future work](future-work.md)
