# Libraries

- **hex-arith**: extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- **hex-poly**: dense `Array`-backed polynomial representation
- **hex-matrix**: dense matrices, matrix/vector arithmetic, elementary row and column operations, submatrix slicing, the Gram matrix
- **hex-row-reduce**: row reduction (RREF), rank, span, nullspace
- **hex-determinant**: the Leibniz determinant and its cofactor/Cauchy-Binet/Plücker theory
- **hex-bareiss**: the fraction-free Bareiss determinant algorithm
- **hex-gram-schmidt**: Gram-Schmidt orthogonalization, GS coefficients, Gram determinants, update formulas under row operations
- **hex-mod-arith**: `ZMod64 p`, `UInt64`-backed arithmetic in `Z/pZ`
- **hex-poly-fp**: polynomials over `F_p`, Frobenius map, square-free decomposition, lazy reduction for small p
- **hex-gf2**: packed bitwise polynomials over `F_2` (XOR + CLMUL), `GF(2^n)` elements
- **hex-poly-z**: polynomials over `Z`, content/primitive part, Mignotte bound
- **hex-roots**: certified complex root isolation for `Z[x]` via dyadic squares, Pellet tests, and speculative Newton iteration
- **hex-real-roots**: certified real root isolation for `Z[x]`: Sturm-count witnesses, a Descartes bisection search with a proven-complete Sturm fallback
- **hex-rcf**: the `rcf` tactic, a complete decision procedure for univariate real-closed-field sentences (Boolean combinations of polynomial inequalities under one `∀`/`∃` over `ℝ`); `mathlib: true`, soundness theorem in the same library
- **hex-resultant**: polynomial resultant and discriminant via the subresultant pseudo-remainder sequence
- **hex-number-field**: fixed fields `QAdjoin p x`, factorization-lazy `AlgebraicRoot`, canonical `AlgebraicNumber`, and roots of polynomials with algebraic coefficients
- **hex-number-field-tower**: successive number-field extensions, Trager factorization, adjoining roots, splitting fields, and primitive-element flattening
- **hex-berlekamp**: Berlekamp factoring and Rabin irreducibility test over `F_p`
- **hex-hensel**: Hensel lifting from `mod p` to `mod p^k`
- **hex-lll**: LLL lattice basis reduction
- **hex-berlekamp-zassenhaus**: complete factoring of `Z[x]`, initially with exhaustive recombination
- **hex-conway**: Conway polynomial database
- **hex-gfq-ring**: canonical quotient ring `F_p[x]/(f)` by a nonconstant modulus
- **hex-gfq-field**: field structure on top of `hex-gfq-ring` when `f` is irreducible
- **hex-gfq**: convenience wrapper, canonical `GFq p n` plus optimized `GF2q n` using Conway polynomials

**Mathlib companion libraries** (each depends on a computational
library and Mathlib, and proves that the executable definitions agree
with Mathlib's):

- **hex-mod-arith-mathlib**: `ZMod64 p ≃+* ZMod p`
- **hex-poly-mathlib**: `DensePoly R ≃+* Polynomial R`
- **hex-matrix-mathlib**: matrix equivalence, row operations as transvections, and the Mathlib algebra tower transported onto our matrix type
- **hex-row-reduce-mathlib**: rank = `Matrix.rank`, nullspace = `LinearMap.ker`, span agreement
- **hex-determinant-mathlib**: `det` agreement with `Matrix.det`, plus the Plücker / Desnanot-Jacobi assembly
- **hex-bareiss-mathlib**: Bareiss determinant = `Matrix.det`, via the bordered-minor invariant
- **hex-gram-schmidt-mathlib**: `GramSchmidt.Int.basis` = Mathlib's `gramSchmidt`
- **hex-poly-z-mathlib**: `DensePoly Int ≃+* Polynomial ℤ`, Mignotte bound (via Mathlib's Mahler measure)
- **hex-roots-mathlib**: Pellet's test on circles (built from `circleIntegral`), the Mahler separation bound, soundness of refinement and `isolate`
- **hex-real-roots-mathlib**: Sturm's theorem (counting form over `Polynomial ℝ`), chain correspondence, soundness and completeness of `isolate?`
- **hex-resultant-mathlib**: executable resultant agreement with `Polynomial.resultant`, specialization, root-product, and discriminant theorems
- **hex-number-field-mathlib**: fixed-field correspondence, exactification, lazy arithmetic, and algebraic-coefficient root completeness
- **hex-number-field-tower-mathlib**: tower embeddings, Trager correctness, splitting fields, and primitive-element equivalence
- **hex-berlekamp-mathlib**: `Decidable (Irreducible f)` for `Polynomial (ZMod p)`
- **hex-hensel-mathlib**: Hensel correctness, uniqueness, `coprime_mod_p_lifts`
- **hex-lll-mathlib**: lattice = `Submodule ℤ`, short vector bound
- **hex-gf2-mathlib**: `GF2Poly ≃+* FpPoly 2`, `GF2n`/`GF2nPoly ≃+* FiniteField 2 f hf hirr`, packed-field finiteness/cardinality
- **hex-gfq-mathlib**: finiteness/cardinality for quotient fields, and `GFq p n ≃+* GaloisField p n`
- **hex-berlekamp-zassenhaus-mathlib**: unconditional factoring correctness, `Decidable (Irreducible f)` for `Polynomial ℤ`

## Implementation dependencies

Each library with its immediate dependencies:

- **hex-arith**: (none)
- **hex-poly**: (none)
- **hex-matrix**: (none)
- **hex-row-reduce**: hex-matrix
- **hex-determinant**: hex-matrix
- **hex-bareiss**: hex-determinant, hex-matrix
- **hex-mod-arith**: hex-arith
- **hex-gram-schmidt**: hex-row-reduce, hex-determinant, hex-bareiss
- **hex-lll**: hex-gram-schmidt, hex-matrix
- **hex-poly-fp**: hex-poly, hex-mod-arith
- **hex-poly-z**: hex-poly
- **hex-roots**: hex-poly-z
- **hex-real-roots**: hex-poly-z
- **hex-rcf**: hex-real-roots, hex-real-roots-mathlib, hex-poly-z, hex-poly-z-mathlib (mathlib: true)
- **hex-resultant**: hex-poly
- **hex-number-field**: hex-poly-z, hex-roots, hex-resultant, hex-berlekamp-zassenhaus, hex-matrix, hex-row-reduce
- **hex-number-field-tower**: hex-number-field, hex-resultant, hex-berlekamp-zassenhaus, hex-row-reduce
- **hex-berlekamp**: hex-poly-fp, hex-matrix, hex-gfq-ring
- **hex-hensel**: hex-poly-fp, hex-poly-z
- **hex-conway**: hex-berlekamp
- **hex-gfq-ring**: hex-poly-fp
- **hex-gfq-field**: hex-gfq-ring
- **hex-gfq**: hex-gfq-field, hex-conway, hex-gf2
- **hex-gf2**: hex-poly
- **hex-berlekamp-zassenhaus**: hex-berlekamp, hex-hensel, hex-lll

Mathlib companion libraries (each also depends on Mathlib):

- **hex-mod-arith-mathlib**: hex-mod-arith
- **hex-poly-mathlib**: hex-poly
- **hex-poly-z-mathlib**: hex-poly-z, hex-poly-mathlib
- **hex-roots-mathlib**: hex-roots, hex-poly-z-mathlib
- **hex-real-roots-mathlib**: hex-real-roots, hex-poly-z-mathlib
- **hex-resultant-mathlib**: hex-resultant, hex-poly-mathlib
- **hex-number-field-mathlib**: hex-number-field, hex-resultant-mathlib, hex-berlekamp-zassenhaus-mathlib, hex-roots-mathlib, hex-poly-z-mathlib
- **hex-number-field-tower-mathlib**: hex-number-field-tower, hex-number-field-mathlib, hex-resultant-mathlib, hex-berlekamp-zassenhaus-mathlib, hex-row-reduce-mathlib
- **hex-matrix-mathlib**: hex-matrix
- **hex-row-reduce-mathlib**: hex-row-reduce, hex-matrix-mathlib
- **hex-determinant-mathlib**: hex-determinant, hex-bareiss, hex-matrix-mathlib
- **hex-bareiss-mathlib**: hex-determinant-mathlib
- **hex-gram-schmidt-mathlib**: hex-gram-schmidt, hex-bareiss-mathlib
- **hex-lll-mathlib**: hex-lll, hex-gram-schmidt-mathlib, hex-row-reduce-mathlib
- **hex-berlekamp-mathlib**: hex-berlekamp, hex-poly-mathlib, hex-mod-arith-mathlib
- **hex-hensel-mathlib**: hex-hensel, hex-poly-mathlib
- **hex-gf2-mathlib**: hex-gf2, hex-poly-fp, hex-gfq-field
- **hex-gfq-mathlib**: hex-gfq
- **hex-berlekamp-zassenhaus-mathlib**: hex-berlekamp-zassenhaus, hex-poly-z-mathlib

LLL is the recombination primitive used by Berlekamp-Zassenhaus: BZ
encodes its lifted local factors as a lattice basis and calls
`hex-lll`'s reduced-basis and short-vector functions. The two
libraries can still be developed in parallel until BZ recombination is
implemented, but the dependency of `hex-berlekamp-zassenhaus` on
`hex-lll` is part of the production graph, not an optional
optimisation.

## Library DAG

The matrix family splits internally: `hex-matrix` is the dense base;
`hex-row-reduce`, `hex-determinant`, and `hex-bareiss` build on it
(`hex-bareiss` also on `hex-determinant`); `hex-gram-schmidt` uses all
three; and `hex-lll` builds on `hex-gram-schmidt`. Each has a matching
`*-mathlib` companion of the same shape. In the diagram below,
`hex-matrix` stands for that whole family.

Three independent roots: hex-poly, hex-arith, hex-matrix.

```
      hex-poly     hex-arith      hex-matrix
       /     \          |           /       \
      /       \     hex-mod-arith  /  hex-gram-schmidt
     /         \       /          /         |
hex-poly-z  hex-poly-fp          /       hex-lll
     \        /       |         /         /
     hex-hensel  hex-gfq-ring  /         /
               \       |      /         /
                \  hex-berlekamp       /
                 \      |             /
                  hex-berlekamp-zassenhaus
```

Additional libraries (finite field construction, GF(2)):
```
hex-poly ── hex-gf2

hex-gfq-ring
     |
hex-gfq-field   hex-conway   hex-gf2
       \        /           /
        \      /           /
         \    /           /
            hex-gfq
```

Number-field extensions:

```text
hex-resultant ───────────────┐
hex-number-field ────────────┼── hex-number-field-tower
hex-berlekamp-zassenhaus ────┤
hex-row-reduce ──────────────┘
```

## Index

Libraries marked **(released)** are published as standalone
repositories; see
[PLAN/Releases.md §Published libraries](../../PLAN/Releases.md#published-libraries).
SPEC files for libraries already under development live with the
library source (`HexFoo/SPEC/hex-foo.md`); SPECs kept in this directory
belong to planned libraries not yet started.

- [hex-arith](../../HexArith/SPEC/hex-arith.md): extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- [hex-matrix](https://github.com/leanprover/hex-matrix/blob/main/SPEC/hex-matrix.md) (released): dense matrices, arithmetic, elementary row/column operations, submatrix slicing, the Gram matrix
- [hex-row-reduce](https://github.com/leanprover/hex-row-reduce/blob/main/SPEC/hex-row-reduce.md) (released): row reduction, rank, span, nullspace
- [hex-determinant](https://github.com/leanprover/hex-determinant/blob/main/SPEC/hex-determinant.md) (released): Leibniz determinant and cofactor/Cauchy-Binet/Plücker theory
- [hex-bareiss](https://github.com/leanprover/hex-bareiss/blob/main/SPEC/hex-bareiss.md) (released): fraction-free Bareiss determinant algorithm
- [hex-matrix-mathlib](https://github.com/leanprover/hex-matrix-mathlib/blob/main/SPEC/hex-matrix-mathlib.md) (released): matrix equivalence, row operations as transvections, transported algebra tower
- [hex-row-reduce-mathlib](https://github.com/leanprover/hex-row-reduce-mathlib/blob/main/SPEC/hex-row-reduce-mathlib.md) (released): rank/nullspace/span correspondence
- [hex-determinant-mathlib](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md) (released): `det` agreement with `Matrix.det`
- [hex-bareiss-mathlib](https://github.com/leanprover/hex-bareiss-mathlib/blob/main/SPEC/hex-bareiss-mathlib.md) (released): Bareiss determinant correctness
- [hex-mod-arith](../../HexModArith/SPEC/hex-mod-arith.md): `ZMod64 p`, `UInt64`-backed arithmetic in `Z/pZ`
- [hex-mod-arith-mathlib](../../HexModArithMathlib/SPEC/hex-mod-arith-mathlib.md): `ZMod64 p ≃+* ZMod p`
- [hex-poly](../../HexPoly/SPEC/hex-poly.md): dense polynomial library, operations, GCD, CRT
- [hex-poly-mathlib](../../HexPolyMathlib/SPEC/hex-poly-mathlib.md): `DensePoly R ≃+* Polynomial R`
- [hex-poly-fp](../../HexPolyFp/SPEC/hex-poly-fp.md): polynomials over `F_p`, Frobenius, square-free decomposition
- [hex-gf2](../../HexGF2/SPEC/hex-gf2.md): packed bitwise polynomials over `F_2`, `GF(2^n)` elements
- [hex-gf2-mathlib](../../HexGF2Mathlib/SPEC/hex-gf2-mathlib.md): `GF2Poly ≃+* FpPoly 2`, `GF2n`/`GF2nPoly ≃+* FiniteField 2 f hf hirr`, packed-field finiteness/cardinality
- [hex-poly-z](../../HexPolyZ/SPEC/hex-poly-z.md): polynomials over `Z`, content/primitive part, Mignotte bound
- [hex-poly-z-mathlib](../../HexPolyZMathlib/SPEC/hex-poly-z-mathlib.md): Mignotte bound proof via Mathlib's Mahler measure
- [hex-roots.md](hex-roots.md): certified complex root isolation for `Z[x]`
- [hex-roots-mathlib](../../HexRootsMathlib/SPEC/hex-roots-mathlib.md): Pellet's test on circles, the Mahler separation bound, soundness of refinement and `isolate`
- [hex-real-roots.md](hex-real-roots.md): certified real root isolation for `Z[x]`, Sturm-count witnesses, Descartes search with Sturm fallback
- [hex-real-roots-mathlib.md](hex-real-roots-mathlib.md): Sturm's theorem, chain correspondence, soundness and completeness of `isolate?`
- [hex-rcf.md](hex-rcf.md): the `rcf` tactic for univariate real-closed-field sentences
- [hex-resultant.md](hex-resultant.md): polynomial resultant and discriminant via the subresultant pseudo-remainder sequence
- [hex-resultant-mathlib.md](hex-resultant-mathlib.md): executable resultant agreement, specialization, root-product, and discriminant theorems
- [hex-number-field.md](hex-number-field.md): `QAdjoin`, factorization-lazy `AlgebraicRoot`, canonical `AlgebraicNumber`, and algebraic-coefficient roots
- [hex-number-field-mathlib.md](hex-number-field-mathlib.md): fixed-field correspondence, exactification, lazy arithmetic, and root completeness
- [hex-number-field-tower.md](hex-number-field-tower.md): successive extensions, Trager factorization, splitting fields, and flattening
- [hex-number-field-tower-mathlib.md](hex-number-field-tower-mathlib.md): semantic towers, factorization correctness, splitting, and primitive-element equivalence
- [hex-berlekamp](../../HexBerlekamp/SPEC/hex-berlekamp.md): Berlekamp factoring and Rabin irreducibility test
- [hex-berlekamp-mathlib](../../HexBerlekampMathlib/SPEC/hex-berlekamp-mathlib.md): Berlekamp/Rabin correctness proofs via Euclidean domain theory
- [hex-hensel](../../HexHensel/SPEC/hex-hensel.md): Hensel lifting algorithms
- [hex-hensel-mathlib](../../HexHenselMathlib/SPEC/hex-hensel-mathlib.md): Hensel correctness, uniqueness, coprimality lifting
- [hex-conway](../../HexConway/SPEC/hex-conway.md): Conway polynomial database
- [hex-gfq-ring](../../HexGFqRing/SPEC/hex-gfq-ring.md): canonical quotient ring `F_p[x]/(f)`
- [hex-gfq-field](../../HexGFqField/SPEC/hex-gfq-field.md): field structure on top of the quotient ring when `f` is irreducible
- [hex-gfq](../../HexGFq/SPEC/hex-gfq.md): convenience wrapper `GFq p n` and optimized `GF2q n` using Conway polynomials
- [hex-gfq-mathlib](../../HexGFqMathlib/SPEC/hex-gfq-mathlib.md): finiteness/cardinality for quotient fields and `GFq p n ≃+* GaloisField p n`
- [hex-gram-schmidt](https://github.com/leanprover/hex-gram-schmidt/blob/main/SPEC/hex-gram-schmidt.md) (released): Gram-Schmidt orthogonalization, coefficients, Gram determinants
- [hex-gram-schmidt-mathlib](https://github.com/leanprover/hex-gram-schmidt-mathlib/blob/main/SPEC/hex-gram-schmidt-mathlib.md) (released): correspondence with Mathlib's `gramSchmidt`
- [hex-lll](https://github.com/leanprover/hex-lll/blob/main/SPEC/hex-lll.md) (released): LLL lattice basis reduction algorithm and proofs
- [hex-lll-mathlib](https://github.com/leanprover/hex-lll-mathlib/blob/main/SPEC/hex-lll-mathlib.md) (released): lattice = `Submodule Z`, short vector bound
- [hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md): complete factoring of `Z[x]`
- [hex-berlekamp-zassenhaus-mathlib](../../HexBerlekampZassenhausMathlib/SPEC/hex-berlekamp-zassenhaus-mathlib.md): unconditional factoring correctness
