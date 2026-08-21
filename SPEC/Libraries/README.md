# Libraries

- **hex-basic**: small Mathlib-free standard-library shims, including kernel-reducible array and vector operations
- **hex-arith**: extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- **hex-primality**: Miller-Rabin compositeness witnesses, Pocklington certificates, a kernel-reducible sieve and stored initial segment, the `primality` tactic
- **hex-int-factor**: integer factorization with complete prime-exponent certificates, the divisor-function API, multiplicative order and primitive roots
- **hex-poly**: dense `Array`-backed polynomial representation
- **hex-mv-poly**: canonical distributed multivariate polynomials at fixed arity with explicit monomial orders
- **hex-mv-gcd**: multivariate gcd with cofactors, content and primitive part, exact division, squarefree decomposition
- **hex-truncated-series**: power series truncated at a precision fixed in the type, with Newton inversion, square root, `exp`, `log`, composition, and reversion
- **hex-matrix**: dense matrices, matrix/vector arithmetic, elementary row and column operations, submatrix slicing, the Gram matrix
- **hex-row-reduce**: row reduction (RREF), rank, span, nullspace
- **hex-determinant**: the Leibniz determinant and its cofactor/Cauchy-Binet/Plücker theory
- **hex-bareiss**: the fraction-free Bareiss determinant algorithm
- **hex-char-poly**: the characteristic polynomial by the division-free Samuelson-Berkowitz algorithm, over any commutative ring
- **hex-hermite**: Hermite normal form over `Int`, unimodular transforms, integer lattice membership, integer kernel bases
- **hex-smith**: Smith normal form over `Int`, invariant factors, and the structure of a finitely generated abelian group
- **hex-poly-smith**: Smith normal form over `F[x]`, monic pivot normalization, unimodular transforms with inverses, and the structure of a finitely generated `F[x]`-module
- **hex-gram-schmidt**: Gram-Schmidt orthogonalization, GS coefficients, Gram determinants, update formulas under row operations
- **hex-mod-arith**: `ZMod64 p`, `UInt64`-backed arithmetic in `Z/pZ`
- **hex-modular**: integer CRT, rational reconstruction, symmetric representatives, and the modulus supply
- **hex-modular-matrix**: multi-modular determinant, certified rank, and Dixon p-adic linear solving over `Q`
- **hex-finite-field**: the Mathlib-free `F_q` interface (characteristic, degree, Frobenius, indexing), the generic `q`-power Frobenius and Frobenius matrix
- **hex-poly-fp**: polynomials over `F_p`, Frobenius map, square-free decomposition, lazy reduction for small p
- **hex-gf2**: packed bitwise polynomials over `F_2` (XOR + CLMUL), `GF(2^n)` elements
- **hex-poly-z**: polynomials over `Z`, content/primitive part, Mignotte bound
- **hex-poly-z-gcd**: modular gcd for `Z[x]` with cofactors, a coprimality witness, and exact division
- **hex-roots**: certified complex root isolation for `Z[x]` via dyadic squares, Pellet tests, and speculative Newton iteration
- **hex-real-roots**: certified real root isolation for `Z[x]`: Sturm-count witnesses, a Descartes bisection search with a proven-complete Sturm fallback
- **hex-interval**: exact open, closed, empty, and unbounded dyadic intervals; a shared expression program; and a budgeted scheduler for propagation, refinement, and subdivision
- **hex-interval-algebraic**: planned Mathlib-facing integration of interval facts with certified real and complex polynomial root isolation; `mathlib: true`
- **hex-rcf**: the `rcf` tactic, a complete decision procedure for univariate real-closed-field sentences (Boolean combinations of polynomial inequalities under one `∀`/`∃` over `ℝ`); `mathlib: true`, soundness theorem in the same library
- **hex-resultant**: polynomial resultant and discriminant via the subresultant pseudo-remainder sequence
- **hex-number-field**: fixed fields `QAdjoin p x`, factorization-lazy `AlgebraicRoot`, canonical `AlgebraicNumber`, and roots of polynomials with algebraic coefficients
- **hex-number-field-tower**: successive number-field extensions, Trager factorization, adjoining roots, splitting fields, and primitive-element flattening
- **hex-berlekamp**: Berlekamp factoring, distinct-degree and equal-degree factorization (Cantor-Zassenhaus), and the Rabin irreducibility test over any `F_q`; the `factor_poly` / `irreducibility` tactic drivers (native `FpPoly p` arms plus extensions for other input types)
- **hex-hensel**: Hensel lifting from `mod p` to `mod p^k`
- **hex-lll**: LLL lattice basis reduction
- **hex-berlekamp-zassenhaus**: complete factoring of `Z[x]`; the `Hex.ZPoly` extension for `factor_poly` / `irreducibility`
- **hex-conway**: Conway polynomial database
- **hex-gfq-ring**: canonical quotient ring `F_p[x]/(f)` by a nonconstant modulus
- **hex-gfq-field**: field structure on top of `hex-gfq-ring` when `f` is irreducible
- **hex-gfq**: convenience wrapper, canonical `GFq p n` plus optimized `GF2q n` using Conway polynomials

**Mathlib companion libraries** (each depends on a computational library and
Mathlib, and supplies correspondence proofs or Mathlib-facing APIs):

- **hex-mod-arith-mathlib**: `ZMod64 p ≃+* ZMod p`
- **hex-modular-mathlib**: CRT agreement with `ZMod.chineseRemainder`, and the rational-reconstruction statements over `ℚ`
- **hex-modular-matrix-mathlib**: Hadamard's inequality discharged, `det` = `Matrix.det`, rank = `Matrix.rank`, and the solve and kernel correspondences
- **hex-poly-z-gcd-mathlib**: gcd divisibility and maximality in `Polynomial ℤ`, and `Decidable (a ∣ b)`
- **hex-primality-mathlib**: `Hex.Nat.Prime ↔ Nat.Prime`, the `norm_num` extension, and segment statements over `Finset.filter Nat.Prime`
- **hex-int-factor-mathlib**: agreement with `Nat.factorization`, `Decidable (Squarefree n)`, and `orderOf` in `(ZMod n)ˣ`
- **hex-finite-field-mathlib**: `Fintype K` and `Fintype.card K = card K` for any `LawfulFiniteField`, and `frob = frobenius`
- **hex-poly-mathlib**: `DensePoly R ≃+* Polynomial R`
- **hex-mv-poly-mathlib**: `MvPoly n R cmp ≃+* MvPolynomial (Fin n) R`, `aeval`, and operation correspondence
- **hex-mv-gcd-mathlib**: gcd maximality transported to `MvPolynomial (Fin n) R`, and decidable divisibility and squarefreeness
- **hex-truncated-series-mathlib**: `TSeries R n ≃+* PowerSeries R ⧸ (X ^ n)`, and agreement with `PowerSeries.invOfUnit`, `subst`, `substInvOfIsUnit`, `exp`, and `logOf`
- **hex-matrix-mathlib**: matrix equivalence, row operations as transvections, and the Mathlib algebra tower transported onto our matrix type
- **hex-row-reduce-mathlib**: rank = `Matrix.rank`, nullspace = `LinearMap.ker`, span agreement
- **hex-determinant-mathlib**: `det` agreement with `Matrix.det`, plus the Plücker / Desnanot-Jacobi assembly
- **hex-bareiss-mathlib**: Bareiss determinant = `Matrix.det`, via the bordered-minor invariant
- **hex-char-poly-mathlib**: agreement with `Matrix.charpoly`, Cayley-Hamilton, the trace and determinant coefficients, transpose and similarity invariance
- **hex-hermite-mathlib**: row lattice = `Submodule.span ℤ`, integer rank = `Matrix.rank`, and an executable basis of the kernel submodule
- **hex-smith-mathlib**: the executable output as `Module.Basis.SmithNormalForm`, the divisibility chain Mathlib's structure omits, and the quotient structure theorem
- **hex-poly-smith-mathlib**: the executable polynomial matrix over `Polynomial F`, `Module.Basis.SmithNormalForm` from the executable output, monic as Mathlib's `normalize`, and the quotient structure theorem
- **hex-gram-schmidt-mathlib**: `GramSchmidt.Int.basis` = Mathlib's `gramSchmidt`
- **hex-poly-z-mathlib**: `DensePoly Int ≃+* Polynomial ℤ`, Mignotte bound (via Mathlib's Mahler measure)
- **hex-roots-mathlib**: Pellet's test on circles (built from `circleIntegral`), the Mahler separation bound, soundness of refinement and `isolate`
- **hex-real-roots-mathlib**: Sturm's theorem (counting form over `Polynomial ℝ`), chain correspondence, soundness and completeness of `isolate?`
- **hex-interval-mathlib**: real semantics, verified arithmetic and elementary-function propagators, certificate replay, and the `interval` tactic
- **hex-resultant-mathlib**: executable resultant agreement with `Polynomial.resultant`, specialization, root-product, and discriminant theorems
- **hex-number-field-mathlib**: fixed-field correspondence, exactification, lazy arithmetic, and algebraic-coefficient root completeness
- **hex-number-field-tower-mathlib**: tower embeddings, Trager correctness, splitting fields, and primitive-element equivalence
- **hex-poly-fp-mathlib**: `FpPoly p ≃+* Polynomial (ZMod p)`, and the transport of coefficients, degree, monicity, and ring operations across it
- **hex-berlekamp-mathlib**: `Decidable (Irreducible f)` for `Polynomial (ZMod p)`; the `Polynomial (ZMod p)` extension for `factor_poly` / `irreducibility`
- **hex-hensel-mathlib**: Hensel correctness, uniqueness, `coprime_mod_p_lifts`
- **hex-lll-mathlib**: lattice = `Submodule ℤ`, short vector bound
- **hex-gf2-mathlib**: `GF2Poly ≃+* FpPoly 2`, `GF2n`/`GF2nPoly ≃+* FiniteField 2 f hf hirr`, packed-field finiteness/cardinality
- **hex-gfq-mathlib**: finiteness/cardinality for quotient fields, and `GFq p n ≃+* GaloisField p n`
- **hex-berlekamp-zassenhaus-mathlib**: unconditional factoring correctness, `Decidable (Irreducible f)` for `Polynomial ℤ`; the `Polynomial ℤ` and strong `Hex.ZPoly` extensions for `factor_poly` / `irreducibility`

## Implementation dependencies

Each library with its immediate dependencies:

- **hex-basic**: (none)
- **hex-arith**: (none)
- **hex-primality**: hex-arith, hex-basic
- **hex-int-factor**: hex-primality, hex-arith, hex-basic
- **hex-poly**: (none)
- **hex-mv-poly**: hex-poly, hex-basic
- **hex-mv-gcd**: hex-mv-poly, hex-poly, hex-poly-fp, hex-resultant, hex-arith, hex-mod-arith
- **hex-truncated-series**: hex-basic
- **hex-matrix**: hex-basic
- **hex-row-reduce**: hex-matrix
- **hex-determinant**: hex-matrix
- **hex-bareiss**: hex-determinant, hex-matrix
- **hex-char-poly**: hex-matrix, hex-poly
- **hex-hermite**: hex-row-reduce, hex-arith, hex-determinant
- **hex-smith**: hex-hermite
- **hex-poly-smith**: hex-poly, hex-matrix, hex-determinant
- **hex-mod-arith**: hex-arith
- **hex-modular**: hex-arith
- **hex-modular-matrix**: hex-modular, hex-matrix, hex-row-reduce, hex-determinant, hex-mod-arith, hex-arith, hex-basic
- **hex-finite-field**: hex-arith, hex-mod-arith, hex-poly, hex-poly-fp, hex-matrix, hex-basic
- **hex-gram-schmidt**: hex-row-reduce, hex-determinant, hex-bareiss
- **hex-lll**: hex-gram-schmidt, hex-matrix, hex-basic
- **hex-poly-fp**: hex-poly, hex-mod-arith
- **hex-poly-z**: hex-poly, hex-arith, hex-basic
- **hex-poly-z-gcd**: hex-poly-z, hex-poly-fp, hex-poly, hex-modular, hex-mod-arith, hex-arith, hex-resultant
- **hex-roots**: hex-poly-z
- **hex-real-roots**: hex-poly-z
- **hex-interval**: (none)
- **hex-interval-algebraic**: hex-interval-mathlib, hex-real-roots-mathlib, hex-roots-mathlib (mathlib: true)
- **hex-rcf**: hex-real-roots, hex-real-roots-mathlib, hex-poly-z, hex-poly-z-mathlib (mathlib: true)
- **hex-resultant**: hex-poly
- **hex-number-field**: hex-poly-z, hex-roots, hex-resultant, hex-berlekamp-zassenhaus, hex-matrix, hex-row-reduce
- **hex-number-field-tower**: hex-number-field, hex-resultant, hex-berlekamp-zassenhaus, hex-row-reduce
- **hex-berlekamp**: hex-poly-fp, hex-matrix, hex-row-reduce, hex-gfq-ring, hex-basic, hex-finite-field
- **hex-hensel**: hex-poly-fp, hex-poly-z, hex-basic
- **hex-conway**: hex-berlekamp
- **hex-gfq-ring**: hex-poly-fp
- **hex-gfq-field**: hex-gfq-ring, hex-finite-field
- **hex-gfq**: hex-gfq-field, hex-conway, hex-gf2
- **hex-gf2**: hex-poly, hex-basic, hex-finite-field
- **hex-berlekamp-zassenhaus**: hex-berlekamp, hex-hensel, hex-lll

Mathlib companion libraries (each also depends on Mathlib):

- **hex-mod-arith-mathlib**: hex-mod-arith
- **hex-modular-mathlib**: hex-modular, hex-mod-arith-mathlib
- **hex-modular-matrix-mathlib**: hex-modular-matrix, hex-matrix-mathlib, hex-determinant-mathlib, hex-row-reduce-mathlib, hex-modular-mathlib
- **hex-primality-mathlib**: hex-primality
- **hex-int-factor-mathlib**: hex-int-factor, hex-primality-mathlib
- **hex-finite-field-mathlib**: hex-finite-field, hex-mod-arith-mathlib, hex-poly-mathlib
- **hex-poly-mathlib**: hex-poly
- **hex-mv-poly-mathlib**: hex-mv-poly, hex-poly-mathlib
- **hex-mv-gcd-mathlib**: hex-mv-gcd, hex-mv-poly-mathlib, hex-resultant-mathlib, hex-poly-mathlib
- **hex-truncated-series-mathlib**: hex-truncated-series
- **hex-poly-z-mathlib**: hex-poly-z, hex-poly-mathlib
- **hex-poly-z-gcd-mathlib**: hex-poly-z-gcd, hex-poly-z-mathlib, hex-poly-mathlib
- **hex-roots-mathlib**: hex-roots, hex-poly-z-mathlib
- **hex-real-roots-mathlib**: hex-real-roots, hex-poly-z-mathlib
- **hex-interval-mathlib**: hex-interval
- **hex-resultant-mathlib**: hex-resultant, hex-poly-mathlib
- **hex-number-field-mathlib**: hex-number-field, hex-resultant-mathlib, hex-berlekamp-zassenhaus-mathlib, hex-roots-mathlib, hex-poly-z-mathlib
- **hex-number-field-tower-mathlib**: hex-number-field-tower, hex-number-field-mathlib, hex-resultant-mathlib, hex-berlekamp-zassenhaus-mathlib, hex-row-reduce-mathlib
- **hex-matrix-mathlib**: hex-matrix
- **hex-row-reduce-mathlib**: hex-row-reduce, hex-matrix-mathlib
- **hex-determinant-mathlib**: hex-determinant, hex-bareiss, hex-matrix-mathlib
- **hex-bareiss-mathlib**: hex-determinant-mathlib
- **hex-char-poly-mathlib**: hex-char-poly, hex-matrix-mathlib, hex-poly-mathlib, hex-determinant-mathlib
- **hex-hermite-mathlib**: hex-hermite, hex-row-reduce-mathlib, hex-determinant-mathlib
- **hex-smith-mathlib**: hex-smith, hex-hermite-mathlib
- **hex-poly-smith-mathlib**: hex-poly-smith, hex-poly-mathlib, hex-matrix-mathlib, hex-determinant-mathlib
- **hex-gram-schmidt-mathlib**: hex-gram-schmidt, hex-bareiss-mathlib
- **hex-lll-mathlib**: hex-lll, hex-gram-schmidt-mathlib, hex-row-reduce-mathlib
- **hex-poly-fp-mathlib**: hex-poly-fp, hex-poly-mathlib, hex-mod-arith-mathlib
- **hex-berlekamp-mathlib**: hex-berlekamp, hex-poly-mathlib, hex-mod-arith-mathlib, hex-poly-fp-mathlib
- **hex-hensel-mathlib**: hex-hensel, hex-poly-mathlib
- **hex-gf2-mathlib**: hex-gf2, hex-poly-fp, hex-gfq-field, hex-poly-fp-mathlib
- **hex-gfq-mathlib**: hex-gfq
- **hex-berlekamp-zassenhaus-mathlib**: hex-berlekamp-zassenhaus, hex-poly-z-mathlib

LLL is the recombination primitive used by Berlekamp-Zassenhaus: BZ
encodes its lifted local factors as a lattice basis and calls
`hex-lll`'s reduced-basis and short-vector functions. The two
libraries can still be developed in parallel until BZ recombination is
implemented, but the dependency of `hex-berlekamp-zassenhaus` on
`hex-lll` is part of the production graph, not an optional
optimisation.

The modular libraries split along their dependency seams. `hex-modular`
holds the reconstruction arithmetic that a matrix consumer and a
polynomial consumer both need, so it sits below both. `hex-modular-matrix`
and `hex-poly-z-gcd` each sit above it beside the type they compute with,
and neither depends on the other. `hex-mv-gcd` gains a dependency on
`hex-poly-z-gcd`, which is its arity-one case, once that library exists.
The reasoning is in [hex-modular §Why not inside hex-arith](hex-modular.md)
and [hex-poly-z-gcd §Why this is not hex-mv-gcd at arity one](hex-poly-z-gcd.md).

## Library DAG

The matrix family splits internally. `hex-matrix` is the dense base.
`hex-row-reduce`, `hex-determinant`, and `hex-bareiss` build on it
(`hex-bareiss` also on `hex-determinant`), `hex-gram-schmidt` uses all
three, and `hex-lll` builds on `hex-gram-schmidt`. `hex-hermite` reuses
the row-echelon and determinant layers and depends on `hex-arith` for the
extended GCD; `hex-smith` sits on top of it. `hex-poly-smith` is the other
member with a dependency outside the family, on `hex-poly` for the
polynomial Euclidean operations. Each has a matching `*-mathlib` companion
of the same shape. In the diagram below, `hex-matrix` stands for that whole
family.

The integer normal forms within it:

```text
hex-row-reduce ───┐
hex-arith ─────────┼── hex-hermite ── hex-smith
hex-determinant ───┘
```

`hex-char-poly` sits on the matrix family too, with `hex-poly` rather
than `hex-arith` as its dependency outside it, as `hex-poly-smith` below
also does. The Samuelson-Berkowitz
algorithm computes no determinant, so `hex-determinant` is not among its
computational dependencies. Its companion does depend on
`hex-determinant-mathlib`, because the correspondence with
`Matrix.charpoly` is a statement about a determinant. The reasoning is in
[hex-char-poly §What the Mathlib-free layer does not establish](hex-char-poly.md).

```text
hex-matrix ──────────────┐
                         ├── hex-char-poly ──┐
hex-poly ────────────────┘                   │
                                             │
hex-matrix-mathlib ──────┐                   │
hex-poly-mathlib ────────┼───────────────────┴── hex-char-poly-mathlib
hex-determinant-mathlib ─┘
```

The polynomial normal form is a sibling rather than a descendant. It
shares the subject with `hex-smith` and none of the code: the base ring
is `F[x]`, the units are the nonzero constants, and there is no
polynomial Hermite normal form underneath it. The comparison is drawn
row by row in [hex-poly-smith.md](hex-poly-smith.md).

```text
hex-poly ────────┐
hex-matrix ──────┼── hex-poly-smith
hex-determinant ─┘
```

The algebraic graph has three independent roots: hex-poly, hex-arith,
and hex-matrix. The module-boundary helpers in hex-basic are an
additional utility root used across the graph.

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

`hex-finite-field` holds the `F_q` interface class and the prime-field
instance; the extension-field and packed-`GF(2^n)` instances live at
their own types, in `hex-gfq-field` and `hex-gf2`. Splitting class from
instance is what keeps the graph acyclic: `hex-gfq-field` sits above
`hex-berlekamp` (through the conformance and bench drivers that build
its irreducibility witnesses), so a library holding both the class and
the extension-field instance could not be written against by
`hex-berlekamp`. The reasoning is in
[hex-finite-field §Placement in the DAG](hex-finite-field.md).

```text
hex-arith ─── hex-mod-arith ─── hex-poly-fp ───┐
hex-poly ──────────────────────────────────────┼── hex-finite-field
hex-matrix ────────────────────────────────────┘        │
                                                        ├── hex-berlekamp
                                                        ├── hex-gfq-field (instance)
                                                        └── hex-gf2       (instance)
```

Number-field extensions:

```text
hex-resultant ───────────────┐
hex-number-field ────────────┼── hex-number-field-tower
hex-berlekamp-zassenhaus ────┤
hex-row-reduce ──────────────┘
```

The computational interval pair is independent. Its planned algebraic adapter
joins the Mathlib-facing interval layer to the existing root-isolation graph:

```text
hex-interval ── hex-interval-mathlib ──┐
hex-real-roots-mathlib ────────────────┼── hex-interval-algebraic
hex-roots-mathlib ─────────────────────┘
```

Multivariate polynomials extend the univariate polynomial library and
use `hex-basic` for the current module-boundary reduction shims:

```text
hex-basic ─────────────────┐
                           ├── hex-mv-poly ──────────────┐
hex-poly ──────────────────┘                             ├── hex-mv-poly-mathlib
     └──────────────────────── hex-poly-mathlib ─────────┘
```

`hex-mv-gcd` sits on `hex-mv-poly` and pulls in three further libraries:
`hex-poly-fp` and `hex-mod-arith` for the univariate images over `F_p`
that its modular routes compute, `hex-resultant` for the subresultant
fallback, and `hex-arith` for the integer extended GCD.

```text
hex-mv-poly ──── hex-mv-gcd ──── hex-mv-gcd-mathlib
```

`hex-truncated-series` sits directly on `hex-basic` and names no
polynomial type. That is what keeps the fast-arithmetic corner acyclic.
Newton inversion of a truncated series is the primitive under fast
polynomial division, and fast polynomial division is a fact about
`DensePoly`, so the two meet in the planned `hex-poly-fast`, which
depends on both. Putting the `DensePoly` conversion inside
`hex-truncated-series` instead would make hex-poly's own fast division
depend on it and hex-truncated-series depend on hex-poly, which has no
valid publication order in
[`scripts/release/released.yml`](../../scripts/release/released.yml).

```text
hex-basic ── hex-truncated-series ── hex-truncated-series-mathlib

hex-truncated-series ──┐
                       ├── hex-poly-fast (planned)
hex-poly ──────────────┘
```

`hex-primality` sits directly on `hex-arith`, which owns the
`Hex.Nat.Prime` predicate, Fermat's little theorem, and the modular
exponentiation its checkers replay. The predicate stays there rather
than moving up, because `hex-mod-arith` builds `ZMod64.PrimeModulus`
on it and depends only on `hex-arith`.

`hex-int-factor` sits on `hex-primality` in turn, and that direction is
forced: a factorization certificate has to prove each listed factor
prime, while a certificate search needs no proof at all, so the
primality library owns the small untrusted partial factorization its
own search needs and the factorization library owns the rest.

```text
hex-arith ──── hex-primality ──── hex-int-factor
                    │                   │
      hex-primality-mathlib   hex-int-factor-mathlib
```

## Index

Libraries marked **(released)** are published as standalone
repositories; see
[PLAN/Releases.md §Published libraries](../../PLAN/Releases.md#published-libraries).
SPEC files for libraries already under development live with the
library source (`HexFoo/SPEC/hex-foo.md`) when they have moved there. This
directory also contains centralized specifications for planned libraries and
for developments whose source-local move has not happened yet.

- [hex-basic](https://github.com/leanprover/hex-basic) (released): small Mathlib-free standard-library shims, including kernel-reducible array and vector operations
- [hex-arith](../../HexArith/SPEC/hex-arith.md): extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- [hex-primality.md](hex-primality.md): Miller-Rabin compositeness witnesses, Pocklington certificates, a kernel-reducible sieve and stored initial segment, the `primality` tactic (the Mathlib companion is specified in the same file)
- [hex-int-factor.md](hex-int-factor.md): integer factorization with complete prime-exponent certificates, the divisor-function API, multiplicative order and primitive roots (the Mathlib companion is specified in the same file)
- [hex-matrix](https://github.com/leanprover/hex-matrix/blob/main/SPEC/hex-matrix.md) (released): dense matrices, arithmetic, elementary row/column operations, submatrix slicing, the Gram matrix
- [hex-row-reduce](https://github.com/leanprover/hex-row-reduce/blob/main/SPEC/hex-row-reduce.md) (released): row reduction, rank, span, nullspace
- [hex-determinant](https://github.com/leanprover/hex-determinant/blob/main/SPEC/hex-determinant.md) (released): Leibniz determinant and cofactor/Cauchy-Binet/Plücker theory
- [hex-bareiss](https://github.com/leanprover/hex-bareiss/blob/main/SPEC/hex-bareiss.md) (released): fraction-free Bareiss determinant algorithm
- [hex-matrix-mathlib](https://github.com/leanprover/hex-matrix-mathlib/blob/main/SPEC/hex-matrix-mathlib.md) (released): matrix equivalence, row operations as transvections, transported algebra tower
- [hex-row-reduce-mathlib](https://github.com/leanprover/hex-row-reduce-mathlib/blob/main/SPEC/hex-row-reduce-mathlib.md) (released): rank/nullspace/span correspondence
- [hex-determinant-mathlib](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md) (released): `det` agreement with `Matrix.det`
- [hex-bareiss-mathlib](https://github.com/leanprover/hex-bareiss-mathlib/blob/main/SPEC/hex-bareiss-mathlib.md) (released): Bareiss determinant correctness
- [hex-char-poly.md](hex-char-poly.md): the characteristic polynomial by the division-free Samuelson-Berkowitz algorithm, with Cayley-Hamilton and the `Matrix.charpoly` correspondence (the Mathlib companion is specified in the same file)
- [hex-hermite.md](hex-hermite.md): Hermite normal form over `Int`, unimodular transforms, integer lattice membership and kernel bases (the Mathlib companion is specified in the same file)
- [hex-smith.md](hex-smith.md): Smith normal form over `Int`, invariant factors, and abelian group structure (the Mathlib companion is specified in the same file)
- [hex-poly-smith.md](hex-poly-smith.md): Smith normal form over `F[x]`, monic pivot normalization, unimodular transforms with inverses, and `F[x]`-module structure (the Mathlib companion is specified in the same file)
- [hex-mod-arith](../../HexModArith/SPEC/hex-mod-arith.md): `ZMod64 p`, `UInt64`-backed arithmetic in `Z/pZ`
- [hex-finite-field.md](hex-finite-field.md): the Mathlib-free `F_q` interface, the generic `q`-power Frobenius, and the equal-degree stage (Cantor-Zassenhaus) it makes worthwhile, specified as hex-berlekamp amendments
- [hex-mod-arith-mathlib](../../HexModArithMathlib/SPEC/hex-mod-arith-mathlib.md): `ZMod64 p ≃+* ZMod p`
- [hex-modular.md](hex-modular.md): integer CRT, rational reconstruction, symmetric representatives, and the modulus supply (the Mathlib companion is specified in the same file)
- [hex-modular-matrix.md](hex-modular-matrix.md): multi-modular determinant, certified rank, and Dixon p-adic linear solving (the Mathlib companion is specified in the same file)
- [hex-poly](../../HexPoly/SPEC/hex-poly.md): dense polynomial library, operations, GCD, CRT
- [hex-poly-mathlib](../../HexPolyMathlib/SPEC/hex-poly-mathlib.md): `DensePoly R ≃+* Polynomial R`
- [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md): canonical distributed multivariate polynomials with explicit monomial orders
- [hex-mv-poly-mathlib](../../HexMvPolyMathlib/SPEC/hex-mv-poly-mathlib.md): `MvPoly n R cmp ≃+* MvPolynomial (Fin n) R`, `aeval`, and operation correspondence
- [hex-mv-gcd](hex-mv-gcd.md): multivariate gcd with cofactors, content and primitive part, exact division, squarefree decomposition
- [hex-truncated-series.md](hex-truncated-series.md): power series truncated at a precision fixed in the type, Newton inversion, square root, `exp`, `log`, composition, and reversion (the Mathlib companion is specified in the same file)
- [hex-poly-fp](../../HexPolyFp/SPEC/hex-poly-fp.md): polynomials over `F_p`, Frobenius, square-free decomposition
- [hex-gf2](../../HexGF2/SPEC/hex-gf2.md): packed bitwise polynomials over `F_2`, `GF(2^n)` elements
- [hex-gf2-mathlib](../../HexGF2Mathlib/SPEC/hex-gf2-mathlib.md): `GF2Poly ≃+* FpPoly 2`, `GF2n`/`GF2nPoly ≃+* FiniteField 2 f hf hirr`, packed-field finiteness/cardinality
- [hex-poly-fp-mathlib](../../HexPolyFpMathlib/SPEC/hex-poly-fp-mathlib.md): `FpPoly p ≃+* Polynomial (ZMod p)`, the crossing point to Mathlib's polynomial type
- [hex-poly-z](../../HexPolyZ/SPEC/hex-poly-z.md): polynomials over `Z`, content/primitive part, Mignotte bound
- [hex-poly-z-mathlib](../../HexPolyZMathlib/SPEC/hex-poly-z-mathlib.md): Mignotte bound proof via Mathlib's Mahler measure
- [hex-poly-z-gcd.md](hex-poly-z-gcd.md): modular gcd for `Z[x]` with cofactors, a coprimality witness, and exact division (the Mathlib companion is specified in the same file)
- [hex-roots.md](../../HexRoots/SPEC/hex-roots.md): certified complex root isolation for `Z[x]`
- [hex-roots-mathlib](../../HexRootsMathlib/SPEC/hex-roots-mathlib.md): Pellet's test on circles, the Mahler separation bound, soundness of refinement and `isolate`
- [hex-real-roots.md](../../HexRealRoots/SPEC/hex-real-roots.md): certified real root isolation for `Z[x]`, Sturm-count witnesses, Descartes search with Sturm fallback
- [hex-real-roots-mathlib.md](../../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md): Sturm's theorem, chain correspondence, soundness and completeness of `isolate?`
- [hex-interval.md](../../HexInterval/SPEC/hex-interval.md): exact interval data, shared programs, and budgeted propagation search
- [hex-interval-mathlib.md](hex-interval-mathlib.md): real semantics, verified propagators, proof replay, and the `interval` tactic
- **hex-interval-algebraic** (planned): Mathlib-facing interval providers backed by certified real and complex polynomial root isolation; its provider contract is specified in [hex-interval.md](../../HexInterval/SPEC/hex-interval.md#specialized-algebraic-solvers-before-generic-propagation)
- [hex-rcf.md](hex-rcf.md): the `rcf` tactic for univariate real-closed-field sentences
- [hex-resultant](../../HexResultant/SPEC/hex-resultant.md): polynomial resultant and discriminant via the subresultant pseudo-remainder sequence
- [hex-resultant-mathlib](../../HexResultantMathlib/SPEC/hex-resultant-mathlib.md): executable resultant agreement, specialization, root-product, and discriminant theorems
- [hex-number-field](../../HexNumberField/SPEC/hex-number-field.md): `QAdjoin`, factorization-lazy `AlgebraicRoot`, canonical `AlgebraicNumber`, and algebraic-coefficient roots
- [hex-number-field-mathlib](../../HexNumberFieldMathlib/SPEC/hex-number-field-mathlib.md): fixed-field correspondence, exactification, lazy arithmetic, and root completeness
- [hex-number-field-tower](../../HexNumberFieldTower/SPEC/hex-number-field-tower.md): successive extensions, Trager factorization, splitting fields, and flattening
- [hex-number-field-tower-mathlib.md](../../HexNumberFieldTowerMathlib/SPEC/hex-number-field-tower-mathlib.md): semantic towers, factorization correctness, splitting, and primitive-element equivalence
- [hex-berlekamp](../../HexBerlekamp/SPEC/hex-berlekamp.md): Berlekamp factoring, Rabin irreducibility test, and the `factor_poly` / `irreducibility` tactic drivers
- [hex-berlekamp-mathlib](../../HexBerlekampMathlib/SPEC/hex-berlekamp-mathlib.md): Berlekamp/Rabin correctness proofs via Euclidean domain theory, and the `Polynomial (ZMod p)` tactic extension
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
- [hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md): complete factoring of `Z[x]`, and the `Hex.ZPoly` tactic extension
- [hex-berlekamp-zassenhaus-mathlib](../../HexBerlekampZassenhausMathlib/SPEC/hex-berlekamp-zassenhaus-mathlib.md): unconditional factoring correctness, and the `Polynomial ℤ` tactic extension
