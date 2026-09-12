# hex-matrix-mathlib (depends on hex-matrix + Mathlib)

Base Mathlib bridge for the matrix family: proves that our dense matrix type and
its elementary operations correspond to Mathlib's abstract linear algebra.

Mathlib's matrices are function-based and its rank/kernel/span are noncomputable
(cardinals, infima over submodules). This bridge connects our computable
representation to Mathlib's, starting from the matrix equivalence and the
elementary-row-operation dictionary. The row-reduction, determinant, and Bareiss
correspondences build on this base in `HexRowReduceMathlib`,
`HexDeterminantMathlib`, and `HexBareissMathlib` respectively.

**Matrix equivalence:**
```lean
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R
```
Its forward map is `fun M i j => M[(i, j)]` — built on the public entry API, not
on the (now-opaque) backing representation, so the equivalence is unaffected by a
representation change.

**Row operations correspond to Mathlib transvections / elementary matrices:**
Our `rowAdd M i j c` is left-multiplication by `Matrix.transvection i j c`; our
`rowSwap` and `rowScale` correspond to Mathlib's `Matrix.swap` permutation matrix
and a diagonal matrix respectively:
```lean
theorem matrixEquiv_rowSwap  (M : Hex.Matrix R n m) (i j : Fin n) : ...
theorem matrixEquiv_rowScale (M : Hex.Matrix R n m) (i : Fin n) (c : R) : ...
theorem matrixEquiv_rowAdd   (M : Hex.Matrix R n m) (src dst : Fin n) (c : R) : ...
```

These give the base dictionary through which the determinant and rank bridges
transfer Mathlib theorems (Cramer's rule, Cayley-Hamilton, rank-nullity,
`diagonal_transvection_induction`) to our matrices.

**Algebraic instances and equivalence upgrades:**
`Hex.Matrix` carries the Mathlib algebraic tower whose operations are the
executable ones (entrywise `+`/`-`/`•` from the `Vector` representation, the
`ofFn` zero/identity, and the executable matrix product). The instances are
transported along `matrixEquiv` (so the laws come from Mathlib's `Matrix`):

```lean
instance [AddCommMonoid R] : AddCommMonoid (Hex.Matrix R n m)
instance [AddCommGroup R]  : AddCommGroup (Hex.Matrix R n m)
instance [Semiring R]      : Module R (Hex.Matrix R n m)
instance [Semiring R]      : Semiring (Hex.Matrix R n n)
instance [Ring R]          : Ring (Hex.Matrix R n n)
instance [CommSemiring R]  : Algebra R (Hex.Matrix R n n)
```

`matrixEquiv` upgrades to the matching bundled equivalences:

```lean
def matrixAddEquiv    [AddCommMonoid R] : Hex.Matrix R n m ≃+ Matrix (Fin n) (Fin m) R
def matrixLinearEquiv [Semiring R]      : Hex.Matrix R n m ≃ₗ[R] Matrix (Fin n) (Fin m) R
def matrixRingEquiv   [Semiring R]      : Hex.Matrix R n n ≃+* Matrix (Fin n) (Fin n) R
def matrixAlgEquiv    [CommSemiring R]  : Hex.Matrix R n n ≃ₐ[R] Matrix (Fin n) (Fin n) R
```

with `@[simp]` transport lemmas (`matrixEquiv_add`, `matrixEquiv_mul`,
`matrixEquiv_smul`, `matrixEquiv_one`, …) feeding `simp`/`grind`.

**Operation correspondence across the equivalence:**
The vector equivalence and the basic container API also cross `matrixEquiv`:

```lean
def vectorEquiv : Vector R n ≃ (Fin n → R)
theorem vectorEquiv_mulVec    : vectorEquiv (M * v) = (matrixEquiv M).mulVec (vectorEquiv v)
theorem matrixEquiv_transpose : matrixEquiv Mᵀ = (matrixEquiv M)ᵀ
theorem matrixEquiv_setRow    : matrixEquiv (setRow M i v) = (matrixEquiv M).updateRow i (vectorEquiv v)
theorem matrixEquiv_setCol    : matrixEquiv (setCol M j v) = (matrixEquiv M).updateCol j v
theorem matrixEquiv_gramMatrix         : matrixEquiv (gramMatrix M) = matrixEquiv M * (matrixEquiv M)ᵀ
theorem matrixEquiv_principalSubmatrix : matrixEquiv (principalSubmatrix M k hk) = (matrixEquiv M).submatrix (Fin.castLE hk) (Fin.castLE hk)
```

(plus `matrixEquiv_takeRows`).

## Matrix literals

`HexMatrixMathlib/Literal.lean` is the literal layer the matrix tactics
share ([SPEC/matrix-tactics.md](../../SPEC/matrix-tactics.md) §Placement);
no tactic lives here.

```lean
def vecOfList [Zero α] : (k : Nat) → List α → (Fin k → α)
def ofLists [Zero α] (n m : Nat) (L : List (List α)) : Matrix (Fin n) (Fin m) α
theorem ofLists_apply (L) (i : Fin n) (j : Fin m) : ofLists n m L i j = (L.getD i []).getD j 0
def entriesEq [Zero α] [DecidableEq α] (n m) (A : Matrix (Fin n) (Fin m) α) (L) : Bool
theorem eq_ofLists_of_entriesEq (h : entriesEq n m A L = true) : A = ofLists n m L
structure Certified (f : α → β) (a : α) where value : β; proof : f a = value
```

A tactic accepts a closed matrix in four syntaxes, possibly behind
definitions unfolded within a budget of eight, and identifies it with the
row list `L` of its entries by one of two routes:

| syntax | route | cost at `16 × 16` |
|---|---|---|
| `!![…]`, `Matrix.of ![…]` | definitional: `vecOfList (k + 1) (a :: l)` unfolds to `vecCons a (vecOfList k l)`, so `A = ofLists n m L` is `rfl`, one unfolding per entry | 6 ms |
| `fun i j => …`, `Matrix.ofArray xs h` | one kernel `decide` on `entriesEq n m A L`, which evaluates `A i j` at every index pair | about 200 ms |

The definitional route is the primary one: the kernel never evaluates an
entry through `Matrix.of` and `vecCons` inside a certificate's arithmetic.
The meta section (`HexMatrixMathlib.Literal`) recognizes the shape and
carrier from the type (`shape?`), the literal behind definitions
(`matchLiteral?`, returning the dimensions, carrier, row-major entry
expressions and the route), evaluates entries with Mathlib's
`evalRatEntry` (`evalEntries`), quotes row lists (`rowList`), builds the
identification proof along the route (`identification`) and elaborates a
term-form argument with an integer expectation for the `!![…]` notations
(`elabArgument`). `Certified` is the record the `%` term forms return.
The empty shapes `!![]`, `!![,,,]` and `!![;;;]` are literals of their
dimensions. Tests: `HexMatrixMathlib/Tests.lean` identifies each syntax and
the empty shapes with its row list.


### Requests from structural tactic frontends

The [structural tactic contracts](../../SPEC/matrix-tactics.md#placement)
request the following extensions to this shared layer before the relevant
numeric handler ships. They are requirements, not descriptions of current
`Literal.lean` capabilities:

- Field-aware `%` argument elaboration, preserving the expected carrier
  rather than defaulting every unannotated literal to integers.
- Rational and prime-residue entry codecs with proved decoding/arithmetic
  agreement and coherent field instances. Rational codecs preserve a `Rat`
  input row list for definitional literal identification and certify its
  agreement with integer rows and a positive common scale, following
  `checkDetRat`'s boundary. Algorithm-specific products and polynomial checks
  remain in their owning libraries.
- Closed vector/factor-function literal recognition with a `vecOfList`
  identification theorem, for RHSs, stated solutions, lattice members and
  invariant-factor targets. Match the matrix layer's supported unfolding and
  diagnostic discipline.

These adapters serve `min_poly`, `smith`, `hermite`, `inverse` and `solve`;
they introduce no shared tactic dispatcher or new library. Polynomial-target
recognition is requested separately against hex-poly-mathlib.
