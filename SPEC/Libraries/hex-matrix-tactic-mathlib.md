# hex-matrix-tactic-mathlib

Mathlib matrix literal conversion, correspondence proofs, and adapters for
[hex-matrix-tactic](hex-matrix-tactic.md). The companion implements the
Mathlib-facing `det`, `rank`, and `char_poly` operations while leaving the
numeric producers and generic frontend protocol in the Mathlib-free library.
This is a specification; adapter names below are proposed unless explicitly
listed as existing in the source inventory.

## Dependencies and ownership

`HexMatrixTacticMathlib` depends on `HexMatrixTactic`, `HexMatrixMathlib`,
`HexBareissMathlib`, `HexRowReduceMathlib`, `HexCharPolyMathlib`, and the
planned `HexRankMathlib`, plus Mathlib. `HexDeterminantMathlib` and
`HexPolyMathlib` are transitive dependencies. Numeric support has no
`HexReflect` dependency. A future symbolic integration library sits above
both frontend and reflection companions; no reverse edge is permitted.

The namespace is `HexMatrixTacticMathlib`, with proposed modules
`Literal`, `Model`, `Det`, `Rank`, `CharPoly`, and opt-in `MathlibAdapters`.
The umbrella imports the ordinary frontends. Importing the explicit adapter
module enables Hex in Mathlib's machinery without changing the baseline
comparison by accident. This companion is not `correspondence_only`: it owns
literal recognition, Meta registrations, conformance and fresh-module proof
probes. Its benchmark contract and fixtures are specified in the base SPEC.
It has no Mathlib-importing compiled bench executable.

## Literal reconstruction

Enumerate every `(i,j)` in row-major order for concrete `Fin n`, `Fin m`:

- `!![…]` matrix notation;
- `Matrix.of ![…]` with each row a concrete vector;
- `fun i j => …` when evaluation at each concrete index is supported;
- `Matrix.ofArray xs h`, with the exact size witness.

Unfold reducible wrappers and let bindings within a documented budget.
Do not require that enumeration itself is definitionally equal to a literal:
prove each interpreted Hex entry equals the original `A i j`. Symbolic
entries use one downstream reflection session; closed entries use the numeric
model. Failure reports its row and column. Shape checks include empty rows and
columns and must not infer the width of a zero-row matrix from its first row.

Let `e := HexMatrixMathlib.matrixEquiv`. The reconstruction API includes the
following **new** theorem shapes, using public Hex accessors:

```text
ofArray_eq (B : Hex.Matrix R n m) (xs : Array R)
  (hsize : xs.size = n*m)
  (hentries : ∀ i : Fin n, ∀ j : Fin m,
    (Matrix.ofArray xs hsize) i j = B[(i,j)]) :
  Matrix.ofArray xs hsize = e B

matrix_eq (B : Hex.Matrix C n m) (φ : C →+* R)
  (hentries : ∀ i j, φ (B[(i,j)]) = A i j) :
  (e B).map φ = A
```

The first also gets an entry-array specialization whose hypothesis reads the
flat offset `i.val*m+j.val`, with its bound derived from `hsize`; the second
has a same-carrier identity specialization. `Matrix.ofArray` is a constructor,
not an equivalence. Reuse its entry lemma and `ofArray_ofFn`; never introduce
an `ofArray`-to-Hex `Equiv` that forgets a length condition. The shared batch
certificate replaces the characteristic-polynomial-specific inductive literal
witnesses and works for rectangular matrices too.

## Statements and scalar domains

The goal forms accept:

```text
by det        : Matrix.det A = e
by rank       : A.rank = r        (also A.rank ≤ r and r ≤ A.rank)
by char_poly  : A.charpoly = p
```

The corresponding term forms return `{ value, proof }` with proof types
`A.det = value`, `A.rank = value`, and `A.charpoly = value`.
Names have no `hex_` prefix. Result reconstruction proves agreement with the
user's expression, not merely a printed numeral or polynomial. Preserve
existing `char_poly` compatibility as described in the base SPEC.

For an integer matrix, integer rank means rank after the injective cast to
`Rat`. To close a target using Mathlib's integer `A.rank`, compose with the
domain-to-fraction-field rank preservation theorem specified by
[hex-rank-mathlib](hex-rank-mathlib.md#scalar-extension). That theorem is
planned; existing `hnfRank_eq_rank` concerns module rank over `Int` and alone
does not establish the cast convention. A first field-only path can certify
the explicitly cast rational matrix using existing row-reduction correctness;
the direct integer target needs the scalar-extension bridge.

For rational literals in `ℝ` or `ℂ`, prove entry equalities to the image of a
rational matrix using `norm_num`, check its certificate in `Rat`, and transport
through the injective rational embedding. For determinant/characteristic
polynomial the operation-preserving map suffices; rank uses injectivity and
minor/column soundness. This avoids kernel reduction of classical equality.
It is support of a fixed closed literal fragment, not arbitrary real or
complex computation.

## Certificate adapters

**Determinant value.** A proposed `det_eq_of_check` adapter composes an input
reconstruction with a checked Hex determinant value and operation
correspondence. For direct Bareiss replay its premises include
`[CommRing C] [DecidableEq C]`, a quotient `q`,
`∀ a b, b ≠ 0 → q (a*b) b = a`, and the kernel-proved equality
`Hex.Matrix.bareissWith q B = d`. Its conclusion is `A.det = φ d` when
`(e B).map φ = A`. A certificate path instead uses the relevant check's
soundness theorem. A Berkowitz constant-coefficient adapter includes the
`(-1)^n` sign for Mathlib's `det(X I - A)` convention.

`HexMatrixMathlib.bareissWith_eq_mathlib_det` is **producer correctness**
for any `CommRing` with `DecidableEq` and the stated exact-quotient law; it
does not assume `IsDomain` or `Nontrivial` explicitly. The trivial ring is
handled separately, and in a nontrivial ring the quotient law implies the
needed cancellation. Mathlib's `Echelon.Decomposition.rank_eq` is instead
**certificate soundness** over a domain. It makes no claim that a particular
Bareiss producer returns a valid certificate. These are different theorems,
and neither is a replacement for the other.

**Rank certificate.** A proposed `rank_eq_of_check` consumes the two-sided
certificate of `HexRank`: a selected nonzero minor (certified via its scaled
inverse/adjugate) and an identity expressing all columns through the selected
columns. Reuse the planned `HexRankMathlib.checkRank_sound` and
`checkRank_sound_map` adapters with their domain and injective-map hypotheses;
do not implement a second rank checker here. Expose lower-bound and
upper-bound adapters for clients that hold only the corresponding witness.
These prove Mathlib `Matrix.rank` equalities/inequalities without reconstructing
Mathlib's full elimination matrix.

**Echelon predicates.** For `E : Hex.Matrix.IsEchelonForm B D`, define the
pivot function to be `D.pivotCols[i]` on the first `D.rank` rows and `⊤`
afterwards. A proposed `isPivotedBy_of_echelon` requires both:

1. `E.HasNonzeroPivots`;
2. every entry strictly before the named pivot in each pivot row is zero.

Then `(e D.echelon).IsPivotedBy pivot` follows from these, sorted pivots and
zero trailing rows. `IsRowReduced` provides nonzero pivots over a nontrivial
ring, but still needs condition 2. For example `B = D.echelon = [1,1]` with
identity transform and the sole pivot named in column 1 satisfies the Hex
RREF fields yet is not pivoted in Mathlib's sense at column 1.
Conversely, `IsPivotedBy` and a sorted list of its finite pivots supply the
entry-shape fields; Hex's transform and inverse witnesses must be provided
separately. It does not assert reduced pivots or zero entries above them.

**Decomposition.** A proposed `decomposition_of_check` takes the original
matrix, a row permutation `σ`, a lower-triangular `L` with nonzero diagonal,
and a checked equation `L * A.submatrix σ id = e D.echelon`, together with
the preceding pivot proof. It builds the pinned `Echelon.Decomposition A`;
its `rank_eq` yields the pivot count. Do not pass `D.transform` as `L`
unconditionally: Hex's invertible transform can contain swaps and operations
above pivots and need not be lower triangular. Conversely, a domain
`Decomposition` need not have a ring-invertible transform (its diagonal is
nonzero, not necessarily a unit); conversion to Hex field row-reduction data
needs scalar extension/invertibility and extra reduction work. General
rank-certificate/decomposition conversions belong to `HexRankMathlib`, as
specified there; this frontend consumes them rather than asserting that the
data structures are definitionally interchangeable.

## Mathlib integration

The opt-in `@[bareiss_ext]` declaration has the actual pinned type
`Mathlib.Tactic.Echelon.BareissExt`, whose sole field is
`producer? : Expr → MetaM (Option Producer)`. A `Producer` takes
`Array (Array Expr)` and returns `BareissData Expr` containing `L`, ordered
row swaps, and pivot columns. Implement a Hex-backed producer returning that
shape, including the lower-triangular transform and restoration of any row
scaling. The determinant-only `Hex.Matrix.bareiss` result cannot supply it;
use or extend the rectangular producer to retain the needed transform, with
these obligations verified by Mathlib's certificate builder.

Reuse the same computation model and quotation used by Hex's own frontend.
Unsupported carriers return `none`. Mathlib then checks the pivot condition
of `L * A.submatrix σ id`, triangularity and nonzero diagonal by kernel
`decide`. A faster producer alone does not remove its documented matrix
multiplication bottleneck. The independent Hex `rank` can use the smaller
certificate, but `bareiss_ext` cannot replace Mathlib's certificate checker.

The pinned `norm_rank` calls `checkBareissApplicable` before model selection:
`CommRing`, `IsDomain`, and reduction of the decidable test `1 = 0` to false.
This is a probe for kernel-decidable zero equality, not a proof that every
entry equality reduces. All actual conditions still have to check. Registering
a model therefore does not enable `norm_rank` on classical `ℝ`/`ℂ`, composite
moduli, or arbitrary symbolic atoms. Those supported Hex cases use the
independent frontend and proved interpretation instead.

The pinned `norm_det` has no analogous producer registry. Supply an opt-in
Hex determinant simproc/Meta adapter that returns a `Simp.Result` with the
same `Matrix.det` rewrite contract, using `det_eq_of_check`. Compose it in an
explicit simp set with `norm_det` as fallback (try Hex first, then the stock
simproc on decline). Preserve unmodified `norm_det`/`eval_det` for standalone
use and comparison; do not claim `bareiss_ext` extends determinant or replace
Mathlib's declaration by a same-named declaration. Test both fallback and
Hex-selected paths.

## Closed algebraic benchmark

Use `α = √2` in the real embedding of `Q(√2)` and
`A = !![α, 1; 1, α]`. Its determinant is `1`, rank is `2`, and characteristic
polynomial is `X² - 2α X + 1`. Repeat as diagonal blocks, then add fixed
rational off-block couplings to exercise full computation. The computable
model represents `a + bα` as a rational pair, multiplies modulo `α² = 2`,
and proves its embedding using `Real.sq_sqrt` with `0 ≤ 2` and the
irreducibility/injectivity evidence needed for field operations and rank.
Use both an explicit number-field presentation and its real-algebraic image;
the registered provider must prove the relation, not infer it from spelling.

`norm_det` normalizes the determinant as a ring expression, treating `√2`
as an atom; its ring normalizer does not by itself use the algebraic relation.
Measure raw `norm_det` output and whether it closes the target. For a complete
proof comparator also measure `eval_det` followed by the explicitly supplied
`α² = 2` normalization, including that normalization's cost. Raw `norm_rank`
on `ℝ` is inapplicable at the equality check: record that result, and compare
rank on the computable number-field model when its kernel equality is
supported. Do not turn inapplicability into an infinite speedup. Run the Hex
standalone real frontend and the computable-carrier comparator as separately
labelled arms. This family tests closed algebraic reduction without waiting
for `hex-reflect`.

## Verified source inventory

Paths below are relative to the repository, or to `.lake/packages/mathlib/`
for Mathlib. The pin in `lake-manifest.json` is
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. These existing declarations were
checked in that source; proposed adapters elsewhere in this SPEC are not
claims about the current API.

| Existing Mathlib declaration | File and checked contract |
|---|---|
| `Matrix.ofArray`, `ofArray_apply`, `ofArray_ofFn` | `Mathlib/LinearAlgebra/Matrix/Defs.lean`: flat array plus `size = m*n`, row-major access, reconstruction of a `Fin` matrix; no ring assumptions. |
| `Mathlib.Tactic.Echelon.BareissExt`, `Producer`, `BareissData`, `RingOps`, `mkProducer`, `bareiss_ext` | `Mathlib/Tactic/Echelon/Core.lean`: model lookup, nested-array producer, transform/swaps/pivots, arithmetic/preparation/restoration/quotation, and Meta registration attribute. |
| `checkBareissApplicable`, `checkKernelDecide`, `mkCertificate`, `producerFor` | `Mathlib/Tactic/Echelon/Bareiss.lean`: domain applicability before dispatch; three kernel-decided certificate conditions; first supported extension then rational fallback. |
| `Echelon.Decomposition`, `Echelon.Decomposition.rank_eq` | `Mathlib/LinearAlgebra/Matrix/Echelon/Decomposition.lean`: namespace is root `Echelon`, not `Matrix.Echelon`; `[CommRing R] [IsDomain R]`, finite linearly ordered indices; rank equals the number of finite pivots. |
| `Matrix.IsPivotedBy` | `Mathlib/LinearAlgebra/Matrix/Echelon/Pivot.lean`: `[Zero R]`, ordered indices, row-echelon shape and leading nonzero entries; its rank theorem additionally assumes a domain and finite indices. |
| `norm_det`, `eval_det` | `Mathlib/Tactic/NormDet.lean`: concrete square `Fin` matrix literals over `CommRing`, Bird determinant and certificate-chain normalization from `Mathlib/Tactic/Determinant/Bird/Cert.lean`; symbolic ring entries allowed. |
| `norm_rank`, `eval_rank` | `Mathlib/Tactic/NormRank.lean`: non-symbolic literal matrices, applicability check then Bareiss certificate; supporting parsing and numeric models in `Mathlib/Tactic/Echelon/{Parsing,Rat,Zsqrtd}.lean`; certificate construction is in `Bareiss.lean`, not a separate `Echelon/Cert.lean` file. |
| `Real.sq_sqrt` | `Mathlib/Analysis/Real/Sqrt.lean`: `(√x)^2 = x` requires `0 ≤ x`. |

| Existing Hex declaration | File and checked contract |
|---|---|
| `HexMatrixMathlib.matrixEquiv` | `HexMatrixMathlib/Basic.lean`: Hex/Mathlib `Fin` matrix equivalence, no ring assumptions. |
| `HexMatrixMathlib.det_eq` | `HexDeterminantMathlib/CoreTransport.lean`: `[CommRing R]`, `Hex.Matrix.det B = Matrix.det (matrixEquiv B)`. |
| `HexMatrixMathlib.bareissWith_eq_mathlib_det` | `HexBareissMathlib/Bareiss.lean`: `[CommRing R] [DecidableEq R]` and `∀ a b, b ≠ 0 → quot (a*b) b = a`; arbitrary square Hex matrix. |
| `HexMatrixMathlib.bareiss_eq_mathlib_det` | Same file: specialization to `Int` and exact integer quotient. |
| `HexMatrixMathlib.rank_eq` | `HexRowReduceMathlib/RankSpanNullspace.lean`: `[Field R]`, `E : Hex.Matrix.IsRowReduced M D` implies `D.rank = (matrixEquiv M).rank`; not a theorem about arbitrary echelon data or arbitrary rings. |
| `hnfRank_eq_rank` in namespace `HexHermiteMathlib` | `HexHermiteMathlib/Rank.lean`: integer HNF rank equals Mathlib module rank over `Int`; contextual inventory, not an added Hermite dependency. |
| `HexCharPolyMathlib.equiv_charPoly` | `HexCharPolyMathlib/Basic.lean`: `[CommRing R] [DecidableEq R]`, dense-polynomial equivalence sends `Hex.Matrix.charPoly B` to `(matrixEquiv B).charpoly`. |
| `Hex.Matrix.RowEchelonData`, `IsEchelonForm`, `IsRowReduced`, `IsEchelonForm.HasNonzeroPivots` | `HexRowReduce/RowEchelon/Contracts.lean`: transform witnesses, sorted columns, zeros below pivots/trailing rows; nonzero pivots and leading-entry conditions must be distinguished as above. |

## Verification obligations

- Build the numeric base without Mathlib or reflection; check the import DAG.
- Check every literal syntax and empty/rectangular boundary; alter an entry,
  dimension, modulus and interpretation instance to test rejection.
- Prove all new reconstruction and certificate adapters with their stated
  hypotheses; test the nonleading-pivot counterexample and a nontriangular
  transform so the echelon adapter cannot silently assume stronger contracts.
- Test determinant signs in odd and even dimensions, rank inequalities in both
  directions, integer/rational cast agreement, real/complex rational literals,
  finite prime and composite carriers, and characteristic polynomials beyond
  `Int`. Negative targets and unresolved conditions must not close.
- Verify the shared model through both the standalone Hex frontend and the
  `bareiss_ext` adapter. Record stock comparator, adapter and standalone costs
  separately under the base SPEC's Phase-4 fixtures and ceilings.
- Preserve existing `char_poly` numeric examples and proof strategy, migrate
  import paths without cycles or duplicate elaborators, and audit axiom sets.
