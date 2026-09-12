# hex-bareiss-mathlib (depends on hex-bareiss + hex-determinant-mathlib + Mathlib)

Mathlib bridge for `hex-bareiss`: proves the row-pivoted Bareiss determinant
correct against both Mathlib's determinant and our executable Leibniz
determinant, via the no-pivot bordered-minor invariant and the determinant
correspondence from `hex-determinant-mathlib`. The proofs are stated over an
arbitrary commutative coefficient ring with an exact quotient; `Int` is a
corollary, with no hypotheses beyond what it has today. The kernel
determinant certificate of hex-bareiss determines the determinant of a
Mathlib integer or rational matrix given as a row list, and the `det`
tactic closes determinant equalities on closed literals with it
([Kernel certificate](#kernel-certificate), [The `det` tactic](#the-det-tactic)).

This library owns no runtime search, conformance driver or compiled
benchmark. Its proof-side surface, the `det` tactic, is measured by the
fresh-module probes under `bench/HexBareissMathlib/ProofProbe` against the
unmodified pinned `eval_det`. Build-only examples live in
`HexBareissMathlib/Tests.lean`.

Computational conformance owner: `HexBareiss`.

Computational performance owner: `HexBareiss` for the producer; this library
for the tactic.

## Coefficient contract

Every theorem here takes `[CommRing R] [DecidableEq R]` (Mathlib's `CommRing`,
which supplies the `Lean.Grind.CommRing` instance the Mathlib-free layer's
`Hex.Matrix.det` needs) together with the exact quotient and its single law,
exactly as specified in
[hex-bareiss §Coefficient contract](https://github.com/leanprover/hex-bareiss/blob/main/SPEC/hex-bareiss.md):

```lean
(quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
```

No public `IsDomain`, `NoZeroDivisors` or nontriviality hypothesis appears. The
coefficient facts the development needs are supplied by
[`HexBasic/ExactDiv.lean`](https://github.com/leanprover/hex-basic/blob/main/HexBasic/ExactDiv.lean)
and apply under a Mathlib `CommRing`: the two instance paths to `Zero R` and
`Mul R` agree, so `[CommRing R] [Div R] [Hex.ExactDivLaws R]` is a usable binder
list with no diamond to work around.

Those lemmas are stated over `[Div R] [Hex.ExactDivLaws R]`, though, and the
generic theorems here carry only the unbundled `quot` and `hquot`. They do not
apply directly; the package is built locally inside each proof that needs it:

```lean
letI : Div R := ⟨quot⟩
haveI : Hex.ExactDivLaws R := ⟨hquot⟩
```

The derived facts (`mul_ne_zero`, `mul_right_cancel`) do not mention `/`, so the
local `Div` never escapes into a statement.

**One `IsDomain` instance is constructed, not assumed.**
`det_eq_zero_of_bareiss_failed_column` closes the failed-pivot branch through
Mathlib's `Matrix.exists_mulVec_eq_zero_iff`, which is stated for
`[CommRing A] [IsDomain A]`. In the nontrivial branch:

```lean
theorem isDomain_of_quot [CommRing R] (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (h1 : (1 : R) ≠ 0) :
    IsDomain R
```

built from `Nontrivial R` (out of `h1`) and `NoZeroDivisors R` (out of the
derived `mul_ne_zero`), then `NoZeroDivisors.to_isDomain`. It is a `haveI`
inside that one proof and never a binder on a public statement, which is what
makes "no public `IsDomain` hypothesis" true rather than a slogan.

`Int.mul_eq_zero` is the only named `Int` lemma this library uses today. Three
further places rely on `Int` being concrete, and each has a replacement:

| site | today | generic replacement |
|---|---|---|
| `borderedMinor_zero_column_succ_det_eq_zero_of_entries` | `Int.mul_eq_zero` on `det(borderedMinor) * prevPivot = 0` | `Hex.ExactDivLaws.mul_right_cancel` against `0 * prevPivot` |
| `bareissNoPivotInvariant_initial` | `decide` for `(1 : Int) ≠ 0` | hypothesis `(1 : R) ≠ 0`, plus a trivial-ring case split at each public theorem |
| `bareissNoPivot_eq_det` sign step | `decide` for `(if 0 % 2 = 0 then 1 else -1) = 1` | `rfl` after the `rowSwaps = 0` rewrite; not `Int`-specific in substance |
| `failedBareissColumn_at_pivot` | `norm_num` for `(-1 : Int) ^ (k + k) = 1` | `pow_mul` and `neg_one_sq` over any `CommRing` |

The no-zero-divisor property, where the development needs it, is
`Hex.ExactDivLaws.mul_ne_zero`.

**The nontriviality seed.** `BareissNoPivotInvariant` asserts
`prevPivot ≠ 0`, and the initial state has `prevPivot = 1`, so
`bareissNoPivotInvariant_initial` and `bareissPivotInvariant_initial` each gain
a hypothesis `(1 : R) ≠ 0`. It is not pushed onto the public theorems: each
opens with `by_cases h1 : (1 : R) = 0`, and in the trivial branch every element
of `R` is `0` (`by_contra` plus `Hex.one_ne_zero_of_nonzero`), so both sides of
the correctness statement are `0`:

```lean
theorem eq_zero_of_one_eq_zero [CommRing R] (h1 : (1 : R) = 0) (a : R) : a = 0 := by
  by_contra ha
  exact Hex.one_ne_zero_of_nonzero ha h1
```

Nothing is added to the shared exact-division package for this.

## No-pivot invariant and core correctness

```lean
def NonzeroBareissPivots [CommRing R] (M : Hex.Matrix R n n) : Prop :=
  ∀ k : Fin n,
    Hex.Matrix.det
      (Hex.Matrix.principalSubmatrix M (k.val + 1) (Nat.succ_le_of_lt k.isLt)) ≠ 0

structure BareissNoPivotInvariant [CommRing R]
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n) : Prop

theorem bareissNoPivotWith_eq_det [CommRing R] [DecidableEq R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (M : Hex.Matrix R n n) (h : NonzeroBareissPivots M) :
    Hex.Matrix.bareissNoPivotWith quot M = Matrix.det (matrixEquiv M)
```

`NonzeroBareissPivots` is unchanged in content: every leading principal minor up
to size `n` is nonzero.

`BareissNoPivotInvariant` stays **quotient-independent**. Its five fields
(`singular_none`, `step_le`, `prevPivot_eq`, `prevPivot_ne`, `trailing_eq`) are
purely relational between `source` and `state`, and the state stores no
quotient, so parameterizing the invariant by `quot` would add an argument no
field mentions. `quot` and `hquot` belong on the step and loop *preservation*
lemmas, which are the statements that actually run `stepMatrixWith quot`.

## Headline correspondence theorems

The preferred surface for downstream Mathlib-side callers:

```lean
theorem bareissWith_eq_det [CommRing R] [DecidableEq R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (M : Hex.Matrix R n n) :
    Hex.Matrix.bareissWith quot M = Hex.Matrix.det M

theorem bareissWith_eq_mathlib_det [CommRing R] [DecidableEq R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (M : Hex.Matrix R n n) :
    Hex.Matrix.bareissWith quot M = Matrix.det (matrixEquiv M)
```

Neither carries a nondegeneracy hypothesis: row pivoting handles the singular
case, and the zero-pivot branch is turned into `det M = 0` rather than being
excluded. `bareissWith_eq_mathlib_det` is `bareissWith_eq_det` composed with
`det_eq` (from `hex-determinant-mathlib`), so it holds outright.

**`Int` corollaries.** Today's four public theorems keep their names and
statements verbatim, and gain no new coefficient hypotheses.
`bareissNoPivot_eq_det` keeps the `NonzeroBareissPivots` premise it already has;
the other three remain premise-free:

```lean
theorem bareissNoPivot_eq_det (M : Hex.Matrix Int n n) (h : NonzeroBareissPivots M) :
    Hex.Matrix.bareissNoPivot M = Matrix.det (matrixEquiv M)

theorem bareiss_eq_mathlib_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)

theorem bareissDet_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)

theorem bareiss_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Hex.Matrix.det M
```

The first two are in `HexBareissMathlib/Bareiss.lean`; `bareissDet_eq_det` and
`bareiss_eq_det` are in the umbrella `HexBareissMathlib.lean`, which is where
they must stay.

Each is the generic theorem instantiated at `quot := Hex.Matrix.exactDiv`, whose
law is `Int.mul_ediv_cancel`. `Hex.Matrix.bareiss` is by definition
`bareissWith Hex.Matrix.exactDiv`, so these are applications, not restatements.
Nothing downstream (`HexGramSchmidtMathlib/Update.lean`,
`HexGramSchmidtMathlib/Int/RowAdd.lean`) needs to change.

**Other carriers.** No carrier-specific determinant correspondence theorem is
needed. At every supported carrier, the only extra proof supplied at the use
site is the exact-quotient law

```lean
fun a b hb => Hex.exactDiv_mul_right a hb
```

with instances obtained as follows:

| carrier | source of `[Div R] [Hex.ExactDivLaws R]` | additional assumptions |
|---|---|---|
| `Rat` | core division plus `Hex.instExactDivLawsField` | none |
| `ZMod64 p` | `HexPolyFp.PrimeField` plus `Hex.instExactDivLawsField` | `[ZMod64.Bounds p] [ZMod64.PrimeModulus p]` |
| `DensePoly F` | polynomial division and `Hex.instExactDivLawsDensePoly` from `HexResultant.ExactDiv` | `[Lean.Grind.Field F] [DecidableEq F]` |
| `ZPoly` | the same dense-polynomial instance over `Hex.instExactDivLawsInt` | none |
| `MvPoly n R cmp` | `Hex.MvPoly.instDiv` and `Hex.MvPoly.instExactDivLaws` from `HexMvGcd.Divide` | the lawful coefficient-GCD and monomial-order context listed in the `hex-bareiss` carrier table |

These instance-law terms are compile-time guards in the carrier integration
modules, not new correspondence APIs in this library. The already-generic
`bareissWith_eq_mathlib_det` is the sole theorem needed once both a Mathlib
`CommRing` and the `hquot` term are in scope; it must not be duplicated under
carrier-specific theorem names. `Rat` and `MvPoly` already have the necessary
Mathlib structures. Executable `DensePoly`/`ZPoly` and `ZMod64` do not currently
have global Mathlib `CommRing` instances, so their computational conformance is
independent of that separate bridge work; this SPEC does not invent local
instances or weaken the theorem to claim otherwise.

These are the theorems on the forbidden list in the Mathlib-free `hex-bareiss`
SPEC: they must live here, never restated or reproven in the executable layer.
The forbidden list is about the *statement shape*, not the coefficient ring: a
Mathlib-free `bareissWith quot M = det M` at any carrier, `Int` included, is
still forbidden below this layer.

## Determinant identity boundary

The only determinant identity consumed is
`HexMatrixMathlib.desnanot_jacobi_borderedMinor`, in `CorePlucker.lean`, which
is already stated over an arbitrary Mathlib `CommRing` with no nondegeneracy
hypothesis. **The generalization requires no change to
`hex-determinant-mathlib`'s identity surface**, and must not introduce a second
determinant identity development. The general Sylvester identity stays absent
and stays unnecessary: fraction-free elimination uses only the `2 × 2`
bordered-minor case, which *is* Desnanot-Jacobi. See
[hex-determinant-mathlib §Sylvester's determinant identity: absent](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md).

One declaration next to it does need generalizing rather than duplicating:
`HexMatrixMathlib.bareissExactDiv_borderedMinor_of_mul_eq` in `CorePlucker.lean`
is a thin `Int` re-export of the Mathlib-free
`Hex.Matrix.bareissExactDiv_borderedMinor_of_mul_eq`, which packages the
Desnanot-Jacobi product identity as the `hexact` premise of
`Hex.Matrix.stepMatrix_borderedMinor_update`. In generic form it takes `quot`
and `hquot` in place of the fixed `exactDiv`, and `prevPivot ≠ 0` remains the
only nondegeneracy hypothesis anywhere in this surface:

```lean
theorem exactQuot_borderedMinor_of_mul_eq [CommRing R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (prevPivot : R)
    (hprev_ne : prevPivot ≠ 0)
    (hdesnanot : det (borderedMinor source (k + 1) hnext i j) * prevPivot = …) :
    quot … prevPivot = det (borderedMinor source (k + 1) hnext i j)
```

Its `Int` instantiation keeps the existing name, so `HexGramSchmidtMathlib`'s
use of the surrounding lemmas is unaffected. Renaming away from
`bareissExactDiv…` is deliberate: the operation is no longer fixed to
`exactDiv`, and a five-qualifier name that restates its call site is the naming
smell the project conventions call out.

Because that declaration is described by name in
[hex-determinant-mathlib §Desnanot-Jacobi: the four public forms](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md),
the implementation owes that SPEC a matching amendment. It is deliberately not
amended ahead of the code: today it describes what is actually there.

Both `CorePlucker.lean` consumers of `desnanot_jacobi_borderedMinor`
(`HexBareissMathlib/Bareiss.lean` and `HexGramSchmidtMathlib/Int/Augmented.lean`)
continue to work: the second stays at `Int` and picks up the corollary.

## Kernel certificate

`HexBareissMathlib/Kernel.lean` proves the kernel certificate of
[hex-bareiss §The kernel certificate](../../HexBareiss/SPEC/hex-bareiss.md#the-kernel-certificate)
sound for `Matrix.det` over `ℤ` and `ℚ`, stated on the Mathlib matrix of a
row list (`ofLists`, from the literal layer of
[hex-matrix-mathlib](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#matrix-literals)):

```lean
theorem det_eq_of_checkList (n) (L : List (List Int)) (c : DetWitness)
    (h : checkDetList n L c = true) : (ofLists n n L).det = c.value
theorem det_eq_of_checkList' (A : Matrix (Fin n) (Fin n) ℤ) (L) (c)
    (hA : A = ofLists n n L) (h : checkDetList n L c = true) : A.det = c.value
theorem det_eq_of_checkRat (n) (L : List (List Rat)) (s : List Nat) (B) (c) (v : Rat)
    (h : checkDetRat n L s B c v = true) : (ofLists n n L).det = v
theorem det_eq_of_checkRat' (A : Matrix (Fin n) (Fin n) ℚ) (L) (s) (B) (c) (v)
    (hA : A = ofLists n n L) (h : checkDetRat n L s B c v = true) : A.det = v
```

The proof follows the certificate. Each recorded swap is a transposition
of two rows below `n`, and `ofLists` of the swapped list is the submatrix
along `Equiv.swap`, so `det_permute` and `sign_swap` give
`det (ofLists (applySwaps s L)) = signOf s · det (ofLists L)` by induction
on the swaps. The transform rows define `Lm i k = (T.getD i []).getD k 0`,
lower triangular because row `i` has length `i + 1`
(`IsLowerTriangular`, `det_of_isLowerTriangular`); the walk's
specification `triangularCheck_spec`, by induction on the rows, gives the
zero products below the diagonal, so `Lm * ofLists n n P` is upper
triangular (`det_of_isUpperTriangular`), and the accumulated identity
`(∏ lᵢ) · d = sign · ∏ uᵢ`. With `det_mul`, `sign² = 1` and `∏ lᵢ ≠ 0`
(`Finset.prod_ne_zero_iff`, `mul_left_cancel₀`) the value is
`det (ofLists n n L)`. A left kernel vector `v` gives
`(fun i => v.getD i 0) ᵥ* ofLists n n L = 0` with a nonzero coordinate,
and `exists_vecMul_eq_zero_iff` gives `det = 0`. The passage from lists to
sums is `dotInt_eq_sum` (a dot product stopping at the shorter list is a
sum over any `Fin r` with `r` at least the first list's length, the
`getD` defaults supplying the zeros) with `column_getD` and `columns_getD`
for the transposition. For `ℚ`, `scaledRows_spec` gives
`diagonal s * ofLists n n L = (ofLists n n B).map Int.cast`, so
`det_diagonal`, `det_mul` and `Int.cast_det` turn the integer theorem into
`(∏ s) · det = value`, and the kernel-checked `v · ∏ s = value` cancels the
nonzero product (`prodNat_cast`).

## Symbolic determinant

This specified extension attaches a second handler to the `det` syntax kind
in `HexBareissMathlib/Tactic.lean`, with corresponding `det%` and
`hex_norm_det` entry points. It uses the polynomial witness and
`checkDetPolyList` specified in
[hex-bareiss §Polynomial determinant certificate](../../HexBareiss/SPEC/hex-bareiss.md#polynomial-determinant-certificate).
The numeric implementation above remains the closed-literal arm. The
symbolic arm, its checker soundness and its proof probes are not yet shipped.

### Prerequisites and input classification

The shared prerequisites are the same as
[hex-generic-rank-mathlib §Prerequisite changes](../../SPEC/Libraries/hex-generic-rank-mathlib.md#prerequisite-changes-in-other-libraries):
canonical list arithmetic in hex-mv-poly and its denotation theorem in
hex-mv-poly-mathlib block the kernel route; the numeric handlers' refactor
to `throwUnsupportedSyntax` blocks composition; and the residue coefficient
provider in hex-reflect-mathlib blocks positive characteristic. The
polynomial producer generalisation belongs to hex-bareiss, its determinant
soundness to this companion. These are implementation obligations, not
claims that the proposed declarations already exist.

Input classification is shared with
[the symbolic `rank` arm](../../SPEC/Libraries/hex-generic-rank-mathlib.md#input-classification).
The numeric handler runs first, returning `notApplicable` via
`throwUnsupportedSyntax` outside its fragment. The symbolic handler reads a
square matrix through the shared literal layer, including definitions
unfolded within budget. It canonicalises and reifies all entries with
`reifyRing?`, with top-level variables enabled, in one hex-reflect batch.
The batch seals its environment at `k` atoms, converts with the
characteristic-aware conversion when `Sym.Arith` supplies the characteristic
and the plain conversion otherwise, and uses `cmp := Hex.Mono.grevlex`.
It yields

```text
P : Hex.Matrix (Hex.MvPoly k C cmp) n n
v : Fin k → F
ι : C →+* F
```

and an interpretation proof `eval₂ ι v P[i, j] = A i j` for every entry.
Here `F` is the user's carrier and `C` the coefficient provider's carrier.
Routing is by the converted polynomials: any nonconstant entry selects the
symbolic arm; if all entries convert to constants after cancellation, the
same arm handles the resulting constant matrix, even with `k > 0`.

Atoms are independent indeterminates. Expressions outside the fixed ring
language, including `x / y`, opaque constants, `Real.exp t` and symbolic
powers, become atoms. No hypotheses or algebraic relations between atoms
are used: `hx : x = 0` does not change the polynomial for `x`. Atomisation
can prove polynomial identities involving these terms, but cannot prove
relations between them. The budgets are hex-reflect's (atoms, terms,
coefficient bits and proof nodes), plus matrix dimension and certificate
size; exhaustion returns `declined` naming the exhausted budget.

In equality mode the user's expression `e` is reified in the same batch,
using the matrix's atoms. Record the atoms allocated by the entries;
reifying `e` must not allocate additional atoms. Seal once after both have
been reified and convert both with that sealed environment. An expression
which cannot be reified as a ring expression in those atoms declines with
`det: symbolic determinant declined: target is not a ring expression in the matrix atoms`.
This includes an opaque term appearing only in `e`.

### Kernel certificate and soundness

The compiled producer returns transform rows and a value `d : MvPoly k C cmp`,
or a polynomial left kernel vector with value zero. Its meaning is always
`Hex.Matrix.det P = d`, including when the determinant is identically zero;
a matrix which becomes singular only at some atom valuations still has a
nonzero polynomial determinant. All witness entries lie in the polynomial
ring, never in a chosen specialisation or in the fraction field.

The kernel checks `checkDetPolyList` on the row lists of canonical polynomial
term lists and the witness in the same representation. Coefficients are
encoded by `Int` for the integer arm and canonical `Nat` residues for the
residue arm; exponent vectors are lists of `Nat`. Shape, canonicality,
nonzero diagonals, vanishing products and the determinant value identity
are checked as specified on the executable side. Polynomial equality uses
the list layer's `beq_iff` contract, not evaluation at sample points.

The proposed `checkDetPolyList_sound` in this companion identifies a passing
check with `Hex.Matrix.det P = d`, where `P` and `d` denote the supplied
lists and `Hex.Matrix.det` is the Leibniz reference. It uses the list
arithmetic denotation theorem, `HexMatrixMathlib.det_eq`, row permutation
signs and the triangular determinant lemmas, just as `det_eq_of_checkList`
does. Cancellation takes place over the polynomial domain: the transform's
diagonal product is nonzero there. The singular branch uses the nonzero
polynomial left kernel vector to prove determinant zero there. Neither
argument requires the vector or diagonal product to stay nonzero after
specialisation.

The batch's quoted `P` is identified definitionally, entry by entry, with
the polynomial values denoted by the term lists; this is the polynomial
analogue of the literal layer's `ofLists` identification. The denotation
lemmas justify list arithmetic without reducing reference polynomial
operations. Every definition on the arithmetic path is `@[expose]`, uses
structural recursion on lists of `Nat`/`Int`, and obeys
[matrix-tactics §Kernel discipline](../../SPEC/matrix-tactics.md#kernel-discipline).
In particular the kernel never evaluates `bareissWith`, `detWitness`, a
reference checker, or `Hex.Matrix.det` on `Hex.Matrix (MvPoly …)`. The
reference determinant occurs in soundness statements only; neither `Array`,
`Vector`, `Fin`, `Finset`, matrix indexing nor well-founded polynomial
arithmetic is reduced to check a certificate. One auxiliary theorem is
checked synchronously through `mkAuxTheorem`; there is no elaborator
`Kernel.whnf` pre-check and no `native_decide`.

### Transport and result reconstruction

Write `E := HexMatrixMathlib.matrixEquiv` (to avoid confusing the matrix
equivalence with the user's expression `e`) and
`φ := HexMvPolyMathlib.eval₂MathlibHom ι v`. The entry proofs and
`eval₂MathlibHom_apply` give `A = (E P).map φ`. Determinant correspondence
and `RingHom.map_det` then give

```text
A.det = φ (Hex.Matrix.det P) = φ d.
```

If `q` is the polynomial reified from `e`, its batch proof gives `φ q = e`.
The tactic checks equality of the canonical term lists of `d` and `q` in
the kernel, uses `beq_iff` and denotation to obtain `d = q`, and composes
these equalities. It proves agreement with the user's expression, without
printing a polynomial and asking `ring` to prove it equal. A mismatch is a
`declined` outcome displaying `φ d` and explaining that the target is not
a polynomial identity in the sealed atoms; it is not evidence that the
specialised target is false. For example, `!![x].det = 0` under `hx : x = 0`
requires substitution before this arm can close it.

The accepted goals are `A.det = e` and `e = A.det`, the latter by symmetry.
With no target expression, `det% A` returns the existing
`HexMatrixMathlib.Certified Matrix.det A`, with `value := φ d` and
`proof : A.det = value`; the value is the denoted computed polynomial in
`F`, not a polynomial object or an unproved pretty-printed expression.
These results are unconditional. Even if a pivot polynomial vanishes at
`v`, determinant transport is valid: unlike symbolic rank, this arm has no
nonvanishing condition to discharge or leave as a goal. The empty matrix
returns one.

### Carriers and composition

The initial characteristic-zero field arm uses the integer provider
(`C := Int`, `ι := Int.castRingHom F`) and requires `[CharZero F]`, matching
the symbolic rank classifier's injective coefficient interpretation.
This is a frontend contract; `RingHom.map_det` itself needs no injectivity
and works for commutative rings. There is no assumption that evaluation of
polynomials at the atoms is injective.

Rational coefficients use row scaling as `checkDetRat` does: for a matrix
over `ℚ`, clear the closed rational coefficient denominators in each row,
record positive integer scales `sᵢ`, certify the resulting integer
polynomial matrix `B`, and check the scaling identities coefficientwise in
canonical list form. If `D := ∏ sᵢ` and `dB` is the certified determinant,
then `D * A.det = φ dB`; cancellation in `ℚ` yields the result. For a
rational target polynomial `q`, also choose and check a positive denominator
`t` with `t * q = qZ` over integer polynomials; kernel list equality checks
`t * dB = D * qZ`. The term form returns `φ dB / D`. Denominator clearing
is a proof-producing coefficient normalisation in the same batch, not a
license to simplify division by symbolic atoms. Only closed rational
coefficients are cleared; `x / y` remains an independent atom.

Positive characteristic uses the residue provider once available, with its
canonical residue list arithmetic, Mathlib ring/domain bridge and lawful
exact quotient at `MvPoly`. For `ZMod64 p`, this includes both
`ZMod64.Bounds p` and `ZMod64.PrimeModulus p`; a composite modulus does not
satisfy the domain contract. Characteristic-aware conversion reduces
coefficients, not exponents or polynomial functions: `X³ - X` over
`ZMod 3` is not the zero polynomial. Until the provider exists this arm
declines with `det: symbolic determinant declined: residue coefficient provider unavailable`.

`hex_norm_det` tries the numeric certificate, then the symbolic certificate,
then the unmodified Mathlib `norm_det` fallback in the same simp set. A
symbolic success rewrites to `φ d`; a decline leaves the original expression
available to Mathlib. No input `norm_det` accepts today regresses. Unsupported
goals return `notApplicable`; capability or budget declines retain
`det: symbolic determinant declined: <reason>`, including carrier or entry
coordinate where relevant, for reporting if the composed tactic fails.
A malformed or rejected producer certificate is `failure`, never a weaker
result disguised as success. The axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`, as for the numeric arm.

### Proof probes and shipping bar

Add symbolic probes under `bench/HexBareissMathlib/ProofProbe`, with the
executable producer measurements owned by hex-bareiss. Sweep dimensions
`2, 4, 8`, atom counts `1, 2, 4`, total entry degrees `1, 2, 4` and entry
supports `1, 4, 16`, recording the actual canonical degree and support.
Use all feasible combinations: a requested support larger than the number
of monomials of the given degree bound and arity is marked infeasible,
not silently generated with smaller support. Include dense, structured,
pivot-swap and identically singular matrices, rational coefficient variants,
and valuations at which a nonzero polynomial determinant becomes zero.

The closed-algebraic family uses `ℚ(√2)` blocks, including
`!![α, 1; 2, α]`. The shared polynomial target is `α² - 2`; both arms
must be measured on that target with `α` treated as an atom. The target
zero using `α² = 2` is a separate scope probe: independent-atom reification
cannot use that relation, in Hex as in `norm_det`. Record the decline;
do not claim an algebraic-number scope win without a separate certified
coefficient provider that can prove the relation. Strictly larger scope
must instead be demonstrated on accepted surfaces such as the shared
literal layer's `fun i j => …`/`Matrix.ofArray` forms and `det%`.

Compare against the unmodified pinned `norm_det` from
`Mathlib/Tactic/NormDet.lean` on identical targets, with the same residual
ring normalisation if the Mathlib arm needs it, in fresh modules against
matched import-only baselines. Use `scripts/bench/fresh_module_sweep.py`:
six samples, adjacent pairs, alternating `AB`/`BA`, retaining all completed
runs on the shared host. Record batch reification, producer, list conversion,
kernel check and total elaboration separately, plus proof node count,
`.olean` size, realised minor support/degree and coefficient bits. Record
one kernel-only profile per family and median ratios in this SPEC before
shipping; these are planned measurements, not inferred timing results.

Bird's `O(n⁴)` ring-normalised certificate chain is expected to lose as
matrix dimension grows while minor support remains modest: the fraction-free
list check uses about `n³ / 3` polynomial products (or `n²` for a singular
vector), and never replays pivot search or division. With many variables,
higher degrees or dense support, expanded minors and intermediate products
can swell enough to reverse that advantage; small matrices can also be
dominated by reification and list conversion. Report those losses and
budget declines rather than extrapolating scalar operation counts to time.

The shipping rule is exactly
[matrix-tactics §The bar against Mathlib](../../SPEC/matrix-tactics.md#the-bar-against-mathlib):
a smaller fresh-module median on every shared symbolic family, and a
strictly larger accepted fragment while preserving Mathlib's accepted
inputs through composition. Fallback preserves scope but does not establish
a runtime win. A losing shared family blocks shipping this arm; a win on
selected rungs, or the numeric arm's existing table, does not clear the bar.

### Declaration inventory

Existing declarations used by this design:

| declarations | source |
|---|---|
| `Hex.Matrix.DetWitness`, `checkDetList`, `checkDetRat`, `detWitness` | `HexBareiss/Kernel.lean` (integer witness and producer today) |
| `HexMatrixMathlib.det_eq_of_checkList`, `det_eq_of_checkRat` | `HexBareissMathlib/Kernel.lean` |
| `hex_norm_det`, `det` and `det%` syntax | `HexBareissMathlib/Tactic.lean` |
| `HexMatrixMathlib.Certified` | `HexMatrixMathlib/Literal.lean` |
| `HexMvPolyMathlib.eval₂MathlibHom`, `eval₂MathlibHom_apply` | `HexMvPolyMathlib/Aeval.lean` |
| `HexMatrixMathlib.det_eq` | `HexDeterminantMathlib/CoreTransport.lean` |
| `RingHom.map_det` | Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `Matrix.det_of_isLowerTriangular`, `det_of_isUpperTriangular` | Mathlib `LinearAlgebra/Matrix/Block.lean` |

`checkDetPolyList`, `checkDetPolyList_sound`, the polynomial generalisation
of `detWitness`, and the canonical list layer's `beq_iff`/denotation API
are proposed obligations. The checker stays Mathlib-free in hex-bareiss;
its determinant soundness stays in this companion.

## The `det` tactic

`HexBareissMathlib/Tactic.lean` declares the non-reserved tactic keyword
`det`, closing `A.det = d` and `d = A.det` for `A : Matrix (Fin n) (Fin n) R`
with `R` either `ℤ` or `ℚ`, a closed literal in one of the four syntaxes
of the literal layer of `hex-matrix-mathlib` (`!![…]`, `Matrix.of ![…]`,
`fun i j => …`, `Matrix.ofArray xs h`), possibly behind definitions
(unfolded within a small budget), and `d` a closed value; the term form
`det% A` returning `Certified Matrix.det A` with its `value` and `proof`
(the `!![…]` notations are given an integer expectation); and the simproc
`hex_norm_det`, which rewrites `Matrix.det A` to its value and falls back
to Mathlib's `norm_det` when the Hex frontend declines, so that the two
form one simp set and no input `norm_det` accepts regresses. Entries are
closed numeric expressions that `norm_num` evaluates (the `fun` form's
entries first pass through the default simp set, for `Fin.val`, casts and
`if i = j` tests) and that the kernel reduces to their numerals.

The tactic evaluates the entries, runs the compiled `detWitnessOfLists`,
quotes the witness with `toExpr`, and builds
`det_eq_of_checkList' A L c hA (of_decide_eq_true rfl)` with `hA` the
literal's identification with its row list (`rfl` for a vector chain, one
kernel `decide` on `entriesEq` otherwise), composed with a kernel-decided
comparison of the value with `d`. A rational matrix is scaled row by row by
the least common multiple of its denominators to an integer one, whose
witness is checked by `checkDetRat` together with the scaling and the
value, through `det_eq_of_checkRat'`. The whole proof is added as an
auxiliary theorem (`mkAuxTheorem`, with asynchronous checking off) so the
kernel checks it exactly once and the tactic sees a rejection. Outcomes
follow the protocol of [SPEC/matrix-tactics.md](../../SPEC/matrix-tactics.md):
a goal that is not a determinant equation is not applicable; a matrix with
free variables, a carrier other than `ℤ` or `ℚ`, a non-square shape, a
non-literal closed matrix or an entry `norm_num` cannot evaluate is
declined with the reason, and the `det` tactic then runs
`simp only [hex_norm_det]`, which reaches `norm_det` for symbolic entries
and other commutative rings (normalizing the determinant as `eval_det`
does; the residual goal is for `ring` or `decide`) and reports the decline
if that fails too; a false target is reported with the certified value
before any proof is built; a rejection by the kernel is diagnosed by
evaluating the certificate check and the identification of the literal in
turn, and reported as a producer bug or an entry the kernel cannot
reduce. Accepted theorems depend on `propext`, `Classical.choice` and
`Quot.sound` only.

**Comparator.** The unmodified pinned `eval_det` (Bird's algorithm with a
certificate chain normalized by `ring`) is the comparator. The
fresh-module probes `bench/HexBareissMathlib/ProofProbe/{Dense8, Dense12,
Dense16, Dense32, Tridiagonal16, Vandermonde8, Singular16, Large8Bits64,
Large4Bits256, Rational8}{Hex,Mathlib}.lean`, written by
`scripts/bench/det_tactic_probes.py`, prove the same seeded literal by
`det` and by `eval_det`, each against its import-only baseline
(`Baseline`, `MathlibBaseline`); `scripts/bench/det_tactic_sweep.py` runs
them through `fresh_module_sweep.py` (six samples, adjacent pairs,
alternating orientation). Each arm's delta is an absolute estimate of its
proof cost, literal elaboration included; the family's comparator ratio is
the ratio of the two medians and is only as resolved as the smaller delta.
`dense-32` has no `eval_det` arm: Bird's algorithm does not finish it
within the `120 s` budget. Medians from
`reports/bench-results/hex-bareiss-mathlib-tactic-probes-eed5c4c60624-chungus2.json`
(shared host, one CPU, both arms with the literal's elaboration inside
the delta):

| family | `eval_det` | `det` | ratio |
|---|---|---|---|
| dense `8 × 8`, 8-bit | 0.51 s | 0.16 s | 3.3 |
| dense `12 × 12`, 8-bit | 3.55 s | 0.30 s | 11.7 |
| dense `16 × 16`, 8-bit | 18.8 s | 0.52 s | 36 |
| dense `32 × 32`, 8-bit | over budget, no arm | 3.71 s | |
| tridiagonal `16 × 16` | 4.40 s | 0.40 s | 10.9 |
| Vandermonde `8 × 8`, leading zero | 0.40 s | 0.11 s | 3.6 |
| singular `16 × 16`, rank `15` | 18.8 s | 0.32 s | 59 |
| dense `8 × 8`, 64-bit | 0.60 s | 0.15 s | 4.0 |
| dense `4 × 4`, 256-bit | 0.11 s | 0.09 s | 1.2 |
| rational `8 × 8` | 0.69 s | 0.20 s | 3.5 |

Proof time against dimension, for the dense `8`-bit, singular (rank
`n − 1`) and dense `64`-bit families up to a ten-second cap per run, is
recorded by `scripts/bench/det_tactic_size_sweep.py` (profiler totals per
file, imports excluded, the median of three runs per point with the range
kept); the current record is
`reports/bench-results/hex-bareiss-mathlib-tactic-size-2166e872dce6-chungus2.json`.
`eval_det` reaches `n = 14` in every family (6.7, 7.7 and 7.0 s) and `det`
reaches `n = 40` on the dense family (7.2 s), `n = 48` on the singular
family (5.3 s) and `n = 24`, the end of its ladder, on the 64-bit family
(1.5 s); the kernel is about a third to a half of `det`'s time at those
dimensions, the literal's elaboration and the compiled producer the rest.
The record is plotted by `scripts/plots/hex-bareiss-mathlib-tactic-size.py`
to `reports/figures/hex-bareiss-mathlib-tactic-size.svg`.

Median kernel shares recorded by the same size sweep are:

| family | `eval_det` | `det` |
|---|---|---|
| dense `8 × 8`, 8-bit | 246 ms | 23 ms |
| dense `12 × 12`, 8-bit | 1.48 s | 63 ms |
| dense `14 × 14`, 8-bit | 2.97 s | 103 ms |
| dense `16 × 16`, 8-bit | timeout | 163 ms |
| dense `32 × 32`, 8-bit | timeout | 1.55 s |
| dense `40 × 40`, 8-bit | timeout | 3.73 s |
| singular `8 × 8` | 244 ms | 13 ms |
| singular `16 × 16` | timeout | 58 ms |
| singular `32 × 32` | timeout | 721 ms |
| singular `48 × 48` | timeout | 2.33 s |
| dense `8 × 8`, 64-bit | 272 ms | 24 ms |
| dense `16 × 16`, 64-bit | timeout | 170 ms |
| dense `24 × 24`, 64-bit | timeout | 611 ms |

The timeout entries have no profiler breakdown because the corresponding
proof exceeded the sweep's ten-second cap.

Determinants on `Hex.Matrix` inputs, finite and closed algebraic carriers
and symbolic entries are out of scope here
([SPEC/matrix-tactics.md §Placement](../../SPEC/matrix-tactics.md#placement)).

## Tests

`HexBareissMathlib/Tests.lean`, build-only:

- `checkDetList` on a hand-written `2 × 2` triangular witness and on a
  hand-written singular witness, discharged by `decide +kernel`, and
  `det_eq_of_checkList` on each, concluding `det (ofLists 2 2 L) = -2` and
  `= 0`;
- the `det` tactic in both orientations on a `3 × 3` example behind a
  definition and inline, on the four literal syntaxes (including a `fun`
  form behind a definition), on compound entries, the empty and `1 × 1`
  matrices, rational entries (a proper fraction, integers written in `ℚ`,
  a singular rational matrix), odd and even dimensions with pivot swaps, a
  `5 × 5` matrix with a late swap, singular inputs of every kind, and a
  `16 × 16` literal with `8`-bit entries;
- `det%` on a definition, inline and on a rational literal, and its
  `proof` field closing the determinant equation;
- `simp only [hex_norm_det]` on integer and rational literals, and on
  symbolic entries through `norm_det` (with `ring`), plus the `det` tactic
  reaching `norm_det` on symbolic entries and on `ZMod 7`;
- the messages on a false target, a closed non-literal and a goal that is
  not a determinant equation (`#guard_msgs`);
- `Hex.Matrix.det` and the bare `det` identifier still usable on
  `Hex.Matrix`;
- the axiom audit of a `16 × 16` determinant proved by `det`.

These are not an independent oracle. The conformance stream of `HexBareiss`
is.
