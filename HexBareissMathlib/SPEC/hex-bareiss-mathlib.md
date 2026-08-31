# hex-bareiss-mathlib (depends on hex-bareiss + hex-determinant-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexBareiss`
Computational performance owner: `HexBareiss`

Mathlib bridge for `hex-bareiss`: proves the row-pivoted Bareiss determinant
correct against both Mathlib's determinant and our executable Leibniz
determinant, via the no-pivot bordered-minor invariant and the determinant
correspondence from `hex-determinant-mathlib`. The proofs are stated over an
arbitrary commutative coefficient ring with an exact quotient; `Int` is a
corollary, with no hypotheses beyond what it has today.

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

**Other carriers.** A Mathlib `Field K` with `DecidableEq K` instantiates
through `Hex.instExactDivLawsField` and `Hex.exactDiv_mul_right`; so does any
`[CommRing R] [Div R] [Hex.ExactDivLaws R]`. Both were checked to elaborate.

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
