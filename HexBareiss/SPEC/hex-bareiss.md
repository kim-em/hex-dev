# hex-bareiss (depends on hex-determinant, hex-matrix)

The executable Bareiss determinant (fraction-free Gaussian elimination), plus
the bordered-minor support its correctness development relies on. The recurrence
is specified over an arbitrary commutative coefficient ring carrying an exact
quotient; `Int` is the specialization every current consumer uses, and its
names, signatures and values are unchanged by the generalization.

## Coefficient contract

Executable operations and correctness laws are kept apart, exactly as in
[hex-resultant](https://github.com/kim-em/hex-dev/blob/main/HexResultant/SPEC/hex-resultant.md).

**Operations.** Each executable definition takes only the unbundled classes it
calls, and the exact quotient is a plain function argument rather than a class.
The table covers the principal algorithm operations, not every definition in
the library: the array-storage layer, `finish`, the initial states and the
`@[csimp]` implementation variants take the classes their own bodies call.

| definition | operation classes | quotient |
|---|---|---|
| `findPivot?`, `findPivotAux` | `[Zero R] [DecidableEq R]` | none |
| `stepMatrixWith` | `[Zero R] [Sub R] [Mul R]` | `quot : R → R → R` |
| `pivotLoopWith`, `noPivotLoopWith` | `[Zero R] [DecidableEq R] [Sub R] [Mul R]` | `quot` |
| `BareissData.sign` | `[One R] [Neg R]` | none |
| `BareissData.det` | `[Zero R] [One R] [Neg R] [Mul R]` | none |
| `bareissWith`, `bareissNoPivotWith` | `[Zero R] [One R] [Neg R] [DecidableEq R] [Sub R] [Mul R]` | `quot` |

`DecidableEq R` appears only where a zero test is genuinely performed: pivot
search and the loop's zero-pivot branch. No `Div R` appears in the executable
layer at all. See [§Exact quotients](#exact-quotients-obligation-totality-and-the-int-fast-path)
for why the quotient is an argument and not a `Div`-derived operation.

**Laws.** Each loop-correctness and headline theorem takes
`[Lean.Grind.CommRing R] [DecidableEq R]` plus the single hypothesis

```lean
(quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
```

That is `Hex.ExactDivLaws.mul_div_cancel_right` in unbundled form. A carrier
with `[Div R] [Hex.ExactDivLaws R]` discharges it by `Hex.exactDiv_mul_right`;
`Int` discharges it for `Hex.Matrix.exactDiv` by `Int.mul_ediv_cancel`. Purely
structural lemmas (entry formulas, fuel composition, loop equalities) and the
`hexact`-premise update lemma need less than this and should not be given the
full binder list.

**What is deliberately not assumed.** No public `IsDomain`, `NoZeroDivisors`
or nontriviality hypothesis, and no divisibility hypothesis anywhere. Bareiss is
an integral-domain algorithm, but the cancellation and no-zero-divisor facts are
*consequences* of the exact-quotient law rather than separate assumptions:

| fact the development needs | where it comes from |
|---|---|
| nonzero products stay nonzero | `Hex.ExactDivLaws.mul_ne_zero` |
| cancel a nonzero right factor | `Hex.ExactDivLaws.mul_right_cancel` |
| `(1 : R) ≠ 0` for the `prevPivot = 1` seed | a case split on `(1 : R) = 0`, discharged through `Hex.one_ne_zero_of_nonzero` |

The law package is stated over `[Div R] [Hex.ExactDivLaws R]`, so a theorem
whose binders carry only the unbundled `quot` and `hquot` cannot invoke those
lemmas directly. The bridge builds the package locally instead:

```lean
letI : Div R := ⟨quot⟩
haveI : Hex.ExactDivLaws R := ⟨hquot⟩
```

The facts it then derives (`mul_ne_zero`, `mul_right_cancel`) do not mention
`/`, so the local `Div` never escapes into a statement and never competes with a
carrier's own `Div` instance.

The `(1 : R) ≠ 0` row is the one place where the `Int` development uses a `decide` that
does not survive generalization: the initial no-pivot invariant asserts
`prevPivot ≠ 0` at `prevPivot = 1`. The generic form takes `(1 : R) ≠ 0` as a
hypothesis on the *invariant* lemmas, and each public theorem opens with a case
split on `(1 : R) = 0`. In the trivial branch every element of `R` is `0` (the
contrapositive of `Hex.one_ne_zero_of_nonzero`), so both sides of the
correctness statement are `0` and the theorem holds without any nontriviality
assumption on the carrier. No new law is needed in the shared exact-division
package for this.

**One `IsDomain` instance is still required, locally.** The failed-pivot branch
proves `det M = 0` through Mathlib's `Matrix.exists_mulVec_eq_zero_iff`, which
is stated for `[CommRing A] [IsDomain A]`. In the nontrivial branch the instance
is constructed rather than assumed: `Nontrivial R` from `(1 : R) ≠ 0`,
`NoZeroDivisors R` from the derived `mul_ne_zero`, then
`NoZeroDivisors.to_isDomain`. This is a `haveI` inside one proof, not a binder
on any public statement.

Every lemma named above lives in
[`HexBasic/ExactDiv.lean`](https://github.com/leanprover/hex-basic/blob/main/HexBasic/ExactDiv.lean),
below this library, so generalizing adds one `public import HexBasic.ExactDiv`
and no new entry in
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml).
`hex-bareiss` stays at `deps: [HexDeterminant, HexMatrix]` and the graph stays
acyclic. In particular the recursive `ExactDivLaws (DensePoly R)` instance lives
in `hex-resultant`, which is *not* below `hex-bareiss`: a polynomial-matrix
instantiation (a characteristic-polynomial or Smith-form consumer) belongs in a
library that already depends on both, never here.

## Algorithm

Write `a⁽ᵏ⁾` for the matrix after `k` elimination steps and `p₍ₖ₎` for the pivot
consumed at step `k`, with `p₍₋₁₎ = 1`. For `i, j > k`:

```
a⁽ᵏ⁺¹⁾_{ij} = quot (p₍ₖ₎ · a⁽ᵏ⁾_{ij} − a⁽ᵏ⁾_{ik} · a⁽ᵏ⁾_{kj}) p₍ₖ₋₁₎
```

Entries with `i ≤ k` or `j < k` are copied unchanged; entries with `i > k` and
`j = k` are set to `0`. `stepMatrixWith` takes `p₍ₖ₎` and `p₍ₖ₋₁₎` as the
explicit arguments `pivot` and `prevPivot`, so the step function itself does not
read the pivot out of the matrix.

**State and data.** `BareissState R n` carries `step`, `matrix`, `prevPivot`,
`rowSwaps` and `singularStep`; `BareissData R n` is the terminal `matrix`,
`rowSwaps` and `singularStep`; `BareissArrayState R` is the array-storage
counterpart. All three gain the coefficient parameter `R`, so existing
`BareissState n`, `BareissData n` and `BareissArrayState` occurrences become
`BareissState Int n`, `BareissData Int n` and `BareissArrayState Int`. Those
three arity changes are the source-visible break the generalization introduces;
they are mechanical, compile-time visible, and change no value.

**Two loops.** `noPivotLoopWith` aborts at a zero diagonal pivot and records the
step; `pivotLoopWith` first tries a row swap. Both are fuelled by `n` and are
equal whenever the no-pivot run records no singular step.

## Zero-pivot detection, row swaps, and sign

`findPivot? M col start` scans column `col` from row `start` downwards and
returns the first row whose entry is nonzero, or `none`. It needs only
`[Zero R] [DecidableEq R]`: an equality test against `0`, never an ordering, a
norm, or a unit test. No pivot *choice* heuristic is specified: the first
nonzero entry is the pivot, and that choice is part of the observable behavior
because it determines `rowSwaps` and hence the sign.

At step `k`, if `a⁽ᵏ⁾_{kk} = 0` the loop calls `findPivot?` on column `k` from
row `k + 1`:

- a row `r` is returned: swap rows `k` and `r`, increment `rowSwaps`, continue;
- `none`: set `singularStep := some k` and stop.

`BareissData.sign` is `1` when `rowSwaps` is even and `-1` when it is odd, and
`BareissData.det` is `0` on a recorded singular step, `sign * a_{n-1,n-1}`
otherwise. Only `[One R] [Neg R]` is needed: the sign is an element of `R`, not
an `Int` multiplier, so nothing here needs a `IntCast` or a characteristic
assumption.

`singularStep = some k` means the algorithm proved a determinant-zero
certificate, not that it gave up: column `k` of `a⁽ᵏ⁾` is zero at and below the
diagonal, and the correctness development turns that into `det M = 0`. That
step is where `ExactDivLaws.mul_right_cancel` is consumed, replacing today's
`Int.mul_eq_zero`.

## Exact quotients: obligation, totality, and the `Int` fast path

**Obligation.** Every division performed by a run has a nonzero denominator
(`prevPivot` is either the seed `1` or a pivot the loop already tested nonzero)
and an exact numerator. Exactness is not checked at runtime and is not a
hypothesis on the input: it is the Desnanot-Jacobi identity, discharged once in
the bridge layer. Concretely, under the bordered-minor invariant the numerator
at step `k` equals `p₍ₖ₋₁₎ · det (borderedMinor source (k+1) hnext i j)`, and
`hquot` returns the second factor.

**Totality, and where it stops.** Both quotients are total *as Lean
definitions*: `Hex.exactDiv a 0 = 0` by its guard, and `Hex.Matrix.exactDiv a 0`
reduces through `Int.ediv` to `0`. The two are equal at `Int`.

They are not both total in *compiled* code, and the SPEC does not claim they
are. `Hex.exactDiv` keeps its zero guard after compilation. `Hex.Matrix.exactDiv`
is `@[extern "lean_int_div_exact"]`, and that entry point guards a zero
denominator only on the small-integer path; with a multi-limb numerator and a
zero denominator it reaches `lean_int_big_div_exact`, whose `d != 0` check is a
`lean_assert` (compiled out in release) before it calls GMP's `mpz_divexact`,
which has no zero-denominator contract. This is a pre-existing property of
`Hex.Matrix.exactDiv`, which drops the `y ∣ x` argument that `Int.divExact`
carries; the generalization neither creates nor removes it.

The consequence for this SPEC is a precondition, not a value: the native exact
quotient is specified only for a nonzero denominator dividing its numerator. A
run never violates that, because the loop records `singularStep` and stops
before dividing by a zero pivot. Nothing downstream may rely on a zero-denominator
call to `Hex.Matrix.exactDiv` returning `0` in compiled code.

**Why the quotient is an argument.** The natural generalization would take
`[Div R]` and call `Hex.exactDiv`. It is value-correct, since at `Int` the two
quotients are equal,

```lean
theorem exactDiv_int_eq (a b : Int) : Hex.exactDiv a b = Hex.Matrix.exactDiv a b
```

but it discards the carrier's exact-division primitive. `Hex.exactDiv` is
`if b = 0 then 0 else a / b`, whose `/` compiles to the `Div R` dictionary
entry, which for `Int` is `Int.ediv` and hence `lean_int_ediv`. Today's
`Hex.Matrix.exactDiv` is `@[extern "lean_int_div_exact"]`, matching
`Int.divExact`, which the runtime routes to `lean_int_big_div_exact` and thence
to GMP's `mpz_divexact`. GMP documents exact division as faster than general
division when exactness is known, though it also documents the implementation as
basecase rather than subquadratic, so the advantage is a constant factor of
unstated size rather than a change of order. The `[Div R]` form additionally
pays a `DecidableEq R` zero test on every one of the ~`n³/3` divisions, which
`Hex.Matrix.exactDiv` does not. How much either costs at the benched rungs is
what the A/B rung below is for; this SPEC does not assert a figure.

Passing `quot` as an argument keeps one algorithm and one proof while letting
each carrier supply its best primitive. In practice `quot` is a section
`variable`, so threading it through the state machine costs no syntax at the
definition sites. The two instantiations are:

```lean
-- generic, from the shared Div-derived wrapper
bareissWith Hex.exactDiv M      -- needs [Div R] [Hex.ExactDivLaws R] for the law only

-- Int, from the GMP-backed exact quotient
def bareiss (M : Matrix Int n n) : Int := bareissWith Hex.Matrix.exactDiv M
```

No generic `Div`-derived alias for `bareissWith Hex.exactDiv` is introduced, so
that every generic call site names the quotient it is using. `Hex.exactDiv`,
`Hex.ExactDivLaws` and the cancellation lemmas are reused unchanged; nothing is
added to the shared exact-division package, and nothing about it is redesigned.

A function-valued parameter can compile to an indirect call through the inner
loop, so the `Int` specialization is *not* asserted to produce byte-identical
code to today's. What it is asserted to do is call the same primitive.
`@[specialize]` on the loop functions is the mechanism for recovering a direct
call at the `Hex.Matrix.exactDiv` instantiation, and the A/B rung is what
confirms it; if neither holds up, keeping a monomorphic `Int` implementation
behind `@[implemented_by]` (alongside the existing `@[csimp]` array path) is the
fallback, at the cost of a second implementation to keep in step.

If a measurement (see [§Benchmarks](#benchmark-changes)) shows the
`lean_int_div_exact` advantage is inside bench noise at every rung, the simpler
`[Div R]`-and-`Hex.exactDiv` form is preferable and this section should be
amended rather than worked around.

## Degenerate dimensions

The loop condition is `state.step + 1 < n`, so it runs `n - 1` steps.

- `n = 0`: no step, `singularStep = none`, the diagonal is empty, and
  `bareiss M = sign = 1`, matching the empty product `det M = 1`.
- `n = 1`: no step and no pivot search. `bareiss M = 1 * M[0][0] = M[0][0]`,
  including when `M[0][0] = 0`; the zero-pivot branch is never reached, so a
  `1 × 1` zero matrix returns `0` through the ordinary diagonal path rather
  than through `singularStep`.
- `n ≥ 2`: the general case above.

No division occurs when `n ≤ 1`, so at those dimensions correctness does not
touch the exact-quotient law at all.

## Complexity

Step `k` updates the `(n - 1 - k)²` entries with `i, j > k`, each costing two
multiplications, one subtraction and one exact division, so a full run performs

```
Σ_{k=0}^{n-2} (n - 1 - k)² = (n-1)·n·(2n-1)/6  ≈  n³/3
```

exact divisions and subtractions and twice that many multiplications, plus at
most `n²/2` zero tests in pivot search. The count is coefficient-independent, and it is the cost of a full
non-aborted run; a run that records `singularStep` performs fewer. The `n²/2`
figure covers pivot search only, not the loop's own diagonal zero test at each
step.

**No denominator swell, and controlled stored-entry growth.** The invariant is
that `a⁽ᵏ⁾_{ij}` is the determinant of `borderedMinor source k _ i j`, a
`(k+1) × (k+1)` minor of the *input*. Every stored entry is therefore a minor of
the input, never a ratio and never an accumulated product; that is what
"fraction-free" means, and it is exactly the invariant the correctness proof
carries, so the complexity claim and the correctness claim are the same
statement. Two qualifications: each step transiently builds a difference of two
products of stored entries before dividing, so the numerator is about twice the
size of the entry it becomes; and an intermediate minor can be larger than the
final determinant, so this bounds growth rather than making it monotone in the
answer.

Over `Int` with `‖M‖∞ ≤ B`, Hadamard's bound gives
`|a⁽ᵏ⁾_{ij}| ≤ (k+1)^((k+1)/2) · B^(k+1)`, i.e. bit length
`O(n · (log n + log B))`, so a run costs `O(n³)` operations on integers of that
size. Over a general commutative ring there is no size measure and no
ring-independent bit bound; the minor identity above is the only size statement
this SPEC makes.

## `Int` specialization

`Hex.Matrix.exactDiv : Int → Int → Int` stays exactly as it is, including its
`@[extern "lean_int_div_exact"]` binding and `exactDiv_eq_divExact`. It is
public `Int` API in its own right (`HexGramSchmidt/Int/Scaled.lean` calls it
directly) and is not folded into the generic layer.

`bareiss`, `bareissData`, `bareissNoPivot` and `bareissNoPivotData` keep their
current names and `Matrix Int n n` signatures, now *defined* as the
`Hex.Matrix.exactDiv` instantiations of their `*With` counterparts. Every
downstream `Int` call site and every committed conformance fixture value is
unchanged, and the inner loop calls the same division primitive.

The array-storage layer (`BareissArrayState`, `matrixToRows`, `rowsToMatrix`,
`getEntry`) generalizes to `Array (Array R)`. One change is needed:
`getEntry rows row col` is `rows[row]![col]!` today, which requires
`Inhabited R`; the generic form is

```lean
def getEntry [Zero R] (rows : Array (Array R)) (row col : Nat) : R :=
  (rows.getD row #[]).getD col 0
```

which needs only the `Zero R` already in scope. At `Int` the junk value is `0`
either way, so the exported behavior `HexGramSchmidt.Int` relies on is
unchanged.

## The kernel certificate

`bareissWith` is the reference computation, and replaying it in the kernel
is the wrong certificate: the kernel would traverse `Vector` buffers,
rebuild `ofFn` matrices at every access and run the pivot search and the
exact divisions, which is what the withdrawn `det` frontend did and how it
lost to `eval_det` by a factor of three per check
([SPEC/matrix-tactics.md §Measured record](../../SPEC/matrix-tactics.md#measured-record)).
`HexBareiss/Kernel.lean` therefore carries the triangularization the
elimination produces as a certificate checked over lists, `DetWitness`,
with a checker `checkDetList` written for the kernel, a rational form
`checkDetRat`, and a producer `detWitness`.

**Data.** All fields are lists of `Nat` or `Int`, so the kernel meets only
structural recursion, `Int.mul`/`Int.add`/`Int.neg` and `Int.decEq`:

```lean
inductive DetWitness where
  | triangular (swaps : List (Nat × Nat)) (transform : List (List Int)) (value : Int)
  | singular (vec : List Int)
```

For a nonsingular `n × n` matrix `A` given as a row list, `swaps` are the
row swaps of the pivot search in application order, `transform` is the
lower triangular transform `L` given row by row with its `i + 1` leading
entries (so its diagonal `lᵢ` is the last entry of row `i`), and `value`
is `det A`. A singular matrix carries a nonzero left kernel vector `v`
instead, and its value is `0`.

**Checks.** `checkDetList n A c` on the row list `A` of the matrix:

1. shapes: `A` has `n` rows of length `n`; every swap exchanges two
   distinct rows below `n`; row `i` of the transform has length `i + 1`
   and a nonzero last entry;
2. the triangularization: the kernel arranges the rows itself
   (`applySwaps`, each swap two `replaceRow`s), reads the sign of the
   arrangement off the number of swaps, and transposes the arranged matrix
   once (`columns`). For every row `i` of `L` it takes the products with
   the columns `0, …, i` of `σA`: the first `i` must vanish, and the last
   is the diagonal entry `uᵢ` of the upper triangular product `U = L · σA`
   (`triangularCheck`). Nothing above the diagonal of `U` is computed;
   the cost is about `n³ / 3` products of minor-sized integers;
3. the value: `(∏ lᵢ) · value = sign σ · ∏ uᵢ` over `Int`, the products
   accumulated during the walk. Since `det L · det (σA) = det U`, that is
   `(∏ lᵢ) · det (σA) = ∏ uᵢ`, and `∏ lᵢ ≠ 0`, the value is `det A`;
4. a singular witness instead: `v` has length `n` and a nonzero entry and
   `v · A = 0`, checked as `n²` products against the columns of `A`.

`checkDetRat n A s B c v` certifies a rational row list `A` through an
integer one: the positive scales `s` take each row of `A` to the row of
`B` (`scaledRows`, `n²` products by `Rat.mul` compared by `Rat.decEq`),
`B` carries the witness `c`, and `v · ∏ s = value c`.

**Producer.** `detWitnessOfLists n A` (and `detWitness` on a
`Hex.Matrix Int n n`) is the row-pivoted fraction-free elimination in
echelon form run on `[A | I]`: the pivot of column `c` is searched at or
below the current pivot row, rows are swapped in both blocks and the swap
recorded, and the rows below are eliminated by the Bareiss step
`(p · x - f · y) / prev` in both blocks. After `r` pivots the entries of
both blocks are minors of `[A | I]`, so every division is exact. With `n`
pivots the right block is the transform in the original row order; its row
`i` restricted to the current positions `0, …, i` is row `i` of `L`, its
diagonal is `1, d₁, …, dₙ₋₁` and the diagonal of `U` is `d₁, …, dₙ` (the
leading principal minors of the arranged matrix), so `value = sign σ · dₙ`.
With fewer than `n` pivots the last row of the left block is zero, so the
last row of the right block is a left kernel vector, nonzero because its
last entry is a product of pivots. The producer re-checks its own output
with `checkDetList` and reports a failure as an error rather than
returning a witness.

The soundness theorems `det_eq_of_checkList` and `det_eq_of_checkRat`
(`Matrix.det` of the Mathlib matrix of the row list equals the value) are
on the forbidden list above and live in
[hex-bareiss-mathlib §Kernel certificate](../../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md#kernel-certificate);
this layer states no equation between the certificate and a determinant.

## Polynomial determinant certificate

The symbolic `det` arm specified in
[hex-bareiss-mathlib §Symbolic determinant](../../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md#symbolic-determinant)
uses the same certificate as [§The kernel certificate](#the-kernel-certificate),
generalised over a coefficient type and instantiated by the companion at
`MvPoly k C Hex.Mono.grevlex`. This is a specified extension; `HexBareiss/Kernel.lean` currently provides the integer
`DetWitness`, `detWitness` and list checkers. Canonical polynomial list
arithmetic in hex-mv-poly is a prerequisite for the polynomial kernel route.

**Placement.** Keep the dependency boundary of
[§Placement in the dependency graph](#placement-in-the-dependency-graph).
The witness and producer in hex-bareiss are generic over ring operations,
equality and an exact quotient supplied by the caller; they do not import
`HexMvGcd` or `HexMvPoly`. Likewise `checkDetPolyList` takes the canonical
term-list operations as parameters, with soundness laws supplied only in
the companion. The companion instantiates these generic executable definitions
with hex-mv-poly's list arithmetic and hex-mv-gcd's polynomial quotient.
No polynomial-specific public alias or division implementation is added to
hex-bareiss, and its dependency list does not grow.

**Producer and witness.** Generalise `detWitness` and its witness data over
the coefficient type, preserving the integer API. The producer runs in compiled
code, with the coefficient/order context of the `MvPoly` carrier contract
below, including `LawfulGcdOps C`. It performs row-pivoted fraction-free
elimination on `[P | I]`, applying each swap and each update
`Hex.exactDiv (pivot * x - factor * y) previousPivot` to both blocks.
`HexMvGcd/Divide.lean` supplies `Hex.MvPoly.instDiv` and
`Hex.MvPoly.instExactDivLaws`; divisions are exact by the same minor invariant.
The producer retains the transform and re-checks its output before returning
it. Pivot search, polynomial normalisation and exact division are executable
work, never kernel replay.

For a nonsingular polynomial matrix the witness contains the row swaps, the
`i + 1` leading polynomial entries of each lower triangular transform row,
and a polynomial value `d = det P`. Here nonsingular means that `det P` is
not the zero polynomial, equivalently invertibility over the fraction field
of the polynomial domain. Singular means an identically zero determinant,
not vanishing at a selected valuation. In that case echelon elimination
returns a nonzero polynomial left kernel vector `v` with `v · P = 0` and
value zero. Even though the fraction field describes singularity, every
witness entry is in the polynomial ring. No specialisation is used to choose
or certify the branch. The `0 × 0` witness is triangular with value one.

**Kernel form.** `checkDetPolyList` is the polynomial analogue of
`checkDetList`: the matrix, transform, value and singular vector are nested
lists of canonical polynomial term lists. A term has an exponent list of
length `k` and a coefficient in the provider's kernel representation (`Int`
or canonical `Nat` residue). The check validates matrix/witness dimensions,
swap bounds and distinctness, exponent lengths, strictly ordered monomials,
nonzero coefficients and canonical coefficient encodings. Zero is the empty
term list; duplicate monomials and stored zero terms are rejected. The list
layer supplies structural addition, negation, multiplication, scalar
multiplication and equality with denotation laws, and preserves canonicality.

As in `checkDetList`, the checker itself applies the swaps and obtains their
sign. For each row `i` of `L`, it checks that the first `i` products with
columns of `σP` vanish, obtains `uᵢ` from column `i`, and requires the last
entry `lᵢ` of the transform row to be nonzero. For `n > 0`,
it checks `l₀ = 1`, `lᵢ₊₁ = uᵢ` for `i < n - 1`, and
`d = sign σ * uₙ₋₁` by canonical list equality. These are the diagonal
relations of this producer, already recorded for the integer witness above.
The general determinant identity `(∏ lᵢ) * d = sign σ * ∏ uᵢ` follows
in the soundness proof by cancellation; neither diagonal product is expanded
in the kernel. Forming them would multiply supports of successive minors,
far beyond the support of the determinant itself. For `n = 0` the checker
requires `d = 1`. A singular witness instead checks a nonzero entry of `v` and every component of `v · P = 0`. The cost is
about `n³ / 3` polynomial products for triangularisation and `n²` for a
singular vector, plus canonicality and final value checks, at the realised
minor support and coefficient sizes. There are no divisions in the checker.

Every definition on the kernel arithmetic path is `@[expose]` and structurally
recursive on lists of `Nat`/`Int`, per
[matrix-tactics §Kernel discipline](../../SPEC/matrix-tactics.md#kernel-discipline).
In particular converting reference polynomials to lists is producer work;
the kernel receives quoted lists and does not traverse `MvPoly` trees or
monomial vectors. The companion identifies the quoted polynomial matrix
with the denoted row list definitionally. Rationals use the companion's proved
coefficient denominator-clearing pass to supply integer polynomial rows and
positive scales; the kernel checks the resulting integer lists, including
cross-multiplied target equality. No rational polynomial list arithmetic is
assumed. As specified in the companion, positive characteristic
requires the residue provider and its canonical list operations.

The proposed `checkDetPolyList_sound`, concluding `Hex.Matrix.det P = d`
through denotation, triangular determinant lemmas and cancellation over the
polynomial domain, lives exclusively in hex-bareiss-mathlib. The reference
Leibniz determinant is a specification in that theorem, never kernel
computation. This executable library adds no determinant correspondence
theorem and never uses `bareissWith` or `det` on `Hex.Matrix (MvPoly …)` as
a kernel check. Expression swell remains governed by
[§Symbolic coefficient growth](#symbolic-coefficient-growth); operation counts
do not promise bounded support or a timing win over Bird's algorithm.

## Mathlib-free vs. Mathlib-bridge proof surface

The following theorems live exclusively in the `*-mathlib` bridge layer and
**must not** be restated, reproven, or specialized inside `hex-bareiss`,
regardless of how convenient that would be for a downstream Mathlib-free
consumer. Generalizing the coefficient ring does not move the boundary: it moves
the same theorems, with `Int` replaced by `R`.

| Theorem (or theorem family) | Mathlib-free layer obligation |
|---|---|
| `bareissWith_eq_det`, and any equation of the form `bareissWith quot M = det M` over the Leibniz `det`, at any carrier including `Int` | forbidden in `hex-bareiss` |
| `det_eq`, i.e. `Hex.det M = Matrix.det (matrixEquiv M)` | forbidden in `hex-bareiss` |
| Desnanot–Jacobi in any form (unscaled, scaled, bordered-minor) that connects `Hex.det` of submatrices through an adjugate identity | forbidden in `hex-bareiss` |
| `NonzeroBareissPivots`, `BareissNoPivotInvariant`, and the no-pivot bordered-minor invariant proof chain culminating in `bareissNoPivotWith_eq_det` | forbidden in `hex-bareiss` |

A Mathlib-free consumer that *appears to require* a theorem on this list is the
failure mode caught by
[PLAN/Conventions.md §Library placement is a hard precondition question 2](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#library-placement-is-a-hard-precondition).
The repair is to relocate the consumer's bridging theorem to the sibling
`*-mathlib` layer (or to redesign the consumer's proof surface), **not** to
manufacture a Mathlib-free proof of the listed theorem.

Row-operation lemmas (`det_rowSwap`, `det_rowScale`, `det_rowAdd`, in
`hex-determinant`) and equalities purely between Hex-local definitions are
unaffected by this list. So is `stepMatrixWith_borderedMinor_update`, which
stays Mathlib-free: it takes the determinant identity as the hypothesis
`hexact` rather than proving it.

**Proof path governs placement, not just statement.** A theorem whose
*statement* is purely Hex-local (e.g. `bareiss (rowAdd M i j c) = bareiss M`,
with `det` nowhere mentioned) still belongs in the bridge layer if its only
realistic Mathlib-free proof requires re-deriving an entry from the forbidden
list above. The shortest-path test in
[PLAN/Conventions.md §Library placement is a hard precondition question 2](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#library-placement-is-a-hard-precondition)
governs **proof obligations**, not statement surface.

## Proof that `bareissWith quot M = det M`

Via the bordered-minor invariant, unchanged in shape from the `Int`
development. Define
`μ(k; i, j) := det M[rows 0..k-1 ∪ {i} | cols 0..k-1 ∪ {j}]`. The invariant
`a⁽ᵏ⁾_{ij} = μ(k; i, j)` holds by induction, where the induction step is the
Desnanot–Jacobi identity:

```
μ(k+1; i, j) · μ(k-1; k-1, k-1)
  = μ(k; k, k) · μ(k; i, j) − μ(k; i, k) · μ(k; k, j)
```

for `i, j ≥ k+1`, with `μ(-1; -1, -1) := 1`. At `k = n-1` this gives `det M`.
Exactness follows: the numerator is `μ(k-1; k-1, k-1) · μ(k+1; i, j)`, and
`hquot` returns `μ(k+1; i, j)` because the previous pivot `μ(k-1; k-1, k-1)` is
nonzero.

The only determinant identity consumed is
`HexMatrixMathlib.desnanot_jacobi_borderedMinor`, which is already stated over
an arbitrary Mathlib `CommRing` and needs no nondegeneracy hypothesis. **No new
determinant identity is required by this generalization**, and the audited
Desnanot-Jacobi statement itself needs no change. One declaration beside it does:
`HexMatrixMathlib.bareissExactDiv_borderedMinor_of_mul_eq` in `CorePlucker.lean`
is fixed to `Int` and must be generalized in place, with an `Int` corollary
retained. In particular the general Sylvester identity remains
absent and remains unnecessary: fraction-free elimination uses only the `2 × 2`
bordered-minor case, which is Desnanot-Jacobi. Do not introduce a second
determinant identity development, and do not rename anything to claim Sylvester;
see
[hex-determinant-mathlib §Sylvester's determinant identity: absent](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md).

Do not reprove Desnanot-Jacobi locally. Track
https://github.com/leanprover-community/mathlib4/pull/37716
(`Mathlib.LinearAlgebra.Matrix.Determinant.DesnanotJacobi`). If merged, import
it; otherwise prove using Mathlib's `Matrix.adjugate`.

Implementation split (the proofs live in the Mathlib bridge layer):
1. `bareissNoPivotWith_eq_det`: under nonzero pivots, prove via the invariant +
   Desnanot–Jacobi.
2. `bareissWith_eq_det`: public API with row pivoting. If pivot search fails at
   step k, prove `det M = 0`; otherwise compose row swaps into a permutation,
   apply the no-pivot theorem, use `det_rowSwap` for sign.

## Supported coefficient carriers

The `Int` aliases are only one instantiation of `bareissWith`. This revision
pins the following carrier surface; it does not claim that every future field
or quotient-ring type in the monorepo is automatically a supported Bareiss
carrier:

| carrier | quotient and exact-law provider | assumptions beyond the carrier's ring operations | required fixture family | exact oracle |
|---|---|---|---|---|
| `Rat` | `Hex.exactDiv`; `Hex.instExactDivLawsField` | none beyond the core `Lean.Grind.Field Rat`, `Div Rat`, and `DecidableEq Rat` instances | rational matrices covering ordinary elimination, row swap, singularity, `n = 0`, and `n = 1` | python-flint `fmpq_mat.det()` |
| `ZMod64 p` | `Hex.exactDiv`; the field instance from `HexPolyFp.PrimeField`, then `Hex.instExactDivLawsField` | `[ZMod64.Bounds p] [ZMod64.PrimeModulus p]` | the rational shapes modulo one fixed prime below `2^31`, plus coefficient reduction and a pivot that is nonzero only after reduction | python-flint `nmod_mat.det()` |
| `DensePoly F` | `Hex.exactDiv`; polynomial `Div` plus `Hex.instExactDivLawsDensePoly` in `HexResultant.ExactDiv` | `[Lean.Grind.Field F] [DecidableEq F]`; concretely exercise `F = Rat` and `F = ZMod64 p` | univariate polynomial matrices with a nonconstant previous pivot and nontrivial exact polynomial quotients | SymPy `Matrix.det(method="berkowitz")` over `QQ[x]` and `GF(p, symmetric=False)[x]` |
| `ZPoly` (`DensePoly Int`) | `Hex.exactDiv`; the same polynomial `Div` and recursive exact-law instance over `Hex.instExactDivLawsInt` | no extra coefficient hypothesis | integer-polynomial matrices with nonconstant pivots, row swap, and a singular case | SymPy `Matrix.det(method="berkowitz")` over `ZZ[x]` |
| `MvPoly n R cmp` | `Hex.exactDiv`; `Hex.MvPoly.instDiv` and `Hex.MvPoly.instExactDivLaws` in `HexMvGcd.Divide` | `[Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] [IsMonomialOrder cmp] [LawfulGcdOps R]`; concretely exercise `R = Int` and `R = Rat` | sparse two- and three-variable matrices with mixed monomials, nonconstant previous pivots, row swap, and singularity | SymPy `Matrix.det(method="berkowitz")` over `ZZ[x0, ...]` and `QQ[x0, ...]` |

Every row uses the same law term:

```lean
fun a b hb => Hex.exactDiv_mul_right a hb
```

The generic provider declarations behind the concrete rows are not inferred
field-only approximations. In particular, polynomial `Div` is induced by
coefficient `Div`, while the recursive `ExactDivLaws (DensePoly R)` instance
requires `[Lean.Grind.CommRing R] [DecidableEq R] [Div R]
[ExactDivLaws R]`; this is why its separate `ZPoly` specialization works. The
`MvPoly` instance inherits the full section context listed above and requires
`LawfulGcdOps R`, not merely `GcdOps R`. Conformance fixes
`Hex.Mono.grevlex`, whose existing `IsMonomialOrder` instance supplies the
required well-founded order laws.

### Placement in the dependency graph

The exact-division implementations remain where they are: dense-polynomial
division in `HexResultant`, above `HexPoly`, and multivariate division in
`HexMvGcd`, above `HexMvPoly` and `HexResultant`. Nothing in `HexBareiss/*`
imports either provider, and no carrier-specific public alias is added there.

Direct typechecking and value guards live in the existing build-only
`conformance/HexBareiss/Conformance.lean`; the carrier emitter is a separate
`conformance/HexBareiss/EmitCarrierFixtures.lean` executable root, and the
bench registrations live in the existing `bench/HexBareiss/Bench.lean`. These
modules may import `HexBareiss` together with `HexPolyFp.PrimeField`,
`HexResultant.ExactDiv`, and `HexMvGcd.Divide`; they are neither part of the
published `HexBareiss` umbrella nor owners in `libraries.yml`. The conformance
module remains listed in the `HexConformance` glob and the emitter and bench are
explicit Lake executable roots.

This placement exercises the providers without creating an upward production
dependency. `scripts/check_dag.py` enforces the production graph from
`libraries.yml`; the integration paths have no production owner (while its
sealed-import check still scans them). If a carrier specialization later
becomes reusable API, it must move to a production library already above both
dependencies, never into `hex-bareiss`. `ZPoly` fixtures use the underlying
`DensePoly Int` type directly, so this test-only integration does not import
`HexPolyZ` merely for an abbreviation.

## Changes required of a later implementation

These are obligations on the implementation issue, not on this SPEC. Until it
lands, `HexBareiss/README.md` and `HexBareissMathlib/README.md` continue to
describe the shipped `Int`-only surface, which is accurate; they are updated by
the implementation, not ahead of it.

### Conformance changes

The existing `Int` fixture records stay byte-identical: a re-emission change is
a regression. `conformance/HexBareiss/Conformance.lean` also checks
`bareissWith Hex.exactDiv M = bareiss M` on every existing matrix.

The added families are emitted separately by
`hexbareiss_emit_carrier_fixtures` to
`conformance-fixtures/HexBareiss/carriers.jsonl`. A new
`scripts/oracle/matrix_carriers.py` tuple in `scripts/ci/run_oracles.sh` checks
that complete stream; the existing integer emitter, fixture and
`matrix_flint.py` tuple remain byte-identical. The carrier driver uses
python-flint for scalar rational and modular records. For polynomial records it
constructs an exact SymPy matrix and explicitly calls
`Matrix.det(method="berkowitz")`, an independent division-free recurrence
rather than SymPy's default Bareiss method. It never asks an expression
simplifier to decide equality.

Records use canonical ascending coefficient arrays for `DensePoly`, ordered
exponent-vector terms for `MvPoly`, and residues normalized to `[0, p)` (using
`GF(p, symmetric=False)`). Complete canonical results are compared
coefficientwise, with no sampling or heuristic simplification.

SymPy and python-flint are already installed and preflighted by the existing
single oracle job. The carrier tuple extends that job; there is no new package,
workflow, job, or matrix.

### Manual changes

`HexManual/Chapters/HexBareiss.lean` cites `Hex.Matrix.BareissData`,
`BareissData.sign`, `BareissData.det`, `bareissData`, `bareiss`,
`bareissNoPivotData`, `bareissNoPivot`, `borderedMinor`,
`bareissData_eq_finish_pivotLoop`, `bareiss_eq_bareissData_det`,
`HexMatrixMathlib.bareiss_eq_det` and `HexMatrixMathlib.bareissDet_eq_det`
through `{docstring}` and `{name}` roles. Every one of those names survives the
generalization, so no chapter rewrite is forced; the docstrings they render do
change, and the chapter must still build.

### Benchmark changes

`runBareissDet*` and the paired FLINT rungs keep their current definitions on
`Int` unchanged: they are the instrument that detects a regression, so they may
not be rewritten in the same change that could cause one.

Add an internal A/B rung, `bareissWith Hex.exactDiv` at two sizes in the upper
half of the existing ladder (the entries are multi-limb there, which is where
`lean_int_div_exact` can differ), and record the ratio against the matching
`runBareissDet` rung in `reports/hex-bareiss-performance.md`. This is an
internal comparison, not an external comparator, so
the existing `Int` entry in `HexBareiss.phase4.comparators` is unchanged.

Both rungs stay Mathlib-free and extend the script of the existing single
bench job; no new workflow, job, or `strategy.matrix` (see
[SPEC/CI.md](https://github.com/kim-em/hex-dev/blob/main/SPEC/CI.md)). If the
two extra rungs push the `Bench verify` step past its wallclock cap, they belong
on the scheduled timing workflow instead, per
[SPEC/benchmarking.md](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md).

Every added carrier also has a required lean-bench family. Scalar carriers
sweep matrix dimension; dense-polynomial carriers sweep dimension and entry
degree at fixed coefficient support; multivariate carriers sweep dimension and
term count at fixed arity and total degree. Each family includes matrices whose
second and later steps divide by a nonconstant previous pivot, so the benchmark
measures exact division rather than only ring arithmetic.

| target family | external comparator | class |
|---|---|---|
| `runBareissRat` | python-flint `fmpq_mat.det()` | informational |
| `runBareissMod` | python-flint `nmod_mat.det()` at the identical prime | informational |
| `runBareissDenseRat`, `runBareissDenseMod` | SymPy Berkowitz determinant over the identical exact polynomial domain | informational |
| `runBareissZPoly` | SymPy Berkowitz determinant over `ZZ[x]` | informational |
| `runBareissMvInt`, `runBareissMvRat` | SymPy Berkowitz determinant over the identical multivariate polynomial domain | informational |

All external comparisons are informational, never Phase-4 gates. FLINT's
determinant selection is structurally different from the prescribed Bareiss
recurrence, while the SymPy calls additionally include Python process overhead
and independent algorithm selection. Result hashes cover the full canonical
answer.

The SymPy and python-flint registrations use a persistent-subprocess carrier
driver, following `Hex.BenchOracle.Flint`. Because process-call benchmarks have
an `IO` body, every point in a dimension/degree or dimension/term-count sweep
is a separate `setup_fixed_benchmark`; there is no two-dimensional parametric
`Nat → IO α` registration. The implementation PR records trivial-request
overhead and overhead-adjusted ratios in
`reports/hex-bareiss-performance.md §Comparator ratios`. These informational
external rungs are scheduled-only; the matching Hex registrations still build
and verify in the ordinary bench target.

Over a field, Bareiss is primarily a conformance surface: fraction-free
elimination buys no denominator control there and should not be inferred to be
the preferred field determinant algorithm from these benchmark results.

### Symbolic coefficient growth

The bordered-minor invariant in [§Complexity](#complexity) is also the symbolic
growth contract: at state index `k`, every active entry is the corresponding
`borderedMinor source k`, a `(k+1) × (k+1)` input minor. Thus fraction-free
elimination introduces no rational denominators and does not store accumulated
products unrelated to input minors.

This does **not** claim compact expressions. Canonical dense or sparse
polynomial arithmetic may expand a minor into many monomials, and the transient
difference of products can be larger still before exact division. Controlling
that expression swell is outside this work. Evaluation/interpolation,
multimodular reconstruction, and other modular symbolic determinant techniques
belong to a later SPEC; neither the conformance plan nor the benchmark plan here
silently substitutes one of them for Bareiss.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_mat_det` via python-flint | informational | the `Int` Bareiss determinant targets (`runBareissDet` and the paired FLINT rungs) |
| FLINT `fmpq_mat.det` via python-flint | informational | `runBareissRat` |
| FLINT `nmod_mat.det` via python-flint | informational | `runBareissMod` |
| SymPy Berkowitz exact-domain determinant | informational | the dense- and multivariate-polynomial Bareiss targets |

FLINT's `fmpz_mat_det` is a structurally distinct reference for integer matrix
determinant: FLINT uses multimodular reduction (determinant modulo many small
primes, then CRT), with a different asymptotic and constant-factor profile from
Bareiss fraction-free elimination. The comparator is `informational`: the ratio
is recorded for orientation but is not a Phase-4 gate. Wired via a
persistent-subprocess Python driver per
[the benchmarking spec's "External comparators" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#external-comparators).

Structured metadata in the project
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml)
under `HexBareiss.phase4.comparators` records the carrier-scoped additions when
their implementation lands. See
`reports/hex-bareiss-performance.md` for the comparator ratio ladder.
