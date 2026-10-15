# hex-pos-def

Exact positive-definiteness decisions for integer and Gaussian-integer
matrices, with independently checkable positive and negative certificates.
The general algorithm is fraction-free elimination without pivot swaps.
An explicitly selected positive-vector method supplies smaller certificates
for symmetric matrices with nonpositive off-diagonal entries.

## Scope and dependencies

`HexPosDef` is Mathlib-free. Its direct dependencies are `HexBasic`,
`HexArith`, `HexMatrix`, and `HexRowReduce`. Its namespace is `Hex.PosDef`.
Reuse matrix operations, structural list arithmetic, common-denominator
encodings, integer exact division, and rational linear solving from these
libraries. The public operations below belong here. Their interpretation
as `Matrix.PosDef` and the `pos_def` tactic belong to
[hex-pos-def-theory](../../HexPosDefTheory/SPEC/hex-pos-def-theory.md).

Own the no-swap elimination and its early negative result in this library.
Do not change or call the row-pivoted determinant producer in `HexBareiss`.
No separate determinant computation, root-coordinate table, numerical approximation,
external CAS, or new extern declaration is needed at runtime.

Semidefiniteness, inertia, symbolic entries, algebraic coefficients, sparse
matrix representations, and Cartan symmetrizer discovery are outside this
contract. A zero quadratic value is sufficient to refute positive
definiteness. Classifying all eigenvalue signs is a different operation.

## Scalars and input encoding

The real arithmetic path uses `Int` directly. Supply a `Gaussian` type
in `Hex.PosDef`, with integer `re` and `im` components, exact equality,
addition, negation, multiplication, conjugation, zero, and one. Its
arithmetic is the usual arithmetic of `a + b i`. Keep this representation
local to the library rather than introducing another library for one
consumer. Executable matrices use the `Hex.Matrix` API.

For rational input, choose one positive natural denominator `s` for the
whole matrix and encode `B = s • A` as integer rows. For complex input,
clear denominators of both components with the same `s`, producing
Gaussian-integer rows. A real matrix embedded in a complex carrier can
use the integer path. Preserve the dimension and denominator with the
quoted input. Exact row lengths and `s > 0` are validation obligations.

Reuse `Hex.Matrix.Lists.ScaledRows` and its cross-multiplication checks for
real rational data. Supply the analogous component checks for complex
rational data. These establish the entry equations without normalizing
rationals inside elimination or certificate dot products. Independent
row scaling is not admissible: it need not preserve Hermitian symmetry.
The Theory library proves transport along the checked equation `s • A = B`.

## Certificates and public operations

Use the following data and operation names under `Hex.PosDef`. Here `R`
is `Int` or `Gaussian`, and all certificate rows are lists.

| Name | Data or contract |
| --- | --- |
| `PositiveCert R` | `triangular T`, containing the leading `i + 1` entries of transform row `i`, or `positiveVector v`, containing an integer vector. |
| `NegativeCert R` | `notHermitian i j`, or `nonpositive v` with a vector over `R`. |
| `Certificate R` | `positive c` or `negative c`, preserving which assertion was certified. |
| `Method` | `triangular` or `positiveVector`, with `triangular` the default. |
| `Error` | An unsupported-method reason or a producer-certificate rejection, kept distinct from mathematical classifications. |
| `Int.checkPositive`, `Gaussian.checkPositive` | Check a positive certificate against a dimension and the original integer or Gaussian-integer row list. |
| `Int.checkNegative`, `Gaussian.checkNegative` | Check a negative certificate against the same input representation. |
| `Int.certify` | Classify a square executable integer matrix using the selected method, returning `Except Error (Certificate Int)`. |
| `Gaussian.certify` | Classify a square executable Gaussian-integer matrix using the general method, returning `Except Error (Certificate Gaussian)`. |

`Gaussian.checkPositive` rejects the `positiveVector` constructor. Real
complex inputs that use that method are encoded by the integer path and
interpreted in the target carrier by the Theory library.

Both checkers require the input to have exactly `n` rows of length `n`.
A triangular certificate must have exactly `n` rows, with row `i` of
length `i + 1`. A vector must have exactly `n` entries. Reject malformed
shapes before using padding or truncated dot products. Coordinates in a
`notHermitian` certificate must be in range.

Distinguish an unsupported specialized method from a rejected producer
certificate. An unsupported method carries no mathematical result. A
rejected certificate is an implementation error. Resource interruption
also supplies no classification. Successful producers recheck their
candidate using the corresponding checker before returning it. Prove
`Int.certify_check` and `Gaussian.certify_check` for this self-validation,
independently of any claim that the elimination quotients are correct.

## General positive checker

Check `B = B*`, where `*` is transpose for integers and conjugate transpose
for Gaussian integers. Let `T` be the lower-triangular matrix obtained by
padding each certificate row with zeros. For every row `i`, check

```text
dot(T[i], B.column j) = 0                 for j < i
u[i] = dot(T[i], B.column i)
d[i] = u[i] * conjugate(T[i,i])
imaginaryPart(d[i]) = 0 and realPart(d[i]) > 0.
```

The integer checker performs only the real comparison. The computed `u`
and `d` are not additional witness arrays. Positivity implies `T[i,i] != 0`.

These conditions make `U = T * B` upper triangular. Both `U * T*` and
`T * B * T*` are the same matrix, which is upper triangular and Hermitian.
It is therefore diagonal, with diagonal `d`. This is the congruence
certificate used by the soundness theorem. The checker does not multiply
two full matrices or recompute leading principal determinants.

For a positive diagonal input, use the same certificate with `T = 1`. Detecting
this input may avoid elimination but adds no certificate constructor or
separate public method. The empty matrix has the empty positive certificate.

## General producer

First check Hermitian symmetry, returning a mismatching coordinate when
it fails. Otherwise initialize the left block to `B`, the right block to
the identity, and the preceding pivot to `1`. At step `k` the left block
has zeros below earlier pivots and equals the right block times `B`.

The diagonal pivot `p` is real. If `p <= 0`, return a negative certificate
as described below, without dividing by `p`. If `p > 0`, eliminate each
row `i > k` in both blocks with the Bareiss update

```text
row[i] := (p * row[i] - left[i,k] * row[k]) / previousPivot.
```

Use the original `left[i,k]` for both updates. Earlier rows remain fixed.
The bordered-minor invariant for the augmented matrix `[B | I]` proves
that the divisions are exact. For Gaussian entries, the preceding pivot
is a nonzero real integer, so divide the two integer components exactly.
The invariant must establish that all diagonal pivots are real, rather
than discarding an imaginary part. An invariant violation is an error.

After the last positive pivot, the right block is `T`, and the left block
is `U = T * B`. Emit the lower-triangular rows of `T`. Their diagonal is
`1, Delta[1], ..., Delta[n-1]`, and the diagonal of `U` is
`Delta[1], ..., Delta[n]`, where `Delta[k]` is the leading principal minor
of size `k` of `B`. This invariant explains the update and its coverage.
The certificate checker does not evaluate those determinants.

No row swaps or symmetric pivot search are needed for this decision.
If every pivot is positive, the positive certificate applies. Otherwise
the first nonpositive pivot supplies a refutation, even when the whole
matrix is nonsingular.

## Negative checker and producer

For `notHermitian i j`, check `B[i,j] != conjugate(B[j,i])`.
For `nonpositive v`, check that some entry of `v` is nonzero, compute
`q = conjugate(v) dot (B * v)`, and check that `q` is real and `q <= 0`.
The integer path uses its ordinary integer order. This check accepts any
valid counterexample, independently of the producer or an elimination
prefix.

At the first nonpositive pivot `k`, all preceding pivots are positive.
Row `t` of the right block is supported on the first `k + 1` coordinates,
and its last entry `l` is the preceding positive principal minor (or `1`
when `k = 0`). Its products with earlier columns vanish. Consequently,

```text
t * B * conjugate(t) = p * conjugate(l) <= 0.
```

Pad `v = conjugate(t)` with zeros to dimension `n`. It is nonzero because
`l != 0`, and the negative checker verifies it directly. Do not infer a
kernel vector of the full matrix from a zero leading pivot.

## Positive-vector method

This explicitly selected method applies to real symmetric matrices with
nonpositive off-diagonal entries and positive goals. Generate a rational
solution to `B * v = 1` using the existing exact rational solve, then
clear its denominators positively. Check the resulting integer vector
with the following independent conditions:

```text
B is symmetric
B[i,j] <= 0 for i != j
v[i] > 0 for every i
(B * v)[i] > 0 for every i.
```

The checker accepts any vector meeting these conditions, not just the
canonical solution or a vector whose product is constant. A failed solve,
a nonpositive coordinate, or an input outside this method's scope returns
an unsupported-method result. It does not refute positive definiteness or
automatically invoke another method. There is no requirement to retain
general elimination state or run both producers.

For `V = diagonal v`, soundness follows from

```text
x^t V B V x = sum_i v[i] (B*v)[i] x[i]^2
              + sum_(i<j) (-B[i,j]) v[i] v[j] (x[i]-x[j])^2.
```

The Theory library proves this identity and the integer descent using
`C = product_i v[i]` and `c[i] = product_(j != i) v[j]`, so `v[i]*c[i] = C`.
For complex test vectors of a real matrix, replace squares by squared
absolute values. The integer certificate is unchanged.

## Kernel reduction and complexity

Use structural list recursion and primitive integer arithmetic on the
arithmetic checker path. The Gaussian checker performs a fixed number of
integer operations per scalar operation. Do not traverse `Hex.Matrix`,
`Array`, `Vector`, `Finset`, or a matrix-function representation inside
certificate dot products. Definitions reduced by the checker must be
exposed to the kernel. Entry identification and denominator checks are
separate from these arithmetic loops.

The general producer uses `O(n^3)` scalar arithmetic operations and
`O(n^2)` scalar storage. The plain positive checker uses `O(n^3)` arithmetic
operations on a certificate with `n(n+1)/2` scalars. Symmetry checking and
negative-vector checking use `O(n^2)` arithmetic operations. The
positive-vector checker uses `O(n^2)` operations and `O(n)` witness scalars.
Its exact solve has the existing solver's cost.

Let `H >= 1` bound the absolute values of the integer components after
denominator clearing. The augmented-minor invariant bounds the bit length
of general transform and elimination entries by
`O(n (log(n+1) + log(H+1)))`: use Hadamard's bound on minors of `[B | I]`,
with complex entry magnitude at most `sqrt(2) * H` for Gaussian inputs.
Products and sums in the checker also contribute their operand-size cost.
These arithmetic bounds are not a claim of cubic elapsed time. Do not
replay exact division, solving, or elimination in the kernel.

## Conformance and performance

Use the existing conformance profiles in [testing](../../SPEC/testing.md).
`conformance/HexPosDef/Conformance.lean` covers both producers, all checker
constructors, and failure of the explicitly selected vector method. Keep
the corpus small: typical positive matrices, first and later nonpositive
pivots, the empty matrix, a non-Hermitian matrix, and malformed certificates
exercise the distinct behavior. Include genuine Gaussian inputs to catch
missing conjugations. Mutate a sign, a shape, and a zero/nonzero claim to
exercise rejection rather than merely comparing producer outputs.

Extend the existing `scripts/oracle/matrix_flint.py` for a bounded exact
classification cross-check. For real symmetric data, compare with positivity
of all leading principal determinants computed by FLINT. For complex
Hermitian data, the oracle may use the rational realification
`[[Re B, -Im B], [Im B, Re B]]`. Check negative witnesses directly as well.
Use the existing fixture stream and failure-report conventions. Do not
introduce another oracle framework or numerical tolerance.

`bench/HexPosDef/Bench.lean` is Mathlib-free and measures the general
producer and checker on one representative integer Gram family at
dimensions `8`, `16`, and `32`. Use `B = C^t*C + I`, with deterministic
small integer entries in `C`, and include the operand growth when explaining
the arithmetic count. A fixed Gaussian example exercises the complex path
without requiring another scaling study. Integrate through the existing
bench and oracle scripts, with no new workflow or top-level job.

The companion owns the small complete-tactic timing table. Neither method
has a measurement prerequisite for being exposed. Profiling, a benchmark
cross-product over carriers, or an arbitrary timing threshold is not a
release requirement.

## Manual

Document the executable API, certificate meanings, and the two methods in
`HexManual/Chapters/HexPosDef.lean`. Include the Theory correspondence and
the live tactic recipes required by
[hex-pos-def-theory](../../HexPosDefTheory/SPEC/hex-pos-def-theory.md#manual) in the same chapter.
Keep exhaustive examples and malformed-certificate regressions in tests.
