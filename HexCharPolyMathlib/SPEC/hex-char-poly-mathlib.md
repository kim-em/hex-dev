# hex-char-poly-mathlib

Mathlib correspondence layer for
[`hex-char-poly`](https://github.com/leanprover/hex-char-poly).  It identifies
the executable Samuelson--Berkowitz output with Mathlib's
`Matrix.charpoly`, then transports the characteristic-polynomial theorems that
are intentionally absent from the Mathlib-free computational package.

## Main correspondence

```lean
namespace HexCharPolyMathlib

theorem equiv_charPoly (A : Hex.Matrix R n n) :
    HexPolyMathlib.equiv (Hex.Matrix.charPoly A) =
      Matrix.charpoly (HexMatrixMathlib.matrixEquiv A)

end HexCharPolyMathlib
```

This theorem is coefficient-generic. `MvPoly` obtains the required Mathlib
`CommRing` from `HexMvPolyMathlib`, and `RationalFn` obtains a Mathlib `Field`
from `HexRationalFnMathlib`, so those carrier specializations need no new
characteristic-polynomial lemma. There is currently no global Mathlib
`CommRing` instance for executable `DensePoly`; the computational carrier
coverage does not wait for that separate bridge. No carrier-specific
`equiv_charPoly` theorem or executable conformance suite is added here; the
carrier fixtures remain owned by `HexCharPoly`.

Importing the umbrella extends `char_poly` to closed
`Matrix (Fin n) (Fin n) Int` literals: `!![…]`, `Matrix.of ![…]`,
`fun i j => …`, and `Matrix.ofArray`, possibly behind transparent definitions
within the shared recognizer's eight-unfolding budget:

```lean
open Matrix Polynomial

def A : Matrix (Fin 2) (Fin 2) Int := !![1, 2; 3, 4]

#check char_poly A

example : A.charpoly = X ^ 2 - 5 * X - 2 := by
  char_poly

example : True := by
  char_poly A
  -- poly : Polynomial Int
  -- charPoly_eq : A.charpoly = poly
  trivial
```

Direct equality goals accept ordinary `Polynomial Int` expressions built from
`X`, `C`, integer numerals, addition, subtraction, multiplication, negation,
and natural-literal powers.  Transparent named definitions made from those
forms are unfolded. The elaborator materializes the finite Mathlib matrix for
compiled evaluation from the shared literal layer's recognized entries,
then emits the packed list certificate. The shared
`HexMatrixMathlib.Literal` layer identifies `!![…]` and `Matrix.of ![…]` with
`ofLists` definitionally. Closed function and array literals use the shared
entrywise identification once, outside the arithmetic checker. The result is
transported through `equiv_charPoly`; Mathlib's noncomputable `Matrix.charpoly`
is never evaluated.

The proof follows the executable recursion on trailing principal blocks.  Its
step theorem proves the bordered determinant identity through the adjugate
coefficient recurrence, identifies the row--block--column moments with the
Toeplitz column, and then inducts over the block size.  There are no axioms or
unfinished proof obligations.

## Kernel certificate and measurements

`HexCharPolyMathlib/Kernel.lean` proves `charpoly_eq_of_checkList` for
`Matrix (Fin n) (Fin n) ℤ` presented by the shared `ofLists` definition.
It combines the core list-checker soundness theorem with `equiv_charPoly`.
An explicit equality between the core and Mathlib integer ring structures
handles their different numeral-instance definitions. The result record
(`Certified`, also available as `CharPolyResult`) keeps `poly` and
`charPoly_eq` projections.

The fresh-module probes under `bench/HexCharPolyMathlib/ProofProbe` use
`random.Random(10212 + n)` and signed 8-bit entries for dimensions 4, 8, 16,
and 32. The three arms are the frozen original frontend, the scalar list
checker study, and the packed frontend. The scalar arm checks only its
certificate; the frontend arms also include literal identification and the
polynomial result. There is no Mathlib characteristic-polynomial tactic to
use as a competitor. The rank measurements in the archived study explain
operation counts and are not an acceptance threshold.

The external runner preregisters kernel targets of 1 second at dimension 16
and 10 seconds at dimension 32, with a separate 300-second operational timeout.
It uses an automatically leased CPU on the shared host, six adjacent pairs
with alternating AB/BA order, and retains host load and raw logs. A timed-out
arm is recorded and its later pairs are skipped. Kernel time is Lean's
`type checking` profiler total; wall time also includes imports, production,
elaboration, and Lake overhead. The targets guide further optimization rather
than withholding the tactic when a target is missed.

On shared host `chungus2`, leased CPU 92, Lean
`v4.34.0-rc2`, the kernel measurements are:

| Dimension | Reference | Reference median | Packed median | Median paired speedup |
|---|---|---:|---:|---:|
| 4 | Scalar lists | 8.2 ms | 16.2 ms | 0.52× |
| 4 | Original frontend | 47.4 ms | 16.0 ms | 2.97× |
| 8 | Scalar lists | 76.9 ms | 68.2 ms | 1.08× |
| 8 | Original frontend | 850.0 ms | 70.7 ms | 11.38× |
| 16 | Scalar lists | 1.63 s | 573.5 ms | 2.85× |
| 16 | Original frontend | 20.45 s | 587.0 ms | 34.96× |
| 32 | Scalar lists | 29.75 s | 5.17 s | 5.69× |
| 32 | Original frontend | 300 s wall timeout (retained) | — | unavailable |

Each completed row contains six adjacent pairs; packed medians are specific
to that row's reference. Speedup is the median of the six within-pair ratios,
not the ratio of medians. The identical original size-32 frontend reached the
operational wall timeout before reporting a kernel total in the retained
cached-certificate sweep. The manifest references that result and skips its
six subsequent pairs. This is an end-to-end timeout, not a kernel lower bound.

The packed frontend meets both kernel targets and improves on the scalar
checker at 16 and 32 and the original frontend wherever it completes. At 4,
the scalar certificate alone is cheaper than the full packed frontend; at 8
the measured times are comparable. These are host-specific observations from hashed working-tree sources, with no
release-quality verdict. All 84 completed samples, paired deltas, source
provenance, artifact sizes, axiom audits and raw logs are retained in
[`evidence/packed`](../../bench/HexCharPolyMathlib/ProofProbe/evidence/packed).
The original scalar study, the 86-sample sweep with cached packed columns,
and all completed optimization probes are retained alongside the final sweep.
Two adjacent cache-removal pairs give comparable size-32 kernel times
(cached 4.82/5.01 s, uncached 4.90/4.75 s), while reducing the `.olean` from
4,566,376 to 3,150,040 bytes; the smaller certificate is used above.

Packing the Toeplitz product as one full polynomial convolution is material:
the size-32 diagnostic with a packed linear combination of shifted columns
takes 28.3 s, whereas the full-convolution diagnostic takes 5.34 s. These are
unpaired diagnostic observations on their recorded CPUs. The full product
includes the unused high coefficients; checking their bounds is necessary for
balanced-digit injectivity. The checker passes packed block columns to the
moment loop without carrying a duplicate list of packed integers in the
witness. The producer materializes entries through the shared literal layer
before native Berkowitz evaluation.

The certificate currently uses one conservative bound for entries, moment
vectors, coefficient vectors and full products. Separate bounds for these
quantities could reduce the packing width; this is a possible further
optimization, not needed to meet the measured targets. Constructor-form
integer literals and a producer that retains all intermediate coefficient
vectors in one recursion are further candidates for measurement.

## Transported results

The public umbrella also provides:

```lean
theorem equiv_evalMatrix (p : Hex.DensePoly R) (A : Hex.Matrix R n n) :
  matrixEquiv (Hex.Matrix.evalMatrix p A) =
    Polynomial.aeval (matrixEquiv A) (HexPolyMathlib.equiv p)

theorem evalMatrix_charPoly (A : Hex.Matrix R n n) :
  Hex.Matrix.evalMatrix (Hex.Matrix.charPoly A) A = 0

theorem eval_charPoly (A : Hex.Matrix R n n) (t : R) :
  (Hex.Matrix.charPoly A).eval t =
    Hex.Matrix.det (t • Hex.Matrix.identity n - A)

theorem coeff_zero_charPoly (A : Hex.Matrix R n n) :
  (Hex.Matrix.charPoly A).coeff 0 = (-1) ^ n * Hex.Matrix.det A

theorem matrixEquiv_trace (A : Hex.Matrix R n n) :
  Hex.Matrix.trace A = Matrix.trace (matrixEquiv A)

theorem charPoly_transpose (A : Hex.Matrix R n n) :
  Hex.Matrix.charPoly A.transpose = Hex.Matrix.charPoly A

theorem charPoly_conj (A U V : Hex.Matrix R n n)
    (h : U * V = Hex.Matrix.identity n) :
  Hex.Matrix.charPoly (U * A * V) = Hex.Matrix.charPoly A
```

Thus the executable polynomial satisfies Cayley--Hamilton, evaluates as the
determinant of `tI-A`, has the expected determinant and trace coefficients,
and is invariant under transpose and conjugation by an explicitly supplied
inverse.
