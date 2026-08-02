/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexResultantMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexResultant: subresultants and discriminants" =>
%%%
tag := "hex-resultant"
%%%

# Introduction
%%%
tag := "hex-resultant-intro"
%%%

`HexResultant` computes polynomial resultants and discriminants without
constructing a Sylvester matrix. Its Brown subresultant pseudo-remainder
sequence stays in the coefficient ring and uses exact division only at the
points where the recurrence proves divisibility. This matters for the tower
algorithms later in the manual: their coefficient rings are executable
number-field presentations, not Mathlib fields.

The computational library is Mathlib-free. `HexResultantMathlib` states the
correspondence between the final executable value and
{name}`Polynomial.resultant`, including specialization and discriminant
conventions.

Exact division is governed by the algebraic law `ExactDivLaws`, which the
correctness proofs discharge rather than assuming laws for the total `/`
operation. The executable carries no runtime divisibility check; the algorithm
only invokes division at factors whose divisibility the Brown recurrence has
established:

{docstring Hex.ExactDivLaws}

# The executable API
%%%
tag := "hex-resultant-api"
%%%

The public chain records its normalized inputs, every nonzero remainder, and
the terminal principal-subresultant scalar. The scalar is separate because a
defective degree drop can change the exact resultant without changing the last
nonzero polynomial.

{docstring Hex.PRSResult}

{docstring Hex.DensePoly.subresultantChain}

# Certified pseudo-division algebra
%%%
tag := "hex-resultant-pseudo-division"
%%%

The coefficient recurrence is characterized independently of its array
implementation: reconstruction and a remainder smaller than the divisor
determine the quotient/remainder pair uniquely. Nonzero scaling of either
input then follows from that characterization.

{docstring Hex.DensePoly.pseudoDivMod_unique}

{docstring Hex.DensePoly.pseudoDivMod_scale_left}

{docstring Hex.DensePoly.pseudoDivMod_scale_right}

The Mathlib companion transports the same step through the formal-degree
Sylvester determinant. This is the resultant recurrence used by the later
Brown correctness argument; the coefficientwise integrality of Brown's exact
quotients remains its own subresultant theorem.

{docstring Hex.DensePoly.PseudoDivMod.quotient_degree}

{docstring Hex.DensePoly.PseudoDivMod.remainder_degree}

{docstring Hex.DensePoly.PseudoDivMod.resultant_step}

{docstring Hex.DensePoly.PseudoDivMod.resultant_step_degree}

# Integral proof and coefficient embeddings

Brown--Traub exactness is proved directly in the input coefficient ring. The
recursive invariant keeps every leading-coefficient and Brown-scale factor
cross-multiplied, then cancels only factors already proved nonzero. This gives
the scalar and coefficientwise reconstruction equations required by the Brown
recurrence without changing coefficient types.

The Mathlib-free fraction field remains available as general proof
infrastructure. Its embedding is injective, commutes with ordered
pseudo-division, and supports pulling exact quotients back to the coefficient
ring, but the Brown recurrence does not depend on that detour.

{docstring Hex.Fraction.ofCoeff}

{docstring Hex.Fraction.ofCoeff_injective}

{docstring Hex.DensePoly.Fraction.map}

{docstring Hex.Fraction.div_pullback}

{docstring Hex.Fraction.divExp_exact}

{docstring Hex.DensePoly.Fraction.map_pseudoDivMod}

{docstring Hex.DensePoly.Fraction.divScalar_pullback}

{docstring Hex.DensePoly.Fraction.divScalar_exact}

The generalized subresultants are coefficient-indexed scalar determinants
local to `HexResultant`; they do not introduce a dependency on the matrix
libraries. Their explicit-degree core makes preservation under the fraction
embedding type-stable. The Brown--Traub identities identify the later scalar
and polynomial quotients with these mapped subresultants, whose coefficients
then have base-ring image witnesses.

{docstring Hex.DensePoly.Subresultant.coeffMinor}

{docstring Hex.DensePoly.Subresultant.poly}

{docstring Hex.DensePoly.Subresultant.poly_size_le}

The local Laplace determinant supplies column multilinearity, arbitrary
alternation and column updates, and the parity law for adjacent-transposition
sequences without importing `hex-matrix` or `hex-determinant`. In particular,
scaling either input polynomial scales the generalized subresultant by one
scalar for each column in that input's Sylvester block. A consecutive-block
rotation then exchanges those blocks, contributing one sign for every crossed
pair of columns and yielding the generalized-subresultant input-swap law.

The column-operation form of Brown--Traub equation (18) is the next
transformation. Starting from the swapped `G, F` matrix, the specialized unit
upper-triangular update adds multiplier-weighted `G` columns into the later
`F` columns. When `H = F + B * G` and the formal degrees satisfy
`deg F = deg B + deg G`, the coefficient convolution replaces every `F`
column by the matching `H` column. The target is the ordinary generalized
Sylvester matrix for `G, H`, with `F`'s formal degree retained explicitly even
when `H` drops in degree. The determinant is unchanged by these additions, so
the only factor is the block-swap sign.

Collapsing the retained formal degree then exposes one sparse first row per
removed degree. Each expansion contributes `lc(G)`, while the final edge
subresultant is `lc(H)^(deg G - deg H - 1) H`. Together these identities give the full
Brown--Traub factorization, and a nonzero factor can be divided out
coefficientwise by the executable exact-division operation.

{docstring Hex.SubresultantMinor.det_setCol_add}

{docstring Hex.SubresultantMinor.det_swapAdjacent}

{docstring Hex.SubresultantMinor.det_applySwaps}

{docstring Hex.SubresultantMinor.rotateBlocks}

{docstring Hex.SubresultantMinor.det_rotateBlocks}

{docstring Hex.SubresultantMinor.det_eq_zero_of_col_eq}

{docstring Hex.SubresultantMinor.det_addCol}

{docstring Hex.SubresultantMinor.det_scaleRange}

{docstring Hex.SubresultantMinor.det_firstRow}

{docstring Hex.DensePoly.Subresultant.poly_scale_left}

{docstring Hex.DensePoly.Subresultant.poly_scale_right}

{docstring Hex.DensePoly.Subresultant.poly_swap}

{docstring Hex.DensePoly.Subresultant.coeffFold_eq_mul}

{docstring Hex.DensePoly.Subresultant.productCols_addMul}

{docstring Hex.DensePoly.Subresultant.det_addMul}

{docstring Hex.DensePoly.Subresultant.coeffMinorAt_addMul}

{docstring Hex.DensePoly.Subresultant.coeffMinorAt_succRight}

{docstring Hex.DensePoly.Subresultant.coeffMinorAt_raiseRight}

{docstring Hex.DensePoly.Subresultant.coeffMinorAt_rightDegree}

{docstring Hex.DensePoly.Subresultant.coeffMinorAt_brownTraub}

{docstring Hex.DensePoly.Subresultant.poly_rightDegree}

{docstring Hex.DensePoly.Subresultant.poly_brownTraub}

{docstring Hex.DensePoly.Subresultant.poly_brownTraub_rightDegree}

{docstring Hex.DensePoly.Subresultant.divScalar_brownTraub}

The pseudo-remainder specialization covers defective degree drops as well as
regular steps. It identifies the subresultant immediately below the divisor
degree, transports every lower subresultant across the step, and feeds the
cross-multiplied family invariant used by the recursive proof.

{docstring Hex.DensePoly.Subresultant.poly_prem}

{docstring Hex.DensePoly.Subresultant.poly_descent}

{docstring Hex.DensePoly.BrownLaw}

{docstring Hex.DensePoly.subresultantOrdered_brownLaw}

{docstring Hex.DensePoly.Subresultant.Fraction.poly_map}

{docstring Hex.DensePoly.Subresultant.Fraction.exists_coeff}

# Certified chain structure
%%%
tag := "hex-resultant-chain-structure"
%%%

The chain representation comes with structural guarantees, not only
executable checks. Every stored term is nonzero; after the two ordered inputs,
each stored polynomial is strictly smaller than its predecessor; and a
nonzero input pair produces at most `min(deg f, deg g) + 2` terms.

{docstring Hex.DensePoly.subresultantChain_ne_zero}

{docstring Hex.DensePoly.subresultantChain_size_strict}

{docstring Hex.DensePoly.subresultantChain_size_le}

## Fuel control

The implementation bounds its recursion with an explicit fuel parameter.
`subresultantOrdered` selects the public `g.size + 1` budget;
`subresultantOrderedFuel` exposes the same recurrence with an explicit budget
for proof auditing. Adding fuel beyond the public budget leaves the result
unchanged.

{docstring Hex.DensePoly.subresultantOrdered}

{docstring Hex.DensePoly.subresultantOrderedFuel}

{docstring Hex.DensePoly.subresultantOrderedFuel_eq}

Most callers need only the scalar resultant:

{docstring Hex.DensePoly.resultant}

The discriminant uses the standard signed derivative-resultant formula, with
the zero and constant conventions handled explicitly:

{docstring Hex.DensePoly.disc}

# A small exact computation
%%%
tag := "hex-resultant-example"
%%%

For `f = X² - 2` and `g = X - 3`, the resultant is `f(3) = 7`; the
discriminant of `f` is `8`. Both checks below run the Mathlib-free algorithm.

```lean
open Hex

namespace HexResultantChapter

private def f : DensePoly Int := DensePoly.ofList [-2, 0, 1]
private def g : DensePoly Int := DensePoly.ofList [-3, 1]

#guard DensePoly.resultant f g = 7
#guard DensePoly.disc f = 8

end HexResultantChapter
```

# Companion contracts
%%%
tag := "hex-resultant-correspondence"
%%%

These declarations describe the executable results in Mathlib terms. The
central contract identifies the executable scalar with Mathlib's
determinant-defined resultant:

{docstring Hex.DensePoly.toPolynomial_resultant}

The executable discriminant has the same total zero/constant convention as
Mathlib's determinant-defined discriminant:

{docstring Hex.DensePoly.toPolynomial_disc}

For positive-degree polynomials in characteristic zero, discriminants multiply
with the square of the cross-resultant. The degree hypotheses exclude the
nonunit-constant counterexample created by the total constant convention. Over
a characteristic-zero field, nonvanishing is therefore the expected
separability criterion:

{docstring Hex.DensePoly.disc_mul}

{docstring Hex.DensePoly.disc_ne_zero_iff_separable}

The specialization contract retains the original formal degrees, so degree
drops after substituting a parameter do not silently change the resultant
convention:

{docstring Hex.DensePoly.eval_resultant}

Independently, Mathlib's resultant has the following proved root-product
formula. It is the algebraic identity the later executable correspondence will
carry into one-level field norms and Trager collision bounds:

{docstring Hex.DensePoly.resultant_eq_leadingCoeff_mul_prod_roots}

# Cross-references
%%%
tag := "hex-resultant-cross-references"
%%%

* {ref "hex-poly"}[HexPoly] supplies the normalized dense representation;
  `HexResultant` supplies the exact pseudo-division and Brown recurrence.
* {ref "hex-number-field"}[HexNumberField] uses bivariate specialization
  vanishing to justify factorization-lazy arithmetic.
* {ref "hex-number-field-tower"}[HexNumberFieldTower] uses the full value and
  root-product correspondence for relative norms and Trager recovery.
