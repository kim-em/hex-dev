# hex-poly-smith (Smith normal form over `F[x]`, depends on hex-poly, hex-matrix, hex-determinant)

The Smith normal form of a matrix of polynomials over a field: a
diagonal matrix `S` with `S = U * A * V` for `U` and `V` unimodular over
`F[x]`, whose diagonal entries are monic and form a divisibility chain
`d₁ ∣ d₂ ∣ ⋯ ∣ d_r`. Those entries are the invariant factors of `A`, and
they determine the structure of the `F[x]`-module presented by `A`.
Mathlib-free. The companion `hex-poly-smith-mathlib` builds Mathlib's
`Module.Basis.SmithNormalForm` over `Polynomial F` from the executable
output and relates the invariant factors to the structure theorem for
finitely generated modules over a principal ideal domain.

The matrix type is `Matrix (DensePoly F) n m`. No new matrix
representation is needed, and none is introduced.

This library is the reusable half of the polynomial normal-form work.
The application to a characteristic matrix `xI - A`, and everything that
follows from it, is `hex-invariant-factors` in
[future-work](../future-work.md) and is deliberately absent here. See
"What is deliberately not here".

## Read the integer pair first, and then discount most of it

[hex-smith](hex-smith.md) and [hex-hermite](hex-hermite.md) are the two
integer normal-form SPECs. They are worth reading first because they fix
the vocabulary this SPEC reuses (the data-plus-inverse contract, the
determinantal-divisor argument, the certificate shape, the
"matrix-update counts rather than complexity" convention). They are also
where the temptation to share code comes from, and most of that
temptation should be resisted.

[hex-hermite](hex-hermite.md) already predicted the split, under "Why
`Int` and not a Euclidean domain class", and it predicted it correctly.
Now that the `F[x]` consumer is being specified rather than
hypothesised, the inventory can be made exact:

| piece | over `ℤ` | over `F[x]` | transfers? |
|---|---|---|---|
| unit group | `{1, -1}` | `F \ {0}` | no: "unimodular" is `det ∈ F^×`, not `det = ±1` |
| pivot normalisation | positive | monic | no: `extGcd` returns a nonnegative `g` for free, `xgcd` returns an arbitrary associate |
| 2x2 elimination shape | `[[s, t], [-b/g, a/g]]` | same shape, scaled by `1/lc g` | partly: the shape transfers, the matrix does not |
| explicit inverse of the step | direct computation | direct computation | yes, as a technique; the entries differ |
| exact division | the generic `Hex.exactDiv`, plus an `@[extern]` `Int` fast path in `hex-bareiss` | the same generic `Hex.exactDiv`, no fast path | partly: the wrapper transfers, the machine-division fast path has no analogue |
| termination measure | `(\|pivot\|, c)` lexicographic | `(deg pivot, c)` lexicographic | yes, as a shape; the first component is computed differently |
| repetition bound `P` | bit length of the pivot entering the stage | degree of the pivot entering the stage | yes, as a shape |
| reduction of entries above a pivot | `%` into `[0, p)` | not needed | no: Smith form clears off-diagonal entries to zero, and the residue range is a Hermite-form concern |
| growth problem | coefficient size | degree, and coefficient size again when `F = ℚ` | no: two problems where `ℤ` has one |
| determinantal divisors | gcd of `k × k` minors, in `Nat` | monic gcd of `k × k` minors, in `DensePoly F` | yes, and it needs the same missing Cauchy-Binet work |
| `mul_eq_one_comm` | adjugate over a commutative ring | the same theorem, same instance | yes, verbatim |
| `mulEqCert` product check | Kronecker digit packing on `Int` | inapplicable | no: see "Certificates" |
| dependency on a Hermite library | real (`extGcd`, exact division, certificates, conventions) | none | no: see below |
| oracle | FLINT `fmpz_mat_snf` | neither FLINT nor the existing driver | no: a new oracle and a new fixture kind |

Two entries in that table deserve more than a row.

**There is no polynomial Hermite normal form underneath this library.**
[hex-smith](hex-smith.md) sits on [hex-hermite](hex-hermite.md) because
the integer elimination step, the exact-division discipline, and the
certificate machinery all live there. Over `F[x]` the corresponding
pieces come from [hex-poly](../../HexPoly/SPEC/hex-poly.md) (`xgcd`,
`divMod`, `leadingCoeff`, `Monic`) and from
[hex-matrix](https://github.com/leanprover/hex-matrix/blob/main/SPEC/hex-matrix.md)
directly, so there is nothing to inherit. The polynomial analogue of
Hermite normal form is a real subject (row-reduced forms, Popov forms,
shifted forms, minimal approximant bases), but it is a *different*
subject with its own canonicity conditions and its own consumers, and
this library neither needs it nor anticipates it. A future
`hex-popov` would sit beside this library, not below it.

**The class generalisation is still not worth writing.** With both sides
of the comparison now specified, the shared surface is one function
shape, and even that function differs: the polynomial step folds the
monic normalisation into the same matrix (see "The elimination step"),
while the integer step gets its normalisation from `extGcd`'s return
type. A Euclidean-domain class carrying `xgcd`, exact division, and a
normalisation would let one *loop skeleton* be written once, at the cost
of an indirection on the innermost path of both libraries, and would
share no *library* theorem: the uniqueness argument is the same argument,
but its statement mentions `Nat` on one side and `DensePoly F` on the
other. What the two libraries do share is `mul_eq_one_comm`, and that
already lives in `hex-determinant` over an arbitrary commutative ring,
which is the point: the genuinely shared content is downstream of both
and needs no class to be shared. The question is now closed rather than
deferred.

## Why this library exists

The integer SPEC has to argue its own marginal value, because
[hex-hermite](hex-hermite.md) already decides lattice membership,
produces one solution of `vecMul x A = b`, gives the integer kernel, and
computes the index, so [hex-smith](hex-smith.md) lists only what those
do not cover. There is no such baseline over `F[x]`: nothing in the tree
can answer any question about a module over `F[x]` today, so every item
below is new capability rather than an increment.

- **The structure of a finitely generated `F[x]`-module.** Given
  relations as the rows of `A : Matrix (DensePoly F) n m`, the module
  `F[x]^m / rowmodule A` is
  `F[x]^(m - r) ⊕ F[x]/(d₁) ⊕ ⋯ ⊕ F[x]/(d_r)`, read off the diagonal
  with the unit `dᵢ = 1` summands dropped. This is the headline
  consumer, and it is the reason the divisibility chain matters: without
  it the diagonal is not canonical and the summands are not the
  invariant factors.
- **Polynomial linear systems.** `A x = b` over `F[x]` becomes a
  diagonal system after the change of basis, so solvability is a
  divisibility test per coordinate, and the solution set is a coset of
  the kernel module.
- **Rank over `F(x)`**, computed without constructing rational
  functions.
- **The order ideal of the torsion part**, generated by `∏ dᵢ` when
  `r = m`, which for square input is the monic associate of `det A`.
- **Canonical forms of a linear operator**, through
  `hex-invariant-factors`. That library is not this one. It supplies
  `xI - A`, calls `snf`, and reads the diagonal; every theorem it needs
  about `snf` is stated here.

The dependency list is short and each entry is used for a specific
thing. `hex-poly` supplies `DensePoly F`, `xgcd`, `divMod`,
`leadingCoeff`, and `Monic`. `hex-matrix` supplies `Matrix`, the
elementary row and column operations, and matrix multiplication.
`hex-determinant` supplies `det`, `mul_eq_one_comm` (which is what makes
the one-sided inverse fields below sufficient), and, once the
prerequisite work below lands, Cauchy-Binet for selected minors.

## What Smith normal form over `F[x]` is

`A : Matrix (DensePoly F) n m` with `F` a field. A **Smith normal
form** of `A` is a triple `(U, S, V)` with `U : Matrix (DensePoly F) n n`
and `V : Matrix (DensePoly F) m m` unimodular over `F[x]` and
`S = U * A * V` satisfying:

1. `S[i][j] = 0` whenever `i ≠ j`.
2. `S[i][i] = dᵢ` monic for `i < r`, and `S[i][i] = 0` for `i ≥ r`.
3. `dᵢ ∣ dᵢ₊₁` for `i + 1 < r`.

Unimodular over `F[x]` means invertible over `F[x]`, equivalently that
`det U` is a **nonzero constant**. This is the first thing that differs
from the integer case and the first thing a port gets wrong: over `ℤ`
the units are `{1, -1}` and unimodularity is `det = ±1`, so a checker
can compare a determinant against two values. Over `F[x]` the unit group
is `F^×`, which is infinite for every field of characteristic zero, so
the condition is a degree condition and not an equality. In the
normalised `DensePoly` representation it is exactly `(det U).size = 1`.

`S` is unique. `U` and `V` are not, and no uniqueness theorem for them is
stated, for the same reason as in [hex-smith](hex-smith.md).

Uniqueness of `S` comes from the **`k`-th determinantal divisor**
`D_k(A)`, the monic gcd of all `k × k` minors of `A`, with `D_0 = 1` and
`D_k = 0` when every such minor vanishes. Every `k × k` minor of `U * A`
is an `F[x]`-combination of the `k × k` minors of `A` (Cauchy-Binet in
its general rectangular form), so `D_k` is unchanged by multiplying by a
unimodular matrix on either side. For a diagonal matrix with a
divisibility chain of monic entries, `D_k = d₁ ⋯ d_k` for `k ≤ r`, and
`D_k = 0` for `k > r`. Hence `r` is the largest `k` with `D_k ≠ 0`, and
`d_k = D_k(A) / D_{k-1}(A)`, both determined by `A` alone.

The `k > r` case has to be stated for the same reason as over `ℤ`:
without it the rank half of uniqueness is not provable. See
`IsSNF.detDivisor_eq` under "Correctness theorems".

The one genuine addition over the integer statement is **monic**. Over
`ℤ` the gcd of a family of integers has a canonical representative for
free, because `Nat` is the codomain of `Int.gcd`. Over `F[x]` a gcd is
determined only up to `F^×`, so "the" determinantal divisor is a
definition and not an observation: it is the monic generator of the
ideal the minors generate, and `0` when that ideal is `0`. Everything
canonical in this library is canonical because of that choice, which is
why the monic normalisation appears in the contract, in the elimination
step, and in the specification function, rather than being applied once
at the end.

## Coefficient hypotheses

The executable path and the proofs use the same bundle:

```lean
variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
```

`Lean.Grind.Field` supplies `Zero`, `One`, `Add`, `Sub`, `Mul`, `Div`,
and `Inv`, which is everything `DensePoly`'s Euclidean operations
require, plus `zero_ne_one` and `mul_inv_cancel`, which is everything
their correctness needs. This follows `hex-row-reduce`, whose
`rowReduce`, `spanCoeffs`, and `nullspace` all carry
`[Lean.Grind.Field R] [DecidableEq R]`, and it is deliberately not
weaker: a version parameterised only on the raw operations would be
executable at unlawful instances and would have to carry the law
packages as explicit hypotheses everywhere.

**This bundle does not yet imply the law packages, and that is a
prerequisite rather than an oversight.** `Hex.DensePoly.DivModLaws F`
and `Hex.DensePoly.GcdLaws F` are the classes that make `divMod`,
`gcd`, and `xgcd` correct rather than merely defined. The instances that
exist today are `instDivModLawsZMod64Fp` and `instGcdLawsZMod64Fp` in
`HexPolyFp/Field.lean`, `instDivModLawsRat` and `ratGcdLaws` in
`HexPolyZ/Rational.lean`, and `instDivModLawsField` and
`instGcdLawsField` in `HexPolyMathlib/Euclid.lean`, the last of which is
stated for Mathlib's `Field` and so is unavailable to a Mathlib-free
library. Against the current tree,

```lean
example {F : Type u} [Lean.Grind.Field F] [DecidableEq F] :
    Hex.DensePoly.DivModLaws F := inferInstance
```

fails. See "Prerequisite changes in other libraries".

**Named coefficient fields.** `ZMod64 p` for a prime modulus and `Rat`
are the two coefficient types carrying the law packages in the
Mathlib-free tree, and the conformance and bench suites use both.
`ZMod64 p` is the case where only degrees grow; `Rat` is the case where
coefficients grow as well, and it is included precisely because it is
the harder one. `hex-gf2` carries `Lean.Grind.Field (GF2nPoly f hirr)`
as `fieldOfDegreePos`, a `def` rather than a registered instance and
without the law packages, so an extension-field coefficient type is
reachable but not wired up. Nothing here depends on it.

**Small fields are a real case, not an edge case.** `ZMod64 2` has one
nonzero element. Nothing in the algorithm cares, but the
evaluation-based product check under "Certificates" needs `D + 1`
distinct points of `F` for a degree bound `D`, and therefore does care,
so its hypothesis is stated in the signature rather than assumed away.

## Degenerate dimensions and degenerate input

Each of these is a case an implementation gets wrong silently, so each
gets a conformance fixture.

- **`n = 0` or `m = 0`.** The rank is `0`, `diag` is the empty vector,
  and both transforms are identities of their (possibly zero) size.
  `IsSNF` holds. Nothing may index into `diag`.
- **`A = 0`.** Rank `0`, both transforms the identity, `diag` empty. The
  pivot loop must stop on the first test rather than searching for a
  pivot that is not there.
- **`1 × 1`.** `snf ⟨#v[p]⟩` is `⟨#v[monicize p]⟩` with `snfRank` equal
  to `1` when `p ≠ 0`, and `⟨#v[0]⟩` with rank `0` otherwise. This is the smallest case that
  distinguishes monic normalisation from no normalisation.
- **Unit entries.** An entry that is a nonzero constant is a unit of
  `F[x]`, so it becomes a pivot of `1` and clears its whole row and
  column in one pass. `invariantFactors` reports those leading `1`s;
  `moduleStructure` drops them.
- **Rank deficiency, in either orientation.** `rank < min n m` is
  ordinary, and the trailing diagonal positions are `0`. Rectangular
  input in both orientations is ordinary.
- **A diagonal input containing zeros or non-monic entries.** This is the
  input to `snfDiagonal` and `snfDiagonalData`, and the place their
  normalisation phase is not
  skippable: `#v[0, x]` is diagonal and is not in Smith normal form, and
  `#v[0, 0]` has no gcd to divide by. See "A fast path for diagonal
  input".
- **Coefficient-field degeneracy.** None. `Lean.Grind.Field` carries
  `zero_ne_one`, so the trivial ring is excluded by the hypothesis and no
  clause is needed for it.

## Data and contract

```lean
namespace Hex.PolyMatrix

/-- Executable Smith normal form data over `F[x]`: the rank, the
invariant factors, and both change-of-basis matrices with their
inverses. -/
structure SmithData (F : Type u) [Zero F] [DecidableEq F] (n m : Nat) where
  rank : Nat
  diag : Vector (DensePoly F) rank
  left : Matrix (DensePoly F) n n
  leftInv : Matrix (DensePoly F) n n
  right : Matrix (DensePoly F) m m
  rightInv : Matrix (DensePoly F) m m

/-- Smith normal form contract over `F[x]`. -/
structure IsSNF (A : Matrix (DensePoly F) n m) (S : SmithData F n m) : Prop where
  left_inv : S.left * S.leftInv = Matrix.identity n
  right_inv : S.right * S.rightInv = Matrix.identity m
  mul_eq : S.left * A * S.right = diagMatrix S.diag n m
  rank_le_n : S.rank ≤ n
  rank_le_m : S.rank ≤ m
  diag_monic : ∀ i : Fin S.rank, S.diag[i].Monic
  chain : ∀ (i : Nat) (h : i + 1 < S.rank), S.diag[i]'(by omega) ∣ S.diag[i + 1]

end Hex.PolyMatrix
```

This elaborates as written against the current tree, on
`HexPoly`, `HexMatrix`, and `HexDeterminant` alone.

**`Hex.PolyMatrix`, not `Hex.Matrix`.** [hex-smith](hex-smith.md) puts
`snf`, `invariantFactors`, and `SmithData` in `Hex.Matrix`. Reusing that
namespace here would produce two declarations named `Hex.Matrix.snf`,
which is an error in any file that imports both libraries, and importing
both is exactly what an application computing integer and polynomial
invariant factors would do. The names stay short and the qualifier goes
in the namespace, per the project naming rule.

**`diag_monic` replaces `diag_pos`.** It is the same clause doing the
same job (pinning down the associate class), and it is the only field
whose *statement* differs from the integer contract.

**One-sided inverse fields.** `left_inv` and `right_inv` record only
`U * W = I` and `V * X = I`. The other direction follows over a
commutative ring through the adjugate, by
`Hex.Matrix.mul_eq_one_comm` in `HexDeterminant/Adjugate.lean`. That
theorem is stated for `[Lean.Grind.CommRing R]` and applies to
`R = DensePoly F` unchanged, so this is one of the few places where the
integer design transfers with nothing to re-derive.

**The inverses are data, not existence.** Every elementary step has an
explicit inverse (see "The elimination step"), so accumulating `W` and
`X` alongside `U` and `V` costs one extra update per step and removes
any need to invert a polynomial matrix afterwards. Inverting one would
mean an adjugate over `F[x]`, whose entries have degree up to `(n-1)·D`,
so this is a larger saving than it is over `ℤ`.

**Unimodularity is a theorem, not a field**, exactly as in
[hex-hermite](hex-hermite.md):

```lean
theorem IsSNF.left_unit (h : IsSNF A S) : (Matrix.det S.left).size = 1
theorem IsSNF.right_unit (h : IsSNF A S) :
    ∃ c : F, c ≠ 0 ∧ Matrix.det S.right = DensePoly.C c
```

Both forms are stated: the `size = 1` form is what the decidable shape
test checks, and the `C c` form is what a proof wants to rewrite with.
For a normalised `DensePoly`, `size = 1` says exactly "nonzero
constant".

**`diagMatrix` belongs in `hex-matrix`.**

```lean
/-- The `n × m` matrix carrying `d` down the leading diagonal. -/
def diagMatrix {R : Type u} [Zero R] {r : Nat} (d : Vector R r) (n m : Nat) :
    Matrix R n m :=
  Matrix.ofFn fun i j => if h : i.val = j.val ∧ i.val < r then d[i.val]'h.2 else 0
```

[hex-smith](hex-smith.md) already requires the move, and displays the
signature specialised to `Int` as its prerequisite API. This library adds
one constraint to that request: the `hex-matrix` version must be
**generic in `R` with `[Zero R]`**, as displayed above. An `Int`-only
constructor in `HexMatrix/Diagonal.lean` would leave this library
defining a second copy at `DensePoly F`, which is precisely the
duplication the relocation exists to prevent, and it would be discovered
only when the second consumer arrives.

Neither version is in the tree yet: `HexMatrix/Diagonal.lean` does not
exist, and `Hex.Matrix.diagonal` and `Hex.Matrix.diagMatrix` are both
unknown constants against the current tree. So nothing has to be
reconciled, only added, and it should be added once at the general
signature.

## The elimination step

This is the piece that carries the monic normalisation, and it is where
the integer and polynomial libraries stop being the same code.

Two entries `a` and `b` in the same column, with
`⟨g, s, t⟩ := Hex.DensePoly.xgcd a b`, so that `s * a + t * b = g` and
`g` generates the same ideal as `a` and `b`. Write `u := 1 / lc g` for
the inverse of the leading coefficient of `g`, and `ĝ := u · g` for the
monic associate. The 2x2 matrix

```
E = ⎡    u·s        u·t   ⎤          E⁻¹ = ⎡ a/ĝ   -t ⎤
    ⎣ -u·(b/ĝ)   u·(a/ĝ)  ⎦                ⎣ b/ĝ    s ⎦
```

applied to the two rows replaces `(a, b)` by `(ĝ, 0)`. It is invoked
only when `a ∤ b` and `b ∤ a`; the divisible cases are handled by a plain
subtraction, for the termination reason under "Algorithms". Every
division in
both matrices is an exact division **by the monic `ĝ`**, so every one of
them can go through `divModMonic` and none of them needs a coefficient
division. `det E = u²·(s·a + t·b)/ĝ = u²·g/ĝ = u`, a nonzero constant, so
`E` is unimodular, and the displayed `E⁻¹` is its inverse by direct
computation: the `(0,0)` entry of `E * E⁻¹` is
`u·(s·a + t·b)/ĝ = u·g/ĝ = 1`, the `(1,1)` entry is
`u·(t·b + s·a)/ĝ = 1`, and the two off-diagonal entries cancel termwise.

Writing the bottom row as `[-b/g, a/g]` instead, with the raw `g`, gives
the same matrix, because `a/g = u·(a/ĝ)`. The `ĝ` form is the one to
implement: it is the same arithmetic with the coefficient division
hoisted into `u`, and it keeps every polynomial division monic.

Every one of these identities is checked numerically over `Rat` on
thirteen inputs (generic, coprime, non-monic leading coefficients,
`a = 0`, `b = 0`, both zero, `a = b`, either side a unit, each side
dividing the other, and `(x, 2x)` in both orders), and the checks are
worth keeping as `#guard`s in the implementation, because a unit
misplaced here produces a matrix that is correct on every input where
`g` happens to be monic.

Three things about this are worth stating, because a port of the
integer step gets each of them wrong.

**The normalisation is inside the step, not after it.**
`Hex.DensePoly.xgcd` returns the last nonzero remainder of the Euclidean
sequence, whose leading coefficient is whatever the arithmetic
produced. It is not monic, it is not monic even when both inputs are,
and without normalisation it is not even independent of the argument
order. Against the current tree, over `Rat`:

```
Hex.DensePoly.gcd (2x² + 2x) (3x + 3)  =  3x + 3
Hex.DensePoly.gcd (x² - 1)   (x² + x)  =  -x - 1
Hex.DensePoly.gcd (x² + x)   (x² - 1)  =  x + 1
```

`HexArith.Int.extGcd` returns `g : Nat`, so the integer library gets its
normalisation from a return type and its `E` needs no `u`. Folding `u`
into `E` rather than applying a separate scaling afterwards costs two
scalar multiplications of the Bezout coefficients and keeps the number
of accumulated transform updates per step at one, which is what a
separate normalising row operation would double.

**The two sides carry different powers of `u`.** `E` has a `u` on every
entry and `E⁻¹` has none. Dropping the `u` from the bottom row of `E`, or
adding one to `E⁻¹`, leaves a pair that is off by a unit in one entry,
and that error is invisible on any input where `g` happens to be monic.
Every fixture in the conformance list whose gcd is non-monic exists to
catch it.

**The all-zero case is a separate branch.** When `a = b = 0` the gcd is
`0`, `lc g = 0`, `u = 1/0 = 0` by the junk-value convention of
`Lean.Grind.Field.inv_zero`, and `E` is the zero matrix, which is not
unimodular. The step returns `(identity, identity, 0)` on that branch.
That keeps it total with a *correct* value rather than a fallback:
`identity * (0, 0) = (0, 0) = (ĝ, 0)`, so the step's specification holds
on the branch and no classification under design principle 8 is
required. The remaining degenerate cases need no branch: `xgcd a 0`
returns `⟨a, 1, 0⟩` and `xgcd 0 b` returns `⟨b, 0, 1⟩`, so the displayed
matrices specialise to a scaling and to a swap-and-scale respectively,
and a unit input just makes `ĝ = 1`.

**Exact division needs no new primitive, and the shared one already
applies.** `Hex.exactDiv` and its `ExactDivLaws` class live in
`hex-basic` (`HexBasic/ExactDiv.lean`), generic over any
`[Zero R] [DecidableEq R] [Div R]` with `exactDiv a 0 = 0` as a
documented junk branch, and `hex-resultant` supplies
`instExactDivLawsDensePoly`. So the four divisions in `E` go through the
same wrapper the integer libraries use, at `R = DensePoly F`, and this
SPEC asks for no polynomial-specific division primitive.

What it does ask for is that `instExactDivLawsDensePoly` travel with the
commutative-ring tower when that moves down into `hex-poly`, for the
reason under "Prerequisite changes in other libraries": otherwise the
generic wrapper is available and the instance that makes it meaningful
here is not.

There is also nothing faster to reach for. The quotient component of
`divMod` *is* the exact quotient when the divisor divides the dividend,
and long division by a monic divisor is already the cheapest route
(`divModMonic`, which skips the coefficient division at every step),
which is why the `ĝ` form of `E` above is the one to implement. What has
no counterpart is the `@[extern "lean_int_div_exact"]` binding in
`HexBareiss/Bareiss.lean`, which is where the integer libraries get
their exact-division speed: that saving is one machine division
instruction, and there is no such thing for a polynomial, so an
implementer looking for the analogue should stop looking.

## Algorithms

**The default is the classical Euclidean pivot algorithm.** As over `ℤ`,
it has a straightforward correctness argument and a termination measure,
and no proven bound on the size of intermediate entries. The
instrumentation under "Benchmarking" is therefore the only evidence
about growth that this algorithm comes with.

The pivot loop:

1. If the remaining block is zero, stop with the current rank.
2. Move a nonzero entry of **minimal degree** to the pivot position by
   one row swap and one column swap.
3. Normalise the pivot to monic, by scaling its row by `1 / lc p`.
4. Clear the pivot's column with row operations and its row with column
   operations, **branching on divisibility at each entry**. For an entry
   `b` in the pivot's column, with monic pivot `p`:
   - if `p ∣ b`, subtract `(b/p)` times the pivot row from `b`'s row.
     This zeroes `b`, leaves the pivot row untouched, and is one exact
     division by a monic divisor;
   - otherwise apply the `E` above to the two rows, which replaces the
     pivot by the monic gcd of `p` and `b`, a strict divisor of `p`.

   The column case is the transpose of this with column operations.
5. If some entry `a[i][j]` of the remaining block is not divisible by the
   pivot `p`, add row `i` to the pivot row **and immediately run the
   column-`j` elimination against the new entry**, which replaces `p` by
   the monic gcd of `p` and `a[i][j]`, then return to step 4. This is the
   step that produces the divisibility chain, and it is the step a naive
   implementation omits.
6. Otherwise advance to the next diagonal position.

**The branch in step 4 is not an optimisation, it is what makes the loop
terminate.** Using `E` on a divisible entry is correct but destroys the
measure, and the failure is not exotic. Take pivot `p = x` and entry
`b = 2x` over `ℚ`. Then `xgcd x (2x)` returns `⟨2x, 0, 1⟩` (this is what
the current implementation returns, not a hypothetical), so `s = 0` and
the new pivot row is `u` times the *other* row. The pivot degree is
unchanged at `1`, and every nonzero entry of row `i` has just been
copied into the pivot row, so the count of nonzero off-pivot entries
goes up. The measure increases. `xgcd p p` does the same thing. The
plain-subtraction branch avoids this by not touching the pivot row at
all.

The pivot is monic from step 3 onwards, so every division in step 4,
in both branches, is by a monic divisor, and the divisibility test is
`Hex.DensePoly.mod` against a monic divisor. Whether to thread the
monicity *proof* through the loop so that `divModMonic` can be called
directly, rather than relying on `divMod` to divide by a leading
coefficient that happens to be `1`, is a measured decision and is
written down as such under "Benchmarking".

**Termination measure.** The pair `(deg pivot, c)` ordered
lexicographically, where `deg pivot` is `p.degree?.getD 0` for the
current nonzero pivot `p` and `c` is the number of nonzero entries in the
pivot row and column other than the pivot itself. The divisible branch of
step 4 leaves `deg pivot` fixed and decreases `c` by one; the `E` branch
strictly decreases `deg pivot`. Both components are naturals, so the loop
is well-founded.

The strict decrease is the one place the polynomial argument is *simpler*
than the integer one. If `p ∤ b` then `gcd(p, b)` is a proper divisor of
`p`, and a proper divisor of a polynomial has strictly smaller degree,
because an associate has equal degree and divisibility with equal degree
forces associates. Over `ℤ` the corresponding step compares absolute
values and needs the same argument phrased through positivity. No clause
in this library does case analysis on a sign, which is a category of
error the integer library has to handle and this one does not.

Step 5 is stated as one fused step for exactly the reason
[hex-smith](hex-smith.md) gives: adding row `i` to the pivot row on its
own leaves `deg pivot` fixed and raises `c` from `0`, so the measure
*increases*, and Lean needs the recursive call itself to decrease.
Fusing the column elimination into the same step makes the recursion
happen only after the pivot has become `gcd(p, a[i][j])`, whose degree is
strictly smaller because `p ∤ a[i][j]`. Note that the fused elimination
takes the `E` branch of step 4 by construction, since the entry it runs
against is not divisible by the pivot.

Whether the measure is threaded as a `termination_by` clause or as
explicit fuel with a sufficiency theorem is an implementation decision,
but it must be one of the two, and `hex-lll`'s `lllFuel` is the
precedent for the fuel form: the fuel-exhausted branch returns a value
that a sufficiency theorem proves unreachable on public API inputs, and
that classification is written down. Design principle 8 allows nothing
weaker. Note that `Hex.DensePoly.xgcd` is itself already fuel-driven
(`p.size + q.size + 1`), so an implementation choosing the fuel form is
consistent with the library underneath it rather than introducing the
idiom.

**A fast path for diagonal input.** A diagonal matrix is already almost
in Smith normal form and needs only normalisation and the chain. The
normalisation is not skippable, because the input diagonal may contain
zeros and non-monic entries. It has two phases:

- **Monicize each nonzero entry.** Scaling column `i` by `1 / lc dᵢ`
  makes `dᵢ` monic. This is a right-hand operation: it updates `right`
  and `rightInv` (the latter by the reciprocal scale) and leaves `left`
  and `leftInv` alone. Doing it on the row instead is equally valid and
  updates the other two; what is not valid is updating all four, which
  would compose the unit in twice.
- **Move the nonzero entries stably before the zeros.** On a diagonal
  matrix, exchanging positions `i` and `j` is a *paired* row and column
  transposition: the row swap alone moves the entry off the diagonal. So
  each move updates all four transforms, one swap on each side.

The rank is then the number of nonzero entries, and the sweep runs on
the monic prefix alone, which is what makes the divisions below defined:
`#v[0, 0]` has no `ĝ` to divide by, and `#v[0, x]` is not in Smith normal
form despite being diagonal.

For two adjacent normalised entries `a, b` monic, with
`⟨g, s, t⟩ := xgcd a b`, `u := 1 / lc g`, `ĝ := u · g`, and `l := a·b/ĝ`,
the pair

```
L₁ = ⎡ 1  1 ⎤   L₂ = ⎡     1      0 ⎤   V = ⎡ u·s   -b/ĝ ⎤
     ⎣ 0  1 ⎦        ⎣ -u·t·b/ĝ   1 ⎦       ⎣ u·t    a/ĝ ⎦
```

sends `diag(a, b)` to `diag(ĝ, l)` as `L₂ · L₁ · diag(a, b) · V`: adding
the second row to the first gives `[[a, b], [0, b]]`, right-multiplying
by `V` (whose determinant is `u·(s·a + t·b)/ĝ = 1`) gives
`[[ĝ, 0], [u·t·b, l]]`, and `L₂` clears the `u·t·b` entry, which is
divisible by `ĝ` because `ĝ` divides `b`. Both `ĝ` and `l` are monic,
because `a` and `b` are.

The inverses are needed as data, so they are displayed too:

```
L₁⁻¹ = ⎡ 1  -1 ⎤   L₂⁻¹ = ⎡    1      0 ⎤   V⁻¹ = ⎡  a/ĝ   b/ĝ ⎤
       ⎣ 0   1 ⎦          ⎣ u·t·b/ĝ   1 ⎦         ⎣ -u·t   u·s ⎦
```

`V⁻¹` is the adjugate of `V`, which is `V`'s inverse outright because
`det V = 1`. All four displayed matrices and the product identity are
checked numerically over `Rat`, as the elimination step is.

**The sweep is a fixed network, not a loop to a fixed point.** "Repeat
adjacent-pair passes until nothing changes" bounds nothing by itself.
Run instead the `r(r-1)/2` comparison schedule of a bubble sort: `r-1`
passes, pass `k` visiting positions `0 … r-2-k`, each position applying
the pair above. The reason a fixed schedule is enough is that
`(a, b) ↦ (gcd a b, lcm a b)` is the comparator of the divisibility
lattice on monic polynomials, which is distributive, and a comparator
network that sorts every `0`/`1` sequence sorts over any distributive
lattice. Bubble sort's network does, so this one produces the
divisibility chain, in exactly `r(r-1)/2` `xgcd` calls with no
convergence argument to make. This
is the polynomial form of FLINT's `snf_diagonal`, and it is the path a
direct-sum presentation of a module takes, which is the common case for
the headline consumer.

**Not specified: a modular variant.** [hex-smith](hex-smith.md) carries
`snfSquareDiag`, the Iliopoulos algorithm run modulo a multiple of the
largest invariant factor. The polynomial analogue exists (work in
`F[x]/(d)` for a suitable monic `d`) and the reason it is out of scope
here is not that it fails to transfer but that it answers a smaller
question: it computes the diagonal without the transforms, and
recovering them is a separate algorithm. [hex-smith](hex-smith.md) keeps
its version only subject to a measured decision rule, and starting a
second unmeasured one here would be premature. It is listed under "Open
questions".

**Not specified: asymptotically fast methods.** Storjohann's algorithms
for polynomial matrices, and the randomized approaches of
Kaltofen-Krishnamoorthy-Saunders, are out of scope, and the comparator
classification under "Benchmarking" says so rather than pretending a
ratio against a library that uses them measures the same algorithm.

## API

```lean
namespace Hex.PolyMatrix

/-- The Smith normal form of `A`. Does not compute the transforms. -/
def snf (A : Matrix (DensePoly F) n m) : Matrix (DensePoly F) n m

/-- The number of nonzero diagonal entries of `snf A`, that is the rank
of `A` over `F(x)`. Computed without building the transforms. -/
def snfRank (A : Matrix (DensePoly F) n m) : Nat

/-- Smith normal form data for `A`: the form, both transforms, and both
inverses. -/
def snfData (A : Matrix (DensePoly F) n m) : SmithData F n m

/-- The invariant factors of `A`, monic and in a divisibility chain. -/
def invariantFactors (A : Matrix (DensePoly F) n m) :
    Vector (DensePoly F) (snfRank A)

/-- Smith normal form of a diagonal matrix, given its diagonal. -/
def snfDiagonal {r : Nat} (d : Vector (DensePoly F) r) : Matrix (DensePoly F) r r

/-- Smith normal form of a diagonal matrix, with the transforms. -/
def snfDiagonalData {r : Nat} (d : Vector (DensePoly F) r) : SmithData F r r

/-- The structure of `F[x]^m / rowmodule A`: the free rank, and the
torsion invariants in a divisibility chain with the units dropped. -/
def moduleStructure (A : Matrix (DensePoly F) n m) : Nat × Array (DensePoly F)

/-- The monic generator of the order ideal (the zeroth Fitting ideal) of
`F[x]^m / rowmodule A`, and `0` when that ideal is `0`, which is exactly
when the quotient has a free summand. -/
def quotientOrder (A : Matrix (DensePoly F) n m) : DensePoly F

/-- A polynomial solution of `vecMul x A = b`, or `none` when there is
none. -/
def solve (A : Matrix (DensePoly F) n m) (b : Vector (DensePoly F) m) :
    Option (Vector (DensePoly F) n)

/-- The `k`-th determinantal divisor: the monic gcd of the determinants
of all `k × k` submatrices of `A`, taken over every choice of `k` rows
and `k` columns. `detDivisor A 0 = 1`, and `detDivisor A k = 0` when
`k > min n m` or when every such minor vanishes.

This is the specification function. Its definition is the gcd above and
mentions nothing about `snf`. `IsSNF.detDivisor_eq` is what says the
invariant factors compute it. -/
noncomputable def detDivisor (A : Matrix (DensePoly F) n m) (k : Nat) : DensePoly F

/-- The determinants of all `k × k` submatrices of `A`, over every
choice of `k` rows and `k` columns, in the canonical enumeration order.
The domain of the gcd that `detDivisor` takes, and the only reason it is
exported is that `detDivisor_spec` mentions it. -/
noncomputable def minors (A : Matrix (DensePoly F) n m) (k : Nat) : List (DensePoly F)

end Hex.PolyMatrix
```

Contracts to state explicitly, because an implementer would otherwise
choose differently.

**The transforms are a separate entry point, as in
[hex-hermite](hex-hermite.md) and [hex-smith](hex-smith.md).** `snf`,
`snfRank`, `invariantFactors`, `snfDiagonal`, `moduleStructure`, and
`quotientOrder` accumulate none of the four transform matrices; only
`snfData`, `snfDiagonalData`, and `solve` do. This is not a stylistic
alignment with the sibling libraries: this SPEC says under "Complexity"
and "The inverses are data" that the polynomial transforms are the
expensive part and that their degrees are the unbounded quantity, and it
would be incoherent to say that and then make every consumer pay for
them. `solve` is the only named consumer that genuinely needs them, since
it maps the right-hand side through `V` and the answer back through `U`.
`hex-invariant-factors` reads the diagonal and wants `snf`; it needs
`snfData` only if it goes on to build the basis realising a canonical
form, which is its decision and not this library's.

Both paths run the same loop, parameterised by whether the accumulators
are updated, so there is one algorithm and not two.

`invariantFactors` drops nothing, so its leading entries may be `1`.
`moduleStructure` drops them, because an `F[x]/(1)` summand is not part
of anyone's answer, and returns the free rank `m - rank` separately.

`quotientOrder` returns the monic product of the invariant factors when
`rank = m` and `0` otherwise. Both values are correct rather than
fallbacks, and the `0` is the same convention `latticeIndex` uses in
[hex-hermite](hex-hermite.md): an element of `F[x]` annihilates the whole
quotient only if it annihilates the free summand, so when `rank < m` the
order ideal really is `0`.

It is therefore an invariant **of the quotient**, not of the quotient's
torsion part, and the difference matters. The torsion part is annihilated
by `∏ dᵢ` whatever the free rank is, so its own order polynomial is
`(invariantFactors A).foldl (· * ·) 1` unconditionally. That is one fold
away and is not given its own name here, but a caller who wants "the
order polynomial" and reads `0` has asked the wrong function.

Note what the polynomial case does *not* have.
[hex-smith](hex-smith.md)'s `quotientOrder` returns an integer, because a
finite abelian group has an order and the analogy there is with a number.
Over `F[x]` the coefficient-field-independent answer is the monic
generator, so the analogy is with the *ideal*. A cardinality exists only
when `F` is finite: over `F_q` the torsion part has `q^(∑ deg dᵢ)`
elements. The degree `∑ deg dᵢ` is the dimension of the torsion part as
an `F`-vector space, which is the number a caller usually wants next, and
is one `degree?` away.

`solve` needs both transforms, not one. From `S = U * A * V`, the system
`vecMul x A = b` becomes `vecMul z S = vecMul b V` with
`z = vecMul x U⁻¹`, so the right-hand side is transformed by `V` before
the diagonal solve and the answer is mapped back by `x = vecMul z U`.
Solving the diagonal system against `b` directly is wrong whenever
`V ≠ I`, which is the usual case, and the transformed right-hand side
gets its own lemma in the theorem list.

`detDivisor` is `noncomputable` under design principle 11: its
definition enumerates exponentially many minors and there is no runtime
twin. It is **defined by that enumeration and not through `snf`**, since
defining it through `snf` would make `IsSNF.detDivisor_eq` circular. The
executable route to its value is the product of the first `k` invariant
factors, which is what that theorem states.

Its definition is a fold of `Hex.DensePoly.gcd` over the enumerated
minors followed by `monicize`. That definition is *not* obviously
independent of the fold order, because `gcd` is only determined up to a
unit at each step, so the characterisation rather than the definition is
what downstream proofs cite:

```lean
theorem detDivisor_spec (A : Matrix (DensePoly F) n m) (k : Nat) :
    (detDivisor A k = 0 ∨ (detDivisor A k).Monic)
      ∧ (∀ M ∈ minors A k, detDivisor A k ∣ M)
      ∧ (∀ d, (∀ M ∈ minors A k, d ∣ M) → d ∣ detDivisor A k)
```

Monic-or-zero plus those two divisibility clauses pin the value exactly,
which is what makes fold-order independence a corollary instead of a
proof obligation at every use site.

## Correctness theorems

```lean
theorem snfData_isSNF (A : Matrix (DensePoly F) n m) : IsSNF A (snfData A)
theorem snf_eq (A : Matrix (DensePoly F) n m) :
    snf A = diagMatrix (snfData A).diag n m
theorem snfRank_eq (A : Matrix (DensePoly F) n m) : snfRank A = (snfData A).rank
theorem snfDiagonalData_isSNF {r : Nat} (d : Vector (DensePoly F) r) :
    IsSNF (diagMatrix d r r) (snfDiagonalData d)

-- The determinantal-divisor characterisation, which is the specification.
-- Stated for every k, including k > S.rank, where both sides are zero.
theorem IsSNF.detDivisor_eq {A : Matrix (DensePoly F) n m} {S : SmithData F n m}
    (h : IsSNF A S) (k : Nat) :
    detDivisor A k =
      if k ≤ S.rank then (S.diag.take k).foldl (· * ·) 1 else 0

-- Uniqueness, in the form callers use.
theorem IsSNF.rank_eq (h : IsSNF A S) (h' : IsSNF A S') : S.rank = S'.rank
theorem IsSNF.diag_eq (h : IsSNF A S) (h' : IsSNF A S') (i : Nat)
    (hi : i < S.rank) (hi' : i < S'.rank) : S.diag[i] = S'.diag[i]

-- Agreement with the determinant, in value and in degree.
theorem prod_invariantFactors (A : Matrix (DensePoly F) n n) (h : snfRank A = n) :
    (invariantFactors A).foldl (· * ·) 1 = monicize (Matrix.det A)
theorem degree_prod_invariantFactors (A : Matrix (DensePoly F) n n)
    (h : snfRank A = n) :
    ((invariantFactors A).foldl (fun acc p => acc + p.degree?.getD 0) 0) =
      (Matrix.det A).degree?.getD 0

-- The consumer-facing statements.
theorem solve_iff_diagonal {A : Matrix (DensePoly F) n m} {b} (S := snfData A) :
    (∃ x, vecMul x A = b) ↔
      ∃ z, vecMul z (diagMatrix S.diag n m) = vecMul b S.right
theorem solve_sound {A : Matrix (DensePoly F) n m} {b x} :
    solve A b = some x → vecMul x A = b
theorem solve_complete {A : Matrix (DensePoly F) n m} {b} :
    (∃ x, vecMul x A = b) → (solve A b).isSome
theorem quotientOrder_eq (A : Matrix (DensePoly F) n m) :
    quotientOrder A =
      if snfRank A = m then (invariantFactors A).foldl (· * ·) 1 else 0
```

Every signature above elaborates as written against the current tree,
with `monicize` supplied as the prerequisite below defines it, and with
the four uses of `Matrix.det` needing the commutative-ring instance that
the same section asks to move.

`IsSNF.detDivisor_eq` is the theorem to prove first, and it must be
stated for every `k` rather than only for `k ≤ S.rank`, for the reason
[hex-smith](hex-smith.md) records: the `k ≤ S.rank` form cannot prove
`rank_eq`, because the value that separates two candidate ranks is
`k = S.rank + 1`, exactly where the restricted statement does not apply.

`degree_prod_invariantFactors` has no integer counterpart and is worth
stating separately. Over `ℤ` the product of the invariant factors is
`|det A|` and there is nothing more to say. Over `F[x]` the *degrees*
add to `deg det A`, which is the bound a caller uses to size buffers, to
predict the cost of the next step, and to check a result against
`hex-determinant` without comparing polynomials. It is also the only
statement in this library that bounds the size of the answer, which
matters because nothing bounds the size of the intermediate values.

**The prerequisite in `hex-determinant` is the same one
[hex-smith](hex-smith.md) names, and it still does not exist.** The
argument for `detDivisor_eq` needs each `k × k` minor of a product to
expand as a combination of the `k × k` minors of the factors, that is,
Cauchy-Binet in its general rectangular form. `HexDeterminant/Minor.lean`
provides only `deleteRowCol`; `HexDeterminant/CauchyBinet.lean` builds
`columnTupleMatrix`, which selects `n` columns from a matrix that has
exactly `n` rows, so the row side is never chosen; `HexMatrix/Submatrix.lean`
offers prefix-taking slices only. So `hex-determinant` needs selected
submatrices indexed by a pair of strictly increasing index maps,
enumeration of the `k`-subsets of `Fin n`, Cauchy-Binet for a selected
minor of a product, and the divisibility lemmas that turn that expansion
into invariance of `detDivisor` under unimodular multiplication.

Two remarks specific to this library. The work is stated over a
commutative ring in `hex-determinant`, so it is done once and serves both
Smith libraries; scheduling it for either one gets the other for free.
And the gcd-and-divisibility half is *not* shared: over `ℤ` it is
arithmetic in `Nat`, and over `F[x]` it is the monic-generator
characterisation above. Implementation of either library should not be
scheduled before the Cauchy-Binet half lands. Nothing else in this SPEC
depends on it, so the executable parts and the certificate can proceed in
parallel with it.

## Certificates

The shape follows [hex-smith](hex-smith.md): four product identities and
a decidable shape test.

```lean
/-- Accepts `(S, T)` as a Smith normal form of `A`, where `T = U * A` is
the intermediate product. -/
def snfCert (A : Matrix (DensePoly F) n m) (S : SmithData F n m)
    (T : Matrix (DensePoly F) n m) : Bool :=
  (S.left * A == T)
    && (T * S.right == diagMatrix S.diag n m)
    && (S.left * S.leftInv == Matrix.identity n)
    && (S.right * S.rightInv == Matrix.identity m)
    && isSNFShape S

theorem snfCert_sound : snfCert A S T = true → IsSNF A S
```

`isSNFShape` is the decidable reflection of **exactly the four fields of
`IsSNF` that the four product identities do not already establish**:

```lean
def isSNFShape (S : SmithData F n m) : Bool :=
  decide (S.rank ≤ n) && decide (S.rank ≤ m)
    && S.diag.toList.all (fun p => p.leadingCoeff == 1)
    && (S.diag.toList.zip S.diag.toList.tail).all (fun q => (q.2 % q.1).isZero)
```

This elaborates as written. Two of its clauses are written out rather
than stated abstractly, and in both cases the abstract version does not
elaborate, which is worth recording so an implementer does not spend the
afternoon rediscovering it. `Hex.DensePoly.Monic p` is
`p.leadingCoeff = 1`, a `Prop` with no `Decidable` instance derived
through the definition, so the test is written on `leadingCoeff`
directly. `Hex.DensePoly`'s `Dvd` instance is `∃ r, q = p * r`, which is
not decidable at all, so the chain is tested by `%` against a divisor the
`Monic` clause has just established is monic, and `isSNFShape`'s
soundness proof has to supply the existential witness from that
remainder.

It does **not** test that the off-diagonal entries vanish or that the
trailing diagonal entries are zero, and adding those tests would be a
mistake worth naming, because it is the obvious thing to write. Those
two conditions are not conditions on `S` at all: `mul_eq` compares
against `diagMatrix S.diag n m`, which is *constructed* zero off the
diagonal and zero past `S.rank`, so the second product identity already
carries them and a Boolean re-test of a constructed matrix checks
nothing.

The rank bounds, by contrast, are not implied by anything else in the
checker, and dropping them is unsound rather than merely redundant. Take
`n = m = 0`, `S.rank = 1`, `S.diag = #v[1]`, and all four transforms the
empty identity. Every product identity holds, because every matrix
involved is empty, and `S.diag[0]` is monic. `rank_le_n` is `1 ≤ 0`. A
shape test built out of the entry conditions alone accepts this.

Because the products are formed, the right-hand identity is checked
directly rather than transposed. [hex-smith](hex-smith.md) checks
`T * V = S` in the form `Vᵀ * Tᵀ = Sᵀ` because its primitive handles
left multiplication only, and that transposition has no purpose here.

**`mulEqCert` does not transfer, and nothing in `hex-lll` replaces it.**
`mulEqCert` (still `Hex.Internal.mulEqCert` in `HexLLL/Certificate.lean`,
`Hex.Matrix.mulEqCert` after the promotion
[hex-hermite](hex-hermite.md) asks for) decides `U * A = C`
by packing each row into a single large integer through Kronecker
substitution, so that the product matrix is never formed. Its three
helpers, `maxAbs`, `packWidth`, and `packRow`, are all scans of `Int`
entries computing an absolute-value bound and a digit width, and none of
those notions has a `DensePoly F` counterpart: the size of a polynomial
is its degree, and degrees do not pack into digits. So this SPEC does
not ask for `mulEqCert` to be generalised, and an implementer should not
try. The polynomial case has its own primitive.

**The polynomial substitute is evaluation.** Two `n × m` matrices over
`F[x]` with entries of degree at most `D` are equal exactly when they
agree at `D + 1` distinct points of `F`, so each product identity reduces
to `D + 1` scalar matrix products over `F`. It is deterministic, so it
supports a `Bool` with a soundness theorem rather than a probabilistic
argument:

```lean
/-- Decides `U * A = C` by evaluation at the supplied points. Sound when
the `k` points are pairwise distinct and `k` exceeds the degree of every
entry of `U * A` and of `C`. -/
def mulEqCertAt {k : Nat} (pts : Vector F k)
    (U : Matrix (DensePoly F) n n) (A C : Matrix (DensePoly F) n m) : Bool
```

**When it wins, and when it does not.** Checking `U * A = C` for
`U : n × n` and `A : n × m` with classical polynomial multiplication
costs `Θ(n² m D²)` coefficient operations. The evaluation route costs
`Θ((n² + n m) D²)` to evaluate the two input matrices at `D + 1` points
by Horner, plus `Θ(n² m D)` for the `D + 1` scalar products. So the
saving is a factor of `D` on the multiplication term only, and it is a
real saving exactly when `n² m D` dominates `(n² + n m) D²`, which is
when the dimensions are large relative to the degree. At small `n` and
large `D` the evaluation is the whole cost and there is nothing to win.
Do not state the factor of `D` unconditionally.

The hypothesis `|F| > D` is real, and is why the points are an argument
rather than something the checker invents. Over `ZMod64 p` with a large
`p` it is satisfied for every degree that fits in memory; over
`ZMod64 2` it fails for every `D ≥ 2`.

**`snfCert` uses the direct products, and `mulEqCertAt` is a separate,
conditional helper.** No dispatcher between the two is specified, because
a sound dispatcher would have to compute a degree bound for `U * A` and
then produce that many pairwise distinct points of `F`, and "produce `k`
distinct points" is an interface `F` does not have in this project.
Specifying one is the work decision rule 4 under "Benchmarking" would
authorise, and it is not v1. Extending the point set into an extension
field of `F` would remove the `|F| > D` hypothesis and is also out of
scope.

**The certificate is complete**, as in [hex-smith](hex-smith.md): by
`IsSNF.rank_eq` and `IsSNF.diag_eq`, anything satisfying the shape
clauses with unimodular transforms has the rank and the diagonal of the
Smith normal form, so an accepted candidate is the answer. That
completeness is downstream of the uniqueness theorem, which is downstream
of the `hex-determinant` prerequisite above; until that chain is closed
the checker is sound but the "it is the answer" claim is not yet proved.
Certified dispatch to an external implementation is possible in the
shape `hex-lll`'s `certCheck` already uses, and is not part of v1.

## Prerequisite changes in other libraries

Five items. Each has a reason independent of this library, and none of
them blocks starting work here, because this SPEC can name the existing
paths until they land.

**`monicize` belongs in `hex-poly`.** There is no monic normalisation in
the tree today (`Hex.DensePoly.monicize` is an unknown constant), yet
`leadingCoeff`, `Monic`, and `scale` are all there and every consumer of
polynomial gcd over a field wants the monic representative.

```lean
/-- The monic associate of `p`, and `0` when `p = 0`. -/
def monicize [Lean.Grind.Field F] [DecidableEq F] (p : DensePoly F) : DensePoly F :=
  p.scale (1 / p.leadingCoeff)
```

It is total with no junk branch: `leadingCoeff 0 = 0` and
`Lean.Grind.Field.inv_zero` give `monicize 0 = 0`, which is the value the
callers want. This is not a new definition for one consumer:
`DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g` is written out inline
throughout `HexBerlekamp/RabinSoundness.lean` and
`HexBerlekamp/Irreducibility.lean`, and `hex-poly-fp` already carries the
`ZMod64 p` specialisation of its monicity lemma as
`FpPoly.scale_inv_leadingCoeff_monic`. Naming the operation once, at the
generic field, is what lets that lemma be stated once too. Note that
`HexBerlekampZassenhaus/BhksCandidates.lean` scales by
`leadingCoeff f` rather than by its inverse, which is the
leading-coefficient trick from the Mignotte bound and not this
operation; it is not a call site.

**`Lean.Grind.CommRing (DensePoly R)` belongs in `hex-poly`.** The
instance is `instGrindCommRingDensePoly` in `HexResultant/ExactDiv.lean`.
Against the current tree,

```lean
example {F : Type u} [Lean.Grind.Field F] [DecidableEq F] :
    Lean.Grind.CommRing (DensePoly F) := inferInstance
```

fails without importing `hex-resultant`.

**This is not a two-line move, and describing it as one would send an
implementer down the wrong path.** What sits in
`HexResultant/ExactDiv.lean` is the whole lightweight algebraic
hierarchy for `DensePoly R`: `natPow`, then `instNatCast`, `instOfNat`,
`instNSMul`, `instNPow`, `instIntCast`, `instZSMul` with their
coefficient lemmas, then `instGrindSemiringDensePoly`,
`instGrindRingDensePoly`, and only at the end
`instGrindCommRingDensePoly`. The underlying *lemmas* are in `hex-poly`
already (`mul_comm_poly`, `mul_assoc_poly`, `mul_add_right_poly`,
`mul_add_left_poly`, `mul_one_right_poly` in
`HexPoly/Euclid/MulRing.lean`, plus the additive laws in
`HexPoly/Operations.lean`), but the instance block assembled from them is
a couple of hundred lines and it has to move as a unit, with
`hex-resultant` re-exporting or importing what it still needs.

Which class each consumer wants is worth getting right, because they
differ. `Hex.Matrix.det` is stated for `[Lean.Grind.Ring R]`;
`Matrix.det_mul`, `Matrix.adjugate`, and `Matrix.mul_eq_one_comm` are
stated for `[Lean.Grind.CommRing R]`. Since the whole tower lives in one
file, both are unavailable together today.

The measured size of the gap: elaborating every Lean block in this SPEC
against `HexPoly`, `HexMatrix`, and `HexDeterminant` alone produces
exactly four failures, all `Lean.Grind.Ring (DensePoly F)` synthesis
failures at a use of `Matrix.det`, in `IsSNF.left_unit`,
`IsSNF.right_unit`, `prod_invariantFactors`, and
`degree_prod_invariantFactors`. Nothing else in the library needs the
tower. So the alternative to moving it is a dependency on
`hex-resultant` bought for four theorem statements, which is the wrong
trade in a project whose DAG is the thing it keeps clean. Moving it also
removes the same accidental dependency from any future consumer of
polynomial matrices, and
[hex-char-poly](hex-char-poly.md) records the same request from the
Cayley-Hamilton side.

**`DivModLaws` and `GcdLaws` need a generic field instance.** The three
existing instances are per-coefficient-type (`ZMod64 p`, `Rat`) or
Mathlib-facing (`Field R`), so a Mathlib-free library generic in `F`
cannot discharge them. The `GcdLaws` half is nearly free: the helper
lemmas `gcd_dvd_left_of_divModLaws`, `gcd_dvd_right_of_divModLaws`,
`dvd_gcd_of_divModLaws`, and `xgcd_bezout_of_divModLaws` in
`HexPoly/Euclid/Reconstruction.lean` already reduce it to `DivModLaws`
plus one remainder lemma, and both existing Mathlib-free instances are
assembled from exactly those. The
`DivModLaws` half is the real work, and it is larger than the three
coefficient hypotheses the division lemmas take as arguments (`hcancel`,
`hexact`, `h_top_ne` in `divMod_eq_of_reconstruction`), each of which
does follow from `mul_inv_cancel` and the absence of zero divisors in a
`Lean.Grind.Field`. `DivModLaws` has nine fields: those hypotheses give
`divMod_spec`, `divMod_remainder_degree_lt_of_pos_degree`, and
`divModMonic_eq_divMod_of_monic`, and the remaining six
(`mod_self_eq_zero`, `mod_eq_zero_of_dvd`, `mod_mod_of_not_pos_degree`,
`mod_eq_mod_of_congr`, `mod_add_mod`, `mod_mul_mod`) are the
modular-arithmetic laws, which the `ZMod64 p` and `Rat` instances each
discharge separately and which the Mathlib instance gets from
`EuclideanDomain`. What the prerequisite asks for is a single generic
constructor deriving all nine from the field hypotheses, stated once in
`hex-poly` next to the existing law packages, subsuming the two concrete
instances. It is a piece of work, not a rearrangement.

**`instExactDivLawsDensePoly` should move with the tower.** It is in
`HexResultant/ExactDiv.lean` beside the commutative-ring instances, and
it is what makes `hex-basic`'s generic `exactDiv` meaningful at
`DensePoly F`. Moving the tower and leaving this behind would produce
exactly the situation the relocation exists to avoid.

**`diagMatrix` must land in `hex-matrix` generic in `R`**, as described
under "Data and contract". This is the only one of the five that
[hex-smith](hex-smith.md) also asks for; what this library adds is the
requirement that the relocated signature not be specialised to `Int`.
The same relocation is discussed from a third side in
[hex-char-poly](hex-char-poly.md), which asks for `trace` and records
that `diagMatrix` is a separate addition it does not itself need.

## Complexity

`A` is `n × m` with rank `r` and entries of degree at most `D`. As in
[hex-smith](hex-smith.md) these are **matrix-update counts** rather than
worst-case complexity: they count row and column updates and `xgcd`
calls, each of which is one Euclidean run on operands of the stated
degree rather than a constant-time operation. A coefficient-operation
count would be the product of these with the operand degree, and that
product is measured rather than derived.

`P` is the number of times the pivot loop repeats at one diagonal
position. Each repetition strictly decreases the degree of the pivot, so
`P` is at most one more than the degree of the pivot at the moment the
position is entered, and in particular is bounded by no matrix
dimension.

Resist strengthening that to `P ≤ D + 1`. It is true at the first
diagonal position, where the pivot is an entry of `A`. At later
positions the pivot is chosen from the *working* block, whose degrees
have grown by an amount this SPEC does not bound, so the bound is stated
in a quantity the algorithm does not control. This is the same statement
as [hex-smith](hex-smith.md)'s "`P` is bounded by the bit length of the
entries", with degree in place of bit length, and it has the same
weakness for the same reason: the honest content is that `P` does not
depend on `n` or `m`.

| operation | algorithm | matrix updates, `xgcd` calls, divisibility tests | entry degree |
|---|---|---|---|
| `snf`, `snfRank` | classical Euclidean pivot loop, no accumulators | `O(P · r · (n + m) · max n m)` updates, plus `O(P · r · n · m)` `mod` tests | unbounded; measured, not proved |
| `snfData` | the same loop with four accumulators | `+ O(P · r · (n² + m²))` | larger than the form; see "Complexity" below |
| `snfDiagonal` | normalisation plus the bubble network | `r(r-1)/2` `xgcd` calls | bounded by the total degree of the input diagonal |
| `snfDiagonalData` | the same, with accumulators | `+ O(r²)` transform updates | transforms not bounded here |
| `invariantFactors` | `snf`, then a slice | as `snf` | `∑ deg dᵢ = deg det A` for square nonsingular `A` |
| `moduleStructure` | `snf` plus a filter | as `snf` | as `snf` |
| `solve` | `snfData`, one diagonal solve, two `vecMul`s | as `snfData`, plus `O(n² + m²)` | as `snfData` |
| `quotientOrder` | `snf`, then a product of the diagonal | as `snf`, plus `O(r)` | `deg = deg det A` when `rank = m = n` |

Four things the table does not say and should.

**The divisibility tests are a separate column for a reason.** Step 5 of
the pivot loop scans the trailing block asking `p ∣ a[i][j]`, and each
question is a polynomial remainder, not a comparison. On a run where the
answer is always yes, those `mod` calls are the whole cost of the step
and no `xgcd` is called at all, so folding them into the `xgcd` count
would understate the work by a factor that depends on the input.

**`snfDiagonalData`'s transforms are not bounded by its diagonal.** The
output diagonal is bounded by the total degree of the input diagonal,
because each entry divides the product. The accumulated `left`, `right`,
and their inverses are built from the Bezout coefficients of `r(r-1)/2`
`xgcd` calls, and this SPEC states no invariant bounding their degrees.
That is the same gap as for `snfData`, at a smaller scale, and the bench
records it on `diagonal-polysmith` for the same reason.

**The transform accumulation is the term to watch.** `snfData` costs
`snf` plus four accumulator updates per elementary operation, on
matrices of size `n × n` and `m × m` rather than `n × m`, and those
updates are polynomial multiplications whose operands grow. This is why
the two paths exist, and it is what decision rule 3 under "Benchmarking"
measures.

**The output is bounded and the working matrix is not.** For square
nonsingular `A`, `∑ deg dᵢ = deg det A ≤ n · D`, so the answer is small.
The intermediate entries have no such bound: the multipliers `s` and `t`
returned by `xgcd` have degrees up to `deg b - deg g` and
`deg a - deg g`, and degrees accumulate along a row over the course of
the elimination. This is the polynomial form of the entry-growth problem
that [hex-hermite](hex-hermite.md) calls the design problem of the
integer libraries, and it has the same status here: acknowledged,
unproved, and instrumented.

**Over `ℚ` there are two growth problems, not one.** Degrees grow as
above, and the rational coefficients grow independently, for the same
reason they do in integer elimination. The `rational-coefficients` bench
family exists to measure the second, and it is the reason
`hex-poly-smith` is not specified as an `F_p`-only library: an
implementation tuned only against `ZMod64 p` will look fine and be
unusable on `ℚ[x]`.

## Conformance

Per [SPEC/testing.md](../testing.md). Unlike
[hex-smith](hex-smith.md), this library **cannot extend the existing
matrix oracle**, and the reason is worth being explicit about because the
cheap-looking route does not exist.

`scripts/oracle/matrix_flint.py` serves `HexRowReduce`,
`HexDeterminant`, `HexBareiss`, and (per [hex-hermite](hex-hermite.md))
the two integer normal forms, and it reads the `matrix` fixture kind
emitted by `emitMatrixFixture` in `Hex/Conformance/Emit.lean`. That
emitter takes `List (List Int)`: there is no way to express a polynomial
entry through it. So this library needs

- a new fixture kind `polymatrix`, emitted by a new
  `emitPolyMatrixFixture` in `Hex/Conformance/Emit.lean`. Its schema has
  to be written down rather than left as "the entries", because the two
  coefficient types encode differently and the existing emitter already
  shows how:

  ```json
  {"kind": "polymatrix", "field": {"p": 65521} | {"rat": true},
   "rows": 3, "cols": 4,
   "entries": [[[c00…], [c01…], …], …]}
  ```

  For `ZMod64 p` each entry is a list of `Int` coefficients ascending by
  exponent, as `emitPolyFixture` already does. For `Rat` an entry is
  `{"num": [...], "den": [...]}`, two parallel `Int` lists with the
  denominators positive and each coefficient in lowest terms, which is
  the encoding `Hex/Conformance/Emit.lean` already uses for `Q`-valued
  polynomial results. A zero polynomial is the empty list, `rows` or
  `cols` may be `0`, and `entries` is then empty;
- a new oracle driver `scripts/oracle/polymatrix.py`;
- an emit driver `conformance/HexPolySmith/EmitFixtures.lean` exposed as
  `lean_exe hexpolysmith_emit_fixtures`, a property-check driver
  `conformance/HexPolySmith/Conformance.lean`, and a committed snapshot
  at `conformance-fixtures/HexPolySmith/smith.jsonl`;
- one tuple appended to `ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexPolySmith|hexpolysmith_emit_fixtures|scripts/oracle/polymatrix.py|conformance-fixtures/HexPolySmith/smith.jsonl"
```

No new job, no matrix, no new workflow file, per [SPEC/CI.md](../CI.md).

**Oracle choice, to be confirmed before the driver is written.** FLINT
appears to expose no Smith normal form for polynomial matrices:
`fmpz_mat_snf` is the integer routine, and the `nmod_poly_mat` and
`fmpz_poly_mat` families expose row reduction and solving rather than a
Smith form. That is the claim in this section most worth being wrong
about, so check it against the FLINT and python-flint versions CI
installs before accepting it. The two candidates are sympy's
`sympy.matrices.normalforms.smith_normal_form` at a polynomial domain
(`GF(p)[x]`, `QQ[x]`), and PARI's `matsnf` on a matrix of `t_POL`
entries through `cypari2`. Both sympy and cypari2 are already CI
dependencies, so neither adds an install step.

They do not cover the same surface. PARI's documented polynomial-entry
`matsnf` takes a square matrix, and the fixture list below requires both
rectangular orientations, so PARI can serve at most as a square-input
cross-check. sympy's `smith_normal_form` takes a matrix over any domain
it considers a principal ideal domain, so it is the only candidate for
the rectangular cases and the primary oracle unless it turns out not to
accept the polynomial domain. Both claims must be confirmed against the
versions CI installs, including what normalisation and what ordering the
results carry, before the driver is written. If neither is usable the fallback is a
self-check driver that verifies `U * A * V = S`, the two inverse
identities, and the shape clauses in Python against an independently
computed diagonal, which is weaker than an oracle and must be labelled
as such rather than quietly substituted.

**Normalisation is the whole risk in the comparison.** Every candidate
oracle returns invariant factors determined up to a unit, and some
return them in the reverse order. The driver normalises to monic and to
increasing-divisibility order before comparing, and that normalisation
is itself tested on fixtures with known answers before it is trusted to
report a mismatch. This is the same warning
[hex-hermite](hex-hermite.md) gives about column-style versus row-style
conventions, and it has the same failure mode: a plausible-looking
matrix that mismatches on every input and reads like an algorithm bug.

The oracle is compared on the diagonal only, never on `U` or `V`, which
are not unique. The transforms are checked in Lean by the product
identities instead.

**Cases that must be present:**

- the zero matrix, a `0 × k` and a `k × 0` matrix, and a matrix of rank
  `1`;
- **input where the first invariant factor is not the lowest-degree
  entry**: `diag(x, x + 1)`, whose Smith normal form is
  `diag(1, x² + x)`. An implementation that omits the divisibility step
  in the pivot loop returns `diag(x, x + 1)` here, so this is the single
  most important case in the suite, and it is the exact analogue of
  `[[2, 0], [0, 3]]` over `ℤ`;
- **input whose entries are non-monic**, with leading coefficients that
  are not `1` in every position that feeds a pivot. This is the case
  that catches a port of the integer step that omits the `u` factor, and
  it must appear over `ℚ` as well as over `ZMod64 p`, because a wrong
  unit is easy to miss modulo a small prime;
- **input whose gcds are non-monic before normalisation**, for example
  the pair `(x² - 1, x² + x)` in a column, where `Hex.DensePoly.gcd`
  returns `-x - 1`, together with the same pair in the other order,
  where it returns `x + 1`;
- input whose Smith normal form has a nontrivial chain of length three,
  for example `diag(x, x², x³)` conjugated by unimodular matrices;
- rank-deficient input, checking the trailing zeros and the rank;
- rectangular input in both orientations;
- input containing unit entries (nonzero constants), where the pivot
  becomes `1`;
- input already in Smith normal form, checking idempotence;
- diagonal input through `snfDiagonal` containing zeros and non-monic
  entries, including `#v[0, x]`, a non-monic entry followed by a zero,
  and `#v[0, 0]`, which is where an implementation that skips the
  normalisation phase divides by zero or returns a non-normal form;
- an unsolvable and a solvable polynomial system through `solve`, with
  the solvable one chosen so that `V ≠ I`, which is what catches a
  `solve` that forgets to transform the right-hand side;
- a `ZMod64 2` fixture of degree at least `2`, which is where the
  `|F| > D` hypothesis of `mulEqCertAt` fails. `snfCert` must accept it,
  because `snfCert` forms the products directly; the fixture exists so
  that a later change routing `snfCert` through `mulEqCertAt` fails here
  rather than silently accepting a wrong candidate;
- a `ℚ` fixture chosen so that naive elimination produces large
  coefficients, with the peak coefficient size recorded, so the growth
  claim under "Complexity" is checked rather than asserted.

The property checks in `conformance/HexPolySmith/Conformance.lean`
assert `U * A * V = S`, `U * W = I`, `V * X = I`, the three shape
clauses, monicity of every diagonal entry, the divisibility chain, the
degree identity `∑ deg dᵢ = deg det A` against `hex-determinant` on
square nonsingular input, and `solve` on both a solvable and an
unsolvable system.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), drivers at
`bench/HexPolySmith/Bench.lean`, no Mathlib import.

**Input families.**

- `random-dense-polysmith`: uniform entries over `ZMod64 p` at a
  degree ladder and a dimension ladder, square and nonsingular.
- `chain-conjugate-poly`: `U * diag(d) * V` for a known monic chain `d`
  and random unimodular `U`, `V`, so the expected answer is known and
  the difficulty is intermediate growth rather than the size of the
  answer.
- `rational-coefficients`: the same shapes over `Rat`, which is where
  coefficient growth appears on top of degree growth.
- `diagonal-polysmith`: diagonal input, the family `snfDiagonal` exists
  for.
- `small-field`: `ZMod64 2` coefficients, where the field is too small
  for the evaluation-based checker and the constant-factor profile of
  the arithmetic is different.

**Comparators.** sympy `smith_normal_form` at a polynomial domain and
PARI `matsnf`, both `informational`, and both subject to the
confirmation under "Conformance". Neither holds a required threshold:
sympy is a pure-Python implementation and will lose by a large and
uninformative factor, and PARI's dispatch is not the algorithm specified
here. Recorded for orientation in
`reports/hex-poly-smith-performance.md`.

**Growth instrumentation is required, not optional.** The default
algorithm ships with no proven bound on intermediate size, so the bench
records peak intermediate entry degree on every family, and additionally
peak coefficient bit-size and time spent in rational arithmetic on
`rational-coefficients`. Those numbers are the evidence for or against
specifying a fraction-free or modular variant, per "Open questions". A
wallclock ratio alone cannot separate degree growth from coefficient
growth, which is the whole reason both families exist.

**Decision rules, written down in advance.** Each is stated over a range
rather than at one ladder endpoint.

1. `snfDiagonal` must be faster than `snf` on `diagonal-polysmith` by a
   margin that grows with `r`, since it skips the elimination entirely.
   A flat or shrinking margin means the fast path is not being taken,
   which is a bug rather than a benchmark result. It is not stated as a
   fixed multiple, because at small `r` the two are legitimately
   comparable.
2. Threading the monicity proof through the pivot loop so that
   `divModMonic` replaces `divMod` is kept only if it wins across the
   upper half of both the degree and the dimension ladders on
   `rational-coefficients`, and does not lose on
   `random-dense-polysmith`. The saving is one coefficient division per
   long-division step, which is nearly free over `ZMod64 p` and is a
   rational-number division over `Rat`, so this is exactly the kind of
   difference that shows on one coefficient type and not the other. The
   cost is carrying a proof through the recursion, which is real, so a
   win on `Rat` alone is the case that justifies it.
3. The `snf` and `snfData` paths are measured separately on every
   family, and the ratio between them is reported rather than the
   absolute times alone. That ratio is the evidence for the API split: if
   it is close to `1` across both ladders, the split is carrying
   complexity for nothing and one entry point returning `SmithData`
   should replace both. The prediction is that it grows with the
   dimension, because the accumulators are `n × n` and `m × m` while the
   form is `n × m`.
4. The evaluation-based `mulEqCertAt` is kept only if it beats the
   direct product across the upper half of the **dimension** ladder at
   fixed degree, which is the regime the operation count above says it
   can win in. Measuring it along the degree ladder instead would be
   measuring the case it is predicted to lose. It is an optimisation to a
   checker that is not on the hot path of any consumer, so a marginal win
   does not justify carrying both routes and the point supply a
   dispatcher would need.

## The Mathlib layer

`hex-poly-smith-mathlib` proves:

```lean
/-- The executable polynomial matrix as a Mathlib matrix over
`Polynomial F`. -/
noncomputable def polyMatrixEquiv (A : Hex.Matrix (DensePoly F) n m) :
    Matrix (Fin n) (Fin m) (Polynomial F)

/-- The executable Smith normal form as Mathlib's structure, for the
submodule spanned by the rows of `A`. -/
noncomputable def smithNormalForm (A : Hex.Matrix (DensePoly F) n m) :
    Module.Basis.SmithNormalForm
      (Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A))) (Fin m)
      (snfRank A)

/-- The divisibility chain, which Mathlib's structure does not carry. -/
theorem smithNormalForm_chain (A : Hex.Matrix (DensePoly F) n m) (i : Nat)
    (h : i + 1 < snfRank A) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣ (smithNormalForm A).a ⟨i + 1, h⟩

/-- Monic is Mathlib's canonical associate for `Polynomial F`. -/
theorem monicize_eq_normalize (p : DensePoly F) :
    toPolynomial (monicize p) = normalize (toPolynomial p)

/-- The structure theorem, instantiated at the executable output. -/
noncomputable def quotientEquiv (A : Hex.Matrix (DensePoly F) n m) :
    (Fin m → Polynomial F) ⧸ Submodule.span (Polynomial F)
        (Set.range (polyMatrixEquiv A)) ≃ₗ[Polynomial F]
      (Fin (m - snfRank A) → Polynomial F) ×
        ⨁ i : Fin (snfRank A),
          Polynomial F ⧸ Ideal.span {toPolynomial ((invariantFactors A)[i])}

/-- The executable rank is the rank over the field of rational
functions. -/
theorem rank_eq_ratFunc_rank (A : Hex.Matrix (DensePoly F) n m) :
    snfRank A =
      ((polyMatrixEquiv A).map (algebraMap (Polynomial F) (RatFunc F))).rank
```

Four things are worth knowing before this layer is scheduled.

**`polyMatrixEquiv` is a composite and should be built as one.**
`hex-poly-mathlib` supplies `DensePoly R ≃+* Polynomial R` and
`hex-matrix-mathlib` supplies the matrix equivalence; what this layer
needs is the entrywise map of the first through the second, which is a
definition neither library has a reason to write. Writing it here once,
with its `map`-commutes lemmas for `*`, `+`, and `det`, is what keeps
every subsequent proof from re-deriving the same transport.

**Mathlib's `Module.Basis.SmithNormalForm` does not carry the
divisibility chain.** Its fields are `bM`, `bN`, `f`, `a`, and `snf`,
with `snf : ∀ i, (bN i : M) = a i • bM (f i)`. Nothing constrains
`a i ∣ a (i+1)`, so the structure is a simultaneous-basis statement
rather than an invariant-factor statement, and its `a` is not canonical.
Mathlib has no invariant factors and no determinantal divisors. So
`smithNormalForm_chain` is genuinely new content rather than a
transport, and the executable library is the only source of canonicity.
This is the same observation [hex-smith](hex-smith.md) records, and the
two libraries would want the same upstream fix, which is an argument for
making it once and not before either exists.

**Monic is `normalize`, and saying so is the point of
`monicize_eq_normalize`.** Mathlib has `NormalizedGCDMonoid (Polynomial K)`
for a field `K`, whose `normalize` divides by the leading coefficient.
Proving that the executable normalisation agrees with it is what lets a
Mathlib-side consumer use Mathlib's gcd vocabulary on the executable
output without a second normalisation convention. The integer library
has no counterpart, because `Int.gcd`'s codomain already settles it.

**The rank statement is the expensive one, and not for the obvious
reason.** `Matrix.rank` is defined over any commutative semiring in
Mathlib, so it does apply at `Polynomial F`; what it computes there is
the rank of the image submodule, which over a non-field is not the number
this library returns. The statement worth having is the one over the
fraction field, which is why `rank_eq_ratFunc_rank` passes through
`RatFunc F`. It needs the `algebraMap` into `RatFunc`, the fact that the
invariant factors are nonzero exactly below the rank, and the transport
of unimodularity, so it should be scheduled after the module statements
rather than with them. Stating it against `(polyMatrixEquiv A).rank`
instead would typecheck and would be a different, weaker theorem.

Following the project split, the uniqueness theorems `IsSNF.rank_eq` and
`IsSNF.diag_eq` are Mathlib-free and proved in `hex-poly-smith`: they are
statements about the executable types with an elementary proof, and no
part of them is shorter through Mathlib.

## What is deliberately not here

**Characteristic matrices and everything downstream of them.** `xI - A`,
the invariant factors of `xI - A`, the matrix minimal polynomial, and
the rational canonical form are `hex-invariant-factors` in
[future-work](../future-work.md). The separation is the point of this
library: the Smith form of a polynomial matrix is a general algorithm
with several consumers, and a library that also knew about companion
matrices would be unusable by the consumers that are not about linear
operators. `hex-invariant-factors` depends on this library, supplies
`xI - A` itself, and needs no theorem from here beyond the ones stated
above.

A naming warning for whoever writes that library: **it must not be
called `hex-rcf`.** [hex-rcf](hex-rcf.md) in this project is the
real-closed-field decision procedure and the `rcf` tactic, and the
abbreviation collides exactly.

**Polynomial Hermite, Popov, and shifted forms.** Row-reduced and
column-reduced forms of polynomial matrices, minimal approximant bases,
and the degree-minimality conditions that make them canonical are a
separate subject with separate consumers. Nothing here depends on them
and nothing here anticipates them. See "Read the integer pair first".

**Elementary divisors.** The prime-power decomposition of the invariant
factors needs factorization in `F[x]`. Unlike the integer case, the
project *has* that for a finite field (`hex-berlekamp` factors over any
`F_q`), so this is reachable rather than blocked, and it is still out of
scope: it is a short function on top of `invariantFactors` and belongs in
whichever library owns the factorization, not here, and it would restrict
the coefficient field in a library that otherwise does not.

**`ℤ[x]` and other non-field coefficients.** `ℤ[x]` is not a principal
ideal domain, and a matrix over it need not have a Smith normal form at
all. This is the most likely misuse of the library, because the type
`Matrix (DensePoly Int) n m` is perfectly well formed, so the
`Lean.Grind.Field F` hypothesis is the guard and no total form over a
general coefficient ring should be added to accommodate a caller that
wants one.

**Sparse input.** Relation matrices are often sparse and dense
elimination fills them in immediately. The sparse matrix item in
[future-work](../future-work.md) names this as one of the cases where a
dense representation genuinely fails, and it should be revisited there
rather than worked around here.

**A shared Euclidean-domain abstraction.** See "Read the integer pair
first". The question is closed, not deferred.

## File organisation

```
HexPolySmith/
  Contracts.lean     -- SmithData, IsSNF, isSNFShape, IsSNF.left_unit
  Step.lean          -- the monic-normalising 2x2 step and its inverse
  Smith.lean         -- snf, snfRank, snfData: one loop, accumulators optional
  Diagonal.lean      -- snfDiagonal, snfDiagonalData: normalisation and the sweep
  Divisor.lean       -- detDivisor, detDivisor_spec, IsSNF.detDivisor_eq
  Unique.lean        -- IsSNF.rank_eq, IsSNF.diag_eq, snfRank_eq, snf_eq
  Structure.lean     -- invariantFactors, moduleStructure, quotientOrder, solve
  Cert.lean          -- snfCert, mulEqCertAt, and their soundness
HexPolySmith.lean    -- umbrella
HexPolySmithMathlib/
  Equiv.lean         -- polyMatrixEquiv and its map-commutes lemmas
  Basis.lean         -- Module.Basis.SmithNormalForm from the executable output
  Chain.lean         -- the divisibility chain Mathlib's structure omits
  Quotient.lean      -- the structure theorem for the quotient
  Rank.lean          -- rank over RatFunc
HexPolySmithMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexPolySmith:
    deps: [HexPoly, HexMatrix, HexDeterminant]
    mathlib: false
    done_through: 0
    status: draft
  HexPolySmithMathlib:
    deps: [HexPolySmith, HexPolyMathlib, HexMatrixMathlib, HexDeterminantMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

`HexPoly` supplies `DensePoly` and its Euclidean operations, `HexMatrix`
supplies `Matrix` and the elementary operations, and `HexDeterminant`
supplies `det`, the adjugate identities, and Cauchy-Binet. Until the
`Lean.Grind.CommRing (DensePoly R)` instance moves down (see
"Prerequisite changes in other libraries"), `HexResultant` has to be
added to the first list, which is a dependency on a two-line instance and
the reason the move is listed at all.

## Open questions

- **Whether a modular or fraction-free variant is worth specifying.**
  The default is the classical pivot loop, which is total, has a
  termination proof, and has no bound on intermediate size. The
  candidates are a variant that works in `F[x]/(d)` for a multiple `d` of
  the largest invariant factor, and a fraction-free variant in the style
  of `hex-bareiss`. The growth instrumentation under "Benchmarking" is
  what decides whether either is called for, and the answer may differ
  between `ZMod64 p` (where only degrees grow) and `Rat` (where
  coefficients grow too). Neither should be started on the strength of
  the name.
- **Whether `detDivisor` should be public at all.** The same question
  [hex-smith](hex-smith.md) leaves open, with the same answer for now: it
  is the specification function, it has no efficient direct evaluation,
  and the statement `d₁ ⋯ d_k = D_k` is the thing a mathematician wants
  to cite. It is exported with its docstring saying so.
- **Whether the two Smith libraries should share a file layout at
  all.** They currently would, module for module, while sharing no code.
  That is either a sign that the abstraction is closer than this SPEC
  claims, or a sign that the layout is the natural one for the subject
  and says nothing. Revisit only if a third instance of the same shape
  appears.
- **Whether `snfRank` can avoid the full elimination.** The API splits
  the form from the transforms, which is settled, but `snfRank` still
  runs the whole pivot loop to count nonzero diagonal entries, and the
  rank of `A` over `F(x)` is in principle available from a cheaper
  computation (row reduction over the fraction field, or an evaluation at
  a point where the rank does not drop). Neither route is free: the first
  needs `RatFunc`-style arithmetic the Mathlib-free layer does not have,
  and the second needs a bound on the bad points. Measure `snfRank`
  against `snf` on `random-dense-polysmith` before deciding whether the
  question is worth reopening.
