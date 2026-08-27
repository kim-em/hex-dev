# hex-poly-fast (fast dense-polynomial arithmetic)

Fast multiplication, division, gcd, multipoint operations, and Padé
approximation for `DensePoly`, without changing the deliberately small
schoolbook interface of hex-poly. Mathlib-free.

This SPEC replaces the "Fast polynomial arithmetic" sketch in
[future-work](../future-work.md). It depends on both hex-poly and
[hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md). Coefficient-specific kernels
remain in the libraries that own the coefficient representation:
hex-poly-z owns integer packing and CRT reconstruction, hex-mod-arith owns
word-modular transforms, hex-modular owns integer CRT, and hex-poly-fp owns
the `FpPoly` adapters and dispatch.

## Why this library exists

**The current semantic foundation is intentionally quadratic.**
`DensePoly.mul` is the schoolbook convolution over only `[Add R] [Mul R]`.
That weak signature is useful: it makes multiplication available over every
coefficient type that can state it and gives every optimized routine one
small reference operation to agree with. It cannot itself be replaced by
Karatsuba, which needs subtraction, or by Kronecker substitution and NTTs,
which know the coefficient representation.

**Fast division is not a separate optimization.** Newton division reverses
the divisor, inverts it as a truncated series, and uses short products to
recover the quotient. Half-gcd then groups many such degree-reducing steps.
Product trees, remainder trees, interpolation, and Padé approximation use
the same multiplication, reciprocal, and middle-product machinery. A library
that supplied only `mulKaratsuba` would leave the important algorithms unable
to compose.

**The coefficient libraries need one algorithmic consumer interface.**
`ZPoly` and `FpPoly` are abbreviations of `DensePoly`, not new representations
that can carry competing `Mul` instances. An explicit multiplication plan
lets integer Kronecker, direct NTT, and CRT-NTT kernels drive the generic
division and tree algorithms without instance ambiguity and without making
this library depend back on either coefficient library.

**The performance work must reach callers.** A fast kernel that no existing
consumer selects is not a completed optimization. The last milestone audits
the Hensel, finite-field, GFq, Berlekamp, and Berlekamp-Zassenhaus hot paths
and changes each call site only when its own benchmark crosses over.

## Placement in the DAG

The generic library has exactly two direct dependencies:

```text
hex-basic ── hex-truncated-series ──┐
                                    ├── hex-poly-fast
hex-poly ────────────────────────────┘
```

It does not depend on hex-mod-arith, hex-modular, hex-poly-fp, or hex-poly-z.
Those libraries construct plans above it:

```text
hex-arith ── hex-mod-arith ─────────┐
hex-arith ── hex-modular ───────────┼── hex-poly-fp / hex-poly-z
hex-poly-fast ───────────────────────┘
```

This direction is essential. Putting `ZMod64` or `Int` dispatch in
hex-poly-fast would make the generic algorithms drag both arithmetic stacks
into every consumer. Putting polynomial reversal in hex-truncated-series
would give that library a hex-poly dependency and destroy the reason its
fixed-vector representation sits below polynomial arithmetic.

hex-truncated-series keeps its own `mulUpTo` implementation. A library above
it cannot change what `TSeries.invOfUnit` calls. Its SPEC therefore requires
a measured generic Karatsuba path for `mulUpTo`, while this library supplies
a separate plan-driven Newton inverse whose correctness is stated by
conversion to `TSeries.invOfUnit`. The small duplication is the price of the
acyclic dependency boundary; the semantic proof is shared.

## Scope

In scope:

- explicit lawful multiplication plans;
- schoolbook and Karatsuba full products, squaring, unbalanced products, and
  arbitrary clipped products;
- cyclic and negacyclic products with positive length;
- reversal and fixed-precision `TSeries` bridges;
- Newton reciprocal precomputation and fast monic/field division;
- half-gcd, gcd, full extended gcd, and one-sided extended gcd;
- balanced product and remainder trees;
- reusable multipoint evaluation and interpolation plans;
- homogeneous Padé approximants and the normalized rational-series form;
- agreement theorems, conformance fixtures, crossover benchmarks, and the
  benchmark-gated downstream adoption audit.

Coefficient-specific work specified here but implemented in its owner:

- two- and four-point Kronecker substitution in hex-poly-z;
- redundant-residue NTT butterflies and reusable transform plans in
  hex-mod-arith;
- balanced batch CRT in hex-modular;
- direct and auxiliary-prime NTT convolution in hex-poly-fp and hex-poly-z.

Out of scope:

- changing `DensePoly.mul`, its `Mul` instance, or its minimal typeclass
  requirements;
- a `PolyOps` abstraction over dense and sparse representations;
- Toom-Cook before a measured gap remains between Karatsuba and the
  coefficient-specific kernels;
- a limb-level arbitrary-precision integer middle product;
- multivariate multiplication, sparse interpolation, or polynomial-matrix
  approximant bases;
- a new Mathlib companion.

## The semantic boundary stays schoolbook

Every public optimized operation reduces to a theorem about existing
`DensePoly` semantics. Dispatch thresholds, cached roots, scratch allocation,
and the chosen kernel are absent from theorem statements.

There is deliberately no typeclass for the plan. Plans are passed explicitly:

```lean
namespace Hex.DensePoly

structure MulPlan (R : Type u) [DecidableEq R]
    [Lean.Grind.CommRing R] where
  /-- A complete normalized product. -/
  mul : DensePoly R → DensePoly R → DensePoly R
  /-- A specialized square; it need not call `mul p p`. -/
  square : DensePoly R → DensePoly R
  /-- `len` coefficients beginning at product degree `lo`, shifted down. -/
  slice : Nat → Nat → DensePoly R → DensePoly R → DensePoly R
  mul_eq : ∀ a b, mul a b = a * b
  square_eq : ∀ a, square a = a * a
  coeff_slice : ∀ lo len a b i,
    (slice lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0

def schoolbookPlan : MulPlan R
def karatsubaPlan (cutoff : Nat) : MulPlan R

def mulWith (plan : MulPlan R) (a b : DensePoly R) : DensePoly R :=
  plan.mul a b

def squareWith (plan : MulPlan R) (a : DensePoly R) : DensePoly R :=
  plan.square a

def mulLow (plan : MulPlan R) (len : Nat)
    (a b : DensePoly R) : DensePoly R :=
  plan.slice 0 len a b
```

`Zero R` is derived from the commutative-ring numeral structure rather than
accepted as an independent parameter.  This matters for normalized dense
polynomials: a separately supplied `Zero` could disagree with the ring's
additive identity, invalidating both trimming and Karatsuba subtraction.

The proof fields are erased. Passing a plan does not move correctness into a
runtime checker, and using a structure rather than a typeclass prevents a
global choice of integer or finite-field multiplication from leaking into
unrelated code.

`slice lo len` is the primitive rather than separate low, high, and middle
implementations. The named middle-product wrapper selects the standard range:
for operand sizes `m >= n > 0`, coefficients `n - 1` through `m - 1`, shifted
down to indices `0` through `m - n`. Callers that already know `m`, `n`, and
the inequalities take the proof-accepting form; the checked form reorders the
operands and handles an empty operand by returning zero.

The generic agreement theorems are short projections:

```lean
theorem mulWith_eq (plan : MulPlan R) (a b : DensePoly R) :
    mulWith plan a b = a * b

theorem squareWith_eq (plan : MulPlan R) (a : DensePoly R) :
    squareWith plan a = a * a

theorem coeff_mulLow (plan : MulPlan R) (len i : Nat) (a b : DensePoly R) :
    (mulLow plan len a b).coeff i =
      if i < len then (a * b).coeff i else 0
```

The substantive proofs are the laws of each plan.

## Generic multiplication algorithms

### Schoolbook plan

`schoolbookPlan` delegates full multiplication to `DensePoly.mulImpl` and
computes a slice without first allocating the full result. For output index
`k`, it folds exactly the valid pairs `i + j = lo + k`. It is both the base
case of every recursive plan and the independent executable comparator used
by conformance tests.

### Karatsuba plan

The Karatsuba plan works over `Lean.Grind.CommRing`, because the cross term
uses subtraction. For a balanced split `a = a0 + x^k a1` and
`b = b0 + x^k b1`, it computes

```text
z0 = a0*b0
z2 = a1*b1
z1 = (a0+a1)*(b0+b1) - z0 - z2
```

and assembles `z0 + x^k z1 + x^(2k) z2`. The recursion:

- stops at an explicit cutoff, including cutoff zero;
- handles odd sizes without padding an observable trailing zero;
- normalizes only once at the public `DensePoly` boundary;
- uses uniquely owned arrays for assembly rather than repeated append;
- has a specialized square recursion, reusing the two equal halves rather
  than rediscovering equality inside the generic product;
- prunes a recursive subproduct when its entire output interval lies outside
  `slice lo len`.

For operands with sizes `m >> n`, the long operand is split into blocks near
the shorter size and the block products are accumulated at their offsets.
Padding both inputs to `max m n` is forbidden: it turns a linear number of
useful blocks into a balanced product whose unused work can dominate the
caller. The declared cost is
`O(ceil(m/n) * M(n))` for `m >= n > 0`, with `M` the balanced plan cost.

Full balanced multiplication and squaring cost
`O(n^(log₂ 3))`; clipped products have the same asymptotic upper bound and
must show a constant-factor win over full-product-then-slice in the
schoolbook/Karatsuba range before their production crossover is enabled.

### Cyclic and negacyclic products

The generic definitions fold an ordinary product modulo `x^n - 1` and
`x^n + 1`, respectively. A proof-taking API requires `0 < n`; checked forms
return `none` at `n = 0`. Their theorems identify the result with the
corresponding polynomial remainder and bound its size by `n`.

hex-poly-fp may compute these operations directly with an NTT plan. The
generic fold remains the reference and fallback, so the direct path needs no
new algebraic semantics.

## Reversal and truncated series

For a polynomial `f` and precision `n`, reversal reads the coefficient below
the leading end first and zero-extends to exactly `n` entries:

```lean
def reverseSeries (f : DensePoly R) (n : Nat) : TSeries R n

theorem coeff_reverseSeries (f : DensePoly R) (n i : Nat) (hi : i < n) :
    (reverseSeries f n).coeff i =
      if i < f.size then f.coeff (f.size - 1 - i) else 0
```

The theorem is accompanied by a range form that removes the conditional under
`i < f.size`.  The guard is essential: subtraction on `Nat` saturates at zero,
so the unguarded right-hand side would read the constant coefficient rather
than zero once `i` passes the leading end. `polyOfSeries` converts a fixed prefix back through
`DensePoly.ofCoeffs`; its coefficient theorem, not structural array equality,
is the bridge used by division proofs.

The plan-driven Newton step computes

```text
h' = h * (2 - g*h) mod x^k
```

at doubling precisions, using `MulPlan.slice 0 k`. `reciprocalWith` takes an
explicit inverse `u` of the constant coefficient. Under
`g.coeff 0 * u = 1`, its result converts to the same truncated series as
`TSeries.invOfUnit g u`. This library does not replace or redirect
`TSeries.invOfUnit`.

`seriesMulUpTo (karatsubaPlan 32)` is the dependency-safe generic Karatsuba
path for callers already above `hex-poly-fast`; its agreement theorem is exact
equality with `TSeries.mulUpTo`. The lower semiring-generic operation remains
schoolbook. Three cold outer trials on `chungus2` (AMD EPYC 9455), Lean
`4.34.0-rc2`, give:

| coefficients | coefficient type | `TSeries.mulUpTo` median | planned Karatsuba median |
|---:|:---|---:|---:|
| 4096 | `Int` | 102.388 ms | 1.040 s |
| 4096 | `Rat` | 1.810 s | 1.884 s |
| 8192 | `Rat` | 7.266 s | 6.961 s |

The rational win at 8192 is comparable to the observed trial spread, while
the integer plan loses decisively, so no implicit route changes. The complete
registered ladder extends through 16384 coefficients. Reproduce a cell with
`lake exe hexpolyfast_bench compare Hex.PolyFastBench.runSeriesSchoolbookRat Hex.PolyFastBench.runSeriesKaratsubaRat --param-floor 8192 --param-ceiling 8192 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1 --max-seconds-per-call 15`.

## Reusable fast division

A reciprocal is worth caching whenever a fixed modulus divides many values,
as in a remainder tree or quotient ring:

```lean
structure DivPlan (R : Type u) [DecidableEq R]
    [Lean.Grind.CommRing R] where
  divisor : DensePoly R
  capacity : Nat
  reciprocal : TSeries R capacity
  divisor_ne : divisor ≠ 0
  reciprocal_spec : ...

def DivPlan.ofMonic (mul : MulPlan R) (q : DensePoly R)
    (hq : Monic q) (hqne : q ≠ 0) (capacity : Nat) : DivPlan R

def DivPlan.ofNonzero [Lean.Grind.Field R] (mul : MulPlan R)
    (q : DensePoly R) (hq : q ≠ 0) (capacity : Nat) : DivPlan R
```

`DivPlan.divMod` takes evidence that the requested quotient length is within
`capacity`. Its quotient is the reversal of a low product with the cached
reciprocal; the remainder is `p - quotient * divisor`, computed with the
same multiplication plan. `DivPlan.mod` may omit materialization of a
quotient that the caller does not retain, but agrees with the second
component.

The one-shot API is total and preserves existing conventions:

```lean
def divModWith [Lean.Grind.Field R] (mul : MulPlan R)
    (p q : DensePoly R) : DensePoly R × DensePoly R

theorem divModWith_eq [Lean.Grind.Field R] (mul : MulPlan R) (p q) :
    divModWith mul p q = DensePoly.divMod p q
```

In particular, division by zero returns `(0, p)`, a divisor larger than the
dividend returns `(0, p)`, and a nonzero constant divisor returns zero
remainder. `divModMonicWith` supplies the analogous commutative-ring API.

The declared cost for quotient length `k` is `O(M(k))` after a reciprocal of
precision `k` is available and `O(M(k))` including construction, since the
doubling steps form a geometric series for every supported multiplication
plan.

The cached-divisor crossover is measured separately from one-shot reciprocal
construction. Three cold outer trials on `chungus2` (AMD EPYC 9455), Lean
`4.34.0-rc2`, give the following rational-polynomial medians for a dividend
with `2n + 1` coefficients and a divisor with `n + 1` coefficients:

| `n` | long division | cached Newton division |
|---:|---:|---:|
| 256 | 36.891 ms | 42.504 ms |
| 512 | 177.681 ms | 163.155 ms |
| 1024 | 881.427 ms | 648.437 ms |
| 2048 | 5.158 s | 2.875 s |

Thus an already-cached divisor crosses between 256 and 512 coefficients. For
eight dividends sharing one divisor, cached medians at `n = 128, 256, 512`
are 98.102 ms, 335.285 ms, and 1.303 s, versus 290.340 ms, 954.347 ms, and
3.451 s when rebuilding the reciprocal for every dividend. Reproduce the
boundary with `lake exe hexpolyfast_bench compare Hex.PolyFastBench.runLongDivision Hex.PolyFastBench.runCachedDivision --param-floor 256 --param-ceiling 1024 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1`.

## Half-gcd

The half-gcd implementation uses a dedicated four-polynomial transformation
record rather than depending on hex-matrix:

```lean
structure GcdStep (R : Type u) [DecidableEq R] where
  a00 : DensePoly R
  a01 : DensePoly R
  a10 : DensePoly R
  a11 : DensePoly R
```

Its invariant states that applying the transformation to the input pair gives
the current Euclidean pair and that the second component has crossed the
requested degree boundary. Recursive high-half calls use middle products;
the finishing steps use `divModWith`.

Expose `gcdWith`, `xgcdWith`, and `xgcdLeftWith`. Their acceptance theorem is
exact executable agreement with `DensePoly.gcd`, `DensePoly.xgcd`, and
`DensePoly.xgcdLeft`, including the returned scaling and Bezout coefficients.
Agreement merely up to multiplication by a unit is insufficient: existing
callers compare the raw gcd and transport the current `GcdLaws` theorems.

The implementation must therefore preserve the existing Euclidean quotient
sequence and input order. It may group steps into matrices but may not insert
monic normalization between them. Zero pairs, one zero input, reversed degree
order, and constant divisors are explicit base cases. The declared balanced
cost is `O(M(n) log n)`.

## Product trees and multipoint operations

`ProductTree` is an opaque balanced tree of nonempty levels. Its public
observations are its leaf sequence, root product, and the product represented
by each node. Construction accepts general polynomial leaves; a point plan
uses leaves `x - C point`.

`EvalPlan` stores the point sequence, its product tree, and the reciprocal
plans needed by the remainder tree. Reusing it for another polynomial does
not rebuild products or reciprocals:

```lean
def EvalPlan.build (mul : MulPlan R) (points : Array R) : EvalPlan R
def EvalPlan.eval (plan : EvalPlan R) (f : DensePoly R) : Array R

theorem EvalPlan.get_eval (plan : EvalPlan R) (f) (i) (hi : i < plan.size) :
    (plan.eval f)[i] = f.eval plan.points[i]
```

The cached remainder-tree path applies when `f.size <= plan.size`; this is the
finite capacity determined when the plan is built. `EvalPlan.eval` remains
total for larger inputs and uses direct pointwise evaluation in that case.
This fallback is necessary because the signature accepts polynomials of
unbounded size: no finite plan built from only the points can cache the
unbounded reciprocal precision required to reduce every such input at the
root. Evaluation works over a commutative ring because every divisor in the
point tree is monic. The empty point sequence produces an empty result.

Interpolation needs a field and distinct points. `InterpPlan.build?` returns
`none` exactly when duplicate points are present. It reuses the point product,
evaluates its derivative at the points, stores the inverse derivative values,
and combines the weighted leaves bottom-up. `InterpPlan.interpolate?` returns
`none` exactly on a value-count mismatch; an empty plan interpolates the empty
value array to zero.

Soundness states that the result has size at most the point count and evaluates
to every supplied value. Uniqueness states that any polynomial of smaller
degree with those values is equal to the result. Construction, bounded-size
evaluation, and interpolation cost `O(M(n) log n)`; the oversized
direct-evaluation fallback costs `O(plan.size * f.size)`. The reusable plan
cost is reported separately.

Three cold outer trials on `chungus2` (AMD EPYC 9455), Lean `4.34.0-rc2`,
give the following integer multipoint-evaluation medians for `n` coefficients
at `n` points:

| `n` | direct Horner | reused plan | cold plan |
|---:|---:|---:|---:|
| 256 | 7.378 ms | 30.602 ms | 73.527 ms |
| 512 | 35.154 ms | 141.703 ms | 316.823 ms |
| 1024 | 196.186 ms | 970.018 ms | 1.777 s |

Reusing the same plan for eight polynomials still loses at the measured
boundary: at `n = 256, 512`, direct Horner takes 58.137 ms and 273.181 ms,
versus 243.688 ms and 1.152 s for the remainder tree. There is therefore no
automatic multipoint-evaluation adoption for this integer workload. Reproduce
the one-polynomial table with `lake exe hexpolyfast_bench compare
Hex.PolyFastBench.runDirectEval Hex.PolyFastBench.runMultipointEval
Hex.PolyFastBench.runColdMultipointEval --param-floor 256 --param-ceiling 1024
--param-schedule doubling --cache-mode cold --outer-trials 3
--signal-floor-multiplier 1`.

For rational interpolation at distinct points, the corresponding medians are:

| `n` | direct Lagrange | reused plan | cold plan |
|---:|---:|---:|---:|
| 8 | 148.931 us | 35.533 us | 145.636 us |
| 16 | 1.186 ms | 162.831 us | 666.097 us |
| 32 | 12.880 ms | 1.104 ms | 3.381 ms |

The reused plan wins throughout these cells; including construction gives a
clear win from 16 points. The warm `n = 8` cell had a 188% trial spread, but
even its slowest trial remained below direct Lagrange. Reproduce the table
with `lake exe hexpolyfast_bench compare
Hex.PolyFastBench.runDirectInterpolation
Hex.PolyFastBench.runPlannedInterpolation
Hex.PolyFastBench.runColdInterpolation --param-floor 8 --param-ceiling 32
--param-schedule doubling --cache-mode cold --outer-trials 3
--signal-floor-multiplier 1`.

## Padé approximation

For a series prefix `s` and bounds `m`, `n`, a homogeneous approximant is a
nonzero pair `(p, q)` satisfying

```text
degree p <= m
degree q <= n
q*s - p = 0 mod x^(m+n+1).
```

The public result carries those degree, nontriviality, and congruence fields.
The homogeneous result is total over a field and is computed by the same
half-gcd engine applied to `x^(m+n+1)` and the polynomial represented by the
series prefix.

A rational formal-series approximant additionally needs `q.coeff 0 ≠ 0`.
`pade?` searches the terminal half-gcd candidates, normalizes a successful
denominator to constant coefficient `1`, and returns `none` exactly when no
approximant within the bounds has an invertible constant term. This distinction
is required: for some series and degree pairs a homogeneous approximant exists
but every admissible denominator has zero constant coefficient.

The declared cost is `O(M(m+n) log (m+n))` and the specification includes the
zero series, `m = 0`, `n = 0`, and precision zero.

The independent benchmark reference forms the classical normalized Hankel
system for diagonal `[n/n]` approximation, solves it by dense rational
Gauss-Jordan elimination, and agrees exactly with `pade?` on every common
rung from 1 through 128. Three cold outer trials on `chungus2` (AMD EPYC
9455), Lean `4.34.0-rc2`, give:

| `n` | linear-algebra reference | half-gcd Padé |
|---:|---:|---:|
| 32 | 7.908 ms | 20.954 ms |
| 64 | 83.094 ms | 109.469 ms |
| 128 | 981.178 ms | 571.852 ms |

The half-gcd path crosses between 64 and 128 for this rational-coefficient
family. Reproduce the boundary with `lake exe hexpolyfast_bench compare
Hex.PolyFastBench.runLinearPade Hex.PolyFastBench.runHalfGcdPade
--param-floor 32 --param-ceiling 128 --param-schedule doubling --cache-mode
cold --outer-trials 3 --signal-floor-multiplier 1
--max-seconds-per-call 15`.

## Integer multiplication: multipoint Kronecker

The existing `Hex.ZPoly.mulKronecker` and `mulKroneckerAt` remain compatible
and keep their agreement theorems. New named kernels implement:

- **KS2**, evaluation at `B` and `-B`, separating even and odd coefficients;
- **KS3**, evaluation at `B` and the reciprocal direction represented by
  reversing the coefficient blocks before packing;
- **KS4**, the combination, using four integer multiplications of roughly
  quarter-sized packed operands.

Here `B = 2^b`, and every variant derives `b` from runtime scans of the two
operands. Bounds use `maxAbs a * maxAbs b`, not the looser square of a shared
maximum, and include the number of terms contributing to a coefficient.
Signed coefficients use an explicit bias or symmetric digit recovery whose
no-overlap and no-borrow obligations are proved for every slot.

The two- and four-point variants trade more GMP multiplications for shorter
operands. No asymptotic winner is assumed. `ZPoly.mulFast` dispatches among
schoolbook, KS1, KS2, KS3, KS4, and CRT-NTT using a committed measured table
over shorter size, operand ratio, and coefficient widths. The existing simple
cutoff APIs remain available to reproduce the current benchmark.

Every kernel has a theorem equal to `DensePoly.mul`; the dispatcher theorem is
independent of the table contents.

## Word-modular NTT

The transform lives in hex-mod-arith because it is an operation on vectors of
`ZMod64`, not on polynomials. A reusable plan records:

```lean
structure ZMod64.NttPlan (p n : Nat) [ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] where
  length_pow_two : exists k, n = 2^k
  root : ZMod64 p
  root_order : ...                 -- exact order n
  invRoot : ZMod64 p
  invLength : ZMod64 p
  forwardTwiddles : Array ...
  inverseTwiddles : Array ...
```

The actual field layout may package powers and preconditioners together, but
the public observations above and the exact-order theorem are fixed.
`build?` validates the requested power-of-two length and returns `none` when
`n` does not divide `p - 1` or no supplied root witness checks. Fixed
auxiliary primes carry pre-built proofs and plans for every supported smaller
length.

Forward butterflies use representatives in `[0, 2p)` and inverse butterflies
use `[0, 4p)`, following Harvey's modified Shoup algorithms. These raw words
are internal bounded structures, not a second modular ring and not a public
`CommRing` instance. The existing `p < 2^31` bound implies `4p < 2^33`, so
all additions and subtractions fit comfortably in `UInt64`; Shoup products
use the existing high-word primitive. Normalization to `ZMod64` happens only
at transform boundaries.

Required theorems:

- each butterfly output has its advertised raw bound and canonical residue;
- forward transform equals the coefficientwise DFT;
- inverse after forward is the original vector;
- pointwise product between the transforms gives cyclic convolution;
- padding to `nextPowTwo (a.size + b.size - 1)` gives ordinary convolution;
- a primitive `2n`th root gives negacyclic convolution of length `n`.

No new `@[extern]` is part of this SPEC. The first implementation is Lean over
the existing verified word primitives. A native transform would require a
separate SPEC amendment naming its logical fallback, runtime contract, and
measured reason to cross the FFI boundary.

## CRT-NTT for arbitrary coefficients

hex-mod-arith owns a fixed catalogue of `NttPrime` packages: a prime modulus
below `2^31`, the maximum supported power-of-two transform length, and a root
of that exact order. The catalogue is finite and checked in the kernel; a
failed capacity or length request is normal control flow.

hex-modular adds balanced batch CRT beside incremental `Crt`/`CrtVec`. The
batch operation validates moduli greater than one and pairwise coprimality,
builds a product tree, combines residues bottom-up, and returns symmetric
representatives. Its agreement theorem is coefficientwise congruence to every
input modulus, and uniqueness uses the existing strict `symMod_unique` bound.

For operands of sizes `r`, `s`, put `k = min r s`.

- For `FpPoly p`, canonical lifts give the absolute coefficient bound
  `B = k * (p - 1)^2` before reduction modulo `p`.
- For `ZPoly`, if the operand bounds are `A` and `C`, use
  `B = k * A * C`.

Auxiliary primes are accumulated until their product `P` satisfies `2*B < P`.
The strict factor-two bound makes symmetric reconstruction equal to the true
integer coefficient in both cases. The finite-field path then reduces that
integer modulo `p`; the integer path returns it directly.

`FpPoly.mulNtt?` uses the target modulus directly when it has a suitable root.
`FpPoly.mulNttCrt?` and `ZPoly.mulNttCrt?` use the catalogue and return `none`
when its length or modulus product is insufficient. Their soundness theorem is
conditional only on returning `some`, not on an unchecked bound supplied by
the caller. `FpPoly.mulFast` falls back to `mulPacked` or Karatsuba;
`ZPoly.mulFast` falls back through the Kronecker dispatcher. Both public
operations are total and equal schoolbook multiplication.

## Complexity contracts

Let `M(n)` be the measured balanced multiplication cost of the selected plan.

| Operation | Required bound |
|---|---:|
| schoolbook full product | `O(n^2)` coefficient operations |
| Karatsuba full/square | `O(n^(log₂ 3))` |
| unbalanced `m x n`, `m >= n` | `O(ceil(m/n) * M(n))` |
| radix-2 NTT convolution | `O(n log n)` word operations |
| reciprocal and division | `O(M(n))` |
| half-gcd / extended gcd | `O(M(n) log n)` |
| product/remainder tree | `O(M(n) log n)` |
| one multipoint evaluation/interpolation | `O(M(n) log n)` |
| Padé approximation | `O(M(n) log n)` |

These are executable design constraints, not merely analysis. A recursive body
that repeatedly normalizes whole arrays, recomputes a reciprocal at every
remainder-tree node, pads an unbalanced product to the longer size, or rebuilds
an NTT root table inside each transform violates the SPEC even if it returns
the correct polynomial.

## Kernel exposure and trust

The logical closure consists of schoolbook polynomial operations, the
coefficientwise `TSeries` API, `Nat`/`Int` arithmetic, and the logical
`ZMod64` operations already specified by hex-mod-arith. Optimized loops use
ordinary definitions or proof-backed `@[csimp]` replacements where source and
target types are identical.

No theorem depends on a benchmark table or on the availability of a native
provider. No root, prime, CRT width, or duplicate-point fact is accepted as an
untrusted Boolean without a sound checker theorem. `native_decide` remains
banned.

## Conformance

The proof driver is `conformance/HexPolyFast/Conformance.lean`. The executable
JSONL driver is `conformance/HexPolyFast/EmitFixtures.lean`; `lake exe
hexpolyfast_emit_fixtures` emits the committed
`conformance-fixtures/HexPolyFast/polyfast.jsonl` fixture, which
`scripts/oracle/polyfast_flint.py` checks. The JSONL surface contains:

- `mul`, `square`, and `slice`, including the selected kernel name;
- `divmod`, `gcd`, `xgcd`, and `xgcd_left`;
- `cyclic` and `negacyclic`;
- `eval_many` and `interpolate`;
- `pade` with the homogeneous relation and normalized success/failure;
- NTT plan, round-trip, direct convolution, and CRT convolution cases;
- KS1/KS2/KS3/KS4 forced-kernel cases.

Small cases are checked independently by exact Python arithmetic. Integer and
prime-field whole results are also checked against FLINT through the existing
persistent oracle infrastructure.
The oracle never reports which kernel Hex should choose; dispatch is tested by
agreement plus benchmark evidence.

Mandatory edge families:

- both operands empty, one empty, constants, and normalized trailing zeros;
- odd split sizes and every Karatsuba cutoff boundary;
- operand ratios from balanced through at least 64:1;
- empty, one-coefficient, last-coefficient, and wholly out-of-range slices;
- positive and negative coefficients at every Kronecker digit bound;
- NTT lengths `1`, `2`, the largest catalogue length, and one beyond it;
- raw butterfly values at `0`, `p-1`, `p`, `2p-1`, and `4p-1` where valid;
- CRT modulus products immediately below and above `2*B`;
- zero divisor, constant divisor, larger divisor, and exact division;
- gcd inputs `(0,0)`, `(f,0)`, `(0,f)`, associates, and reversed degrees;
- empty point sets, duplicate interpolation points, and value-count mismatch;
- Padé cases with a unit denominator, only a nonunit homogeneous denominator,
  and no normalized result.

## Benchmarking and production dispatch

Per [benchmarking](../benchmarking.md), the bench driver is
`bench/HexPolyFast/Bench.lean`. It imports no Mathlib. Every dispatch family
records both time and allocation counts and includes cells immediately below,
at, and above the proposed crossover.

Required families:

- schoolbook, Karatsuba, square, and clipped products over `Int`, `Rat`, and
  small `ZMod64` fields, with degrees from 4 through at least 16384;
- balanced and unbalanced shapes, with ratios 1, 2, 4, 16, and 64;
- KS1/KS2/KS3/KS4 over the current degree/coefficient-width grid, extended
  into the GMP Karatsuba, Toom, and FFT regimes;
- direct NTT, CRT-NTT, packed Fp multiplication, and generic Karatsuba across
  modulus and transform-length ladders;
- cold plan construction, warm plan reuse, and repeated fixed-modulus calls;
- Newton division against long division, with and without a cached divisor;
- Euclidean gcd/xgcd against half-gcd;
- Horner against product/remainder-tree evaluation for one and repeated
  polynomials;
- direct Lagrange interpolation against the reusable interpolation plan;
- linear-algebra reference Padé against half-gcd Padé on small shared cases.

FLINT `fmpz_poly` and `nmod_poly` are informational external comparators. The
gating comparisons are within Lean: no production cell selected by a committed
dispatch table may lose to the retained implementation outside the uncertainty
band defined by the benchmark protocol. Each table records the host, toolchain,
sample count, and script that regenerates it.

The downstream audit covers at least:

- `HexHensel.QuadraticMultifactor` product trees and lift products;
- Fp square-free decomposition and the Berlekamp irreducibility gcd chain;
- `FpPoly.composeModMonic`, Frobenius, and GFq reduction/power paths;
- Berlekamp-Zassenhaus trial products and integer reassembly;
- repeated modulus division in finite-field and quotient-ring consumers.

A call site changes only when its representative end-to-end benchmark wins.
A measured loss keeps the old path and is a completed audit result, not a
reason to move the global crossover until unrelated cells regress.

## The Mathlib layer

There is no `hex-poly-fast-mathlib`. Each optimized multiplication and
division theorem lands on an existing `DensePoly` operation, and
hex-poly-mathlib already transports those operations to `Polynomial`.
Likewise, evaluation and interpolation soundness are stated directly with
`DensePoly.eval`; a later Mathlib-facing consumer can rewrite through the
existing equivalence.

If a future theorem needs Mathlib's asymptotic framework, it belongs in that
consumer or in a documentation proof, not in the computational dependency
graph. The executable complexity contracts here are enforced by body shape
and benchmarks.

## Milestones

1. **Prerequisites.** Finish hex-truncated-series through Newton inversion and
   hex-modular through scalar/vector and balanced batch CRT. Add measured
   Karatsuba `mulUpTo` to hex-truncated-series without changing its dependency.
2. **Generic multiplication.** `MulPlan`, schoolbook, Karatsuba, specialized
   square, unbalanced blocking, arbitrary slices, cyclic/negacyclic references,
   and all agreement theorems.
3. **Newton division.** Reversal/series bridges, `reciprocalWith`, `DivPlan`,
   monic and field division, cached remainders, and exact agreement.
4. **Half-gcd.** The transformation invariant, fast gcd, full and one-sided
   extended gcd, exact agreement, and the degree/complexity benchmarks.
5. **Multipoint Kronecker.** KS2, KS3, KS4, signed bounds and recovery,
   compatibility with current APIs, and the measured integer dispatcher.
6. **NTT.** Plan validation, redundant forward/inverse butterflies, transform
   correctness, direct Fp convolution, and cyclic/negacyclic adapters.
7. **CRT-NTT.** Balanced batch CRT, the fixed prime catalogue, strict recovery
   bounds, arbitrary-Fp and integer paths, and total fallback dispatchers.
8. **Trees and Padé.** Product/remainder trees, reusable evaluation and
   interpolation plans, homogeneous and normalized Padé, and their complete
   conformance/benchmark families.
9. **Adoption.** Audit the named consumers, switch only winning cells, update
   their owning SPECs and benchmarks, and keep the single-job CI topology.

No later milestone may be used to excuse a quadratic placeholder in an earlier
one. In particular, milestone 3 implements Newton division with clipped
products, and milestone 4 implements an actual half-gcd recursion rather than
renaming the Euclidean loop.

## File organisation

```text
HexPolyFast/
  Plan.lean          -- MulPlan, schoolbookPlan, agreement projections
  Karatsuba.lean     -- full, square, unbalanced, and clipped recursion
  Cyclic.lean        -- cyclic and negacyclic reference operations
  Reverse.lean       -- DensePoly/TSeries bridges
  Reciprocal.lean    -- plan-driven Newton inverse
  Division.lean      -- DivPlan and one-shot division
  HalfGcd.lean       -- GcdStep, gcd, xgcd, xgcdLeft
  ProductTree.lean   -- balanced product/remainder trees
  Multipoint.lean    -- EvalPlan and InterpPlan
  Pade.lean          -- homogeneous and normalized approximants
HexPolyFast.lean
```

The coefficient-owner file layouts gain:

```text
HexModArith/Ntt/{Plan,Butterfly,Transform,Catalogue}.lean
HexModular/BatchCrt.lean
HexPolyFp/NttMul.lean
HexPolyZ/KroneckerMulti.lean
HexPolyZ/NttMul.lean
```

`libraries.yml` eventually gains, after its dependencies are active:

```yaml
  HexPolyFast:
    deps: [HexPoly, HexTruncatedSeries]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: FLINT fmpz_poly and nmod_poly via python-flint
          class: informational
          rationale: "FLINT has independently tuned coefficient-specific dispatch; within-Lean agreement and crossover cells gate production selection."
      input_families:
        - name: full-and-clipped-multiplication
          description: Balanced and unbalanced full, square, low, and middle products across crossover sizes.
        - name: newton-division
          description: One-shot and cached-divisor division against long division.
        - name: half-gcd
          description: Gcd, full xgcd, and one-sided xgcd across balanced and skewed degree pairs.
        - name: multipoint
          description: Cold and reused product/remainder trees for evaluation and interpolation.
        - name: pade
          description: Homogeneous and normalized Padé cases, including normalized failure.
        - name: coefficient-kernels
          description: Forced Kronecker and direct/CRT-NTT paths across degree, width, and modulus ladders.
```

hex-poly-fp and hex-poly-z then add `HexPolyFast` and `HexModular`; hex-poly-z
also adds `HexModArith`. The release manifest is updated only when those
implementation changes actually land, never by this SPEC-only change.

## References

- David Harvey, [*Faster polynomial multiplication via multipoint Kronecker
  substitution*](https://arxiv.org/abs/0712.4046), Journal of Symbolic
  Computation 44 (2009), 1502-1510. This is the basis for KS2, KS3, and KS4.
- David Harvey, [*Faster arithmetic for number-theoretic
  transforms*](https://arxiv.org/abs/1205.2926), Journal of Symbolic
  Computation 60 (2014), 113-119. This is the basis for the redundant Shoup
  butterflies.
- David Harvey, [*The Karatsuba integer middle
  product*](https://doi.org/10.1016/j.jsc.2012.02.001), Journal of Symbolic
  Computation 47 (2012), 954-967. This SPEC uses the polynomial
  middle-product construction that the integer algorithm adapts; it does not
  add a limb-level integer primitive.
