# hex-poly (dense polynomial library, no dependencies)

The dense polynomial library.

**Dense representation:**
```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

The normalization invariant removes trailing stored zeros. For canonical
coefficients, structural polynomial equality agrees with coefficientwise
mathematical equality. For noncanonical representations with a zero-reflecting
interpretation, it preserves semantic degree, but distinct nonzero stored
polynomials may have the same interpretation. Every operation maintains the
storage invariant; semantic identities then test zero coefficient differences.

The polynomial literal `#p[a₀, a₁, ...]` abbreviates
`DensePoly.ofCoeffs #[a₀, a₁, ...]`. Coefficients are listed in ascending
degree order, and the expected polynomial type determines the coefficient
type. As with `ofCoeffs`, trailing zero coefficients are removed. A polynomial prints, through its `Repr` instance, as that same literal,
so a printed value can be pasted back.

- Index = degree, `coeffs[i]` is coefficient of `x^i`
- Normalization invariant: no trailing zeros
- Structural equality is semantic equality for canonical coefficients;
  noncanonical interpretations use zero differences
- O(1) degree, O(1) coefficient access

**Degree.** `degree?` returns `none` for the zero polynomial and otherwise the
index of the leading coefficient. `natDegree` is `degree?` with the zero case
defaulted to `0`, matching Mathlib's `Polynomial.natDegree`, and is the form
every caller should use unless it must distinguish the zero polynomial:

```lean
namespace Hex.DensePoly

abbrev natDegree (p : DensePoly R) : Nat := p.degree?.getD 0

theorem natDegree_eq_degree?_getD (p : DensePoly R) :
    p.natDegree = p.degree?.getD 0
theorem natDegree_eq_size_sub_one (p : DensePoly R) :
    p.natDegree = p.size - 1
@[simp] theorem natDegree_zero : (0 : DensePoly R).natDegree = 0

end Hex.DensePoly
```

It is a reducible abbreviation rather than a definition so that statements
phrased either way stay definitionally equal, which keeps the `degree?` lemmas
usable without a transport step. `hex-sparse-poly`, `hex-gf2` and
`hex-number-field` carry the same `natDegree` over their own degree functions.

**Operations:**
- Addition, negation, subtraction, multiplication. `mul` is the schoolbook
  convolution and is the specification at every coefficient type; the
  subquadratic kernel is coefficient-specific and therefore lives
  downstream (`Hex.ZPoly.mulKronecker` in `hex-poly-z`). The planned
  [hex-poly-fast](../../HexPolyFast/SPEC/hex-poly-fast.md) adds explicit lawful
  multiplication plans, Karatsuba, clipped products, fast division, and
  half-gcd without changing this operation or its instance. A
  type-preserving `@[csimp]` swap of `mul` itself is not available: every
  subquadratic scheme needs subtraction (Karatsuba) or an integer
  encoding (Kronecker), and `mul` is defined over `[Add R] [Mul R]`
  alone. This is the same constraint that keeps `mulStrassen` a separate
  entry point in `hex-matrix`.
- Horner evaluation is multiplicative over a commutative ring
  (`eval_mul_commring`), which is what licenses the Kronecker
  substitution downstream.
- Coefficient scaling, with public composition, addition, and multiplication
  transport laws (`scale_scale`, `scale_add`, `scale_mul`, `mul_scale`)
- Division with remainder (for monic divisors; general division over fields)
- Polynomial GCD (plain Euclidean remainder sequence, **not** the extended
  algorithm). `gcd` tracks only the remainders, so it is `O(deg²)`. The extended
  algorithm additionally multiplies the divisor against the growing Bezout
  accumulators `s`, `t` at every step (`q*s₁`, `q*t₁`), which is `O(deg³)` and
  unnecessary when only the gcd *value* is needed. The common case is the
  square-free / separability test `gcd(f, f') = 1`. Computing Bezout coefficients
  inside `gcd` is a correctness-neutral but ~10⁴× performance defect on the BHKS
  prime-selection hot path, so `gcd` must be the plain remainder sequence.
- Extended GCD (`xgcd`, Bezout coefficients: `a*f + b*g = gcd(f,g)`), a
  *separate* function for the genuine Bezout use-sites (CRT, Hensel, Berlekamp
  correctness). `gcd` agrees with `xgcd`'s gcd component (`gcd_eq_xgcd_gcd`), so
  the gcd-value lemmas transfer.
- One-sided extended GCD (`xgcdLeft`, gcd plus the coefficient of the left
  input) for inverse computations that need only one Bezout coefficient. It
  skips the second growing polynomial multiplication at every Euclidean step.
- Monic one-sided extended GCD (`xgcdLeftMonic`) for field inverse computations
  whose cofactor is needed only up to a nonzero scalar. It rescales each
  nonzero remainder and its tracked coefficient before division, preventing
  avoidable coefficient swell while preserving the Bezout relation up to the
  returned gcd representative. `xgcdLeft` remains the exact-cofactor API.
- Evaluation (Horner's method)
- Composition, derivative
- Content and primitive part (for `DensePoly Int`)

**Lightweight field and ring surface.** The umbrella also exports the
Mathlib-free `Lean.Grind` semiring/ring instances for `DensePoly`, using binary
exponentiation for natural powers. Over every lightweight field it exports
lawful division, remainder, gcd, and extended-gcd instances, plus the canonical
`monicize` operation and its size, divisibility, idempotence, and nonzero laws.
These declarations use no `HexBasic` or Mathlib dependency; coefficient-ring
exact-division instances remain in their owning downstream libraries.

**Polynomial GCD, key properties:**
- `gcd f g` divides both `f` and `g`
- Every common divisor of `f` and `g` divides `gcd f g`
- Bezout: `∃ a b, a * f + b * g = gcd f g`

**Coprimality over a lightweight field.** `HexPoly.Coprime` exports
`DensePoly.Coprime p q := ∃ s t, s*p + t*q = 1` and `coprime_iff`, identifying
this witness condition with `monicize (gcd p q) = 1`. The monic associate is
essential: the Euclidean algorithm need not choose a monic gcd.
The interface includes symmetry, descent along divisibility, the coprime
divisibility lemma, stability under products and powers, and rescaling by a
nonzero field element. `coprime_cofactors` proves coprimality after exact
division by the monic gcd. These are proof-only APIs; they do not change
polynomial arithmetic or install a new coefficient instance.

Supporting field lemmas cover monicity of one and powers, monicity of exact
cofactors, nonzero leading coefficients, polynomial cancellation and nonzero
products, divisibility transitivity, and scaling as multiplication by a constant.
Names such as `DensePoly.mul_ne_zero` refer to polynomial multiplication;
Mathlib-facing proofs about scalar products can qualify `_root_.mul_ne_zero`.

**Existential CRT for polynomials** (corollary of Bezout):

```lean
def polyCRT [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R) : DensePoly R :=
  u * t * b + v * s * a

theorem polyCRT_mod_fst [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % a = u % a

theorem polyCRT_mod_snd [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % b = v % b
```

Given coprime `a, b` with Bezout coefficients `s, t`, constructs `h`
with `h ≡ u (mod a)` and `h ≡ v (mod b)`. Used by hex-hensel,
hex-gfq-ring, and hex-berlekamp-mathlib (Berlekamp correctness proof).

## Ordered-domain pseudo-division

The [ordered-field Sturm contract](../../SPEC/Libraries/hex-sturm.md) uses
ordinary `DensePoly D` over a nontrivial ordered commutative domain with
executable equality. Preserve the existing total polynomial operations and
field algorithms. For representation coefficients follow the family
[execution contract](../../SPEC/real-closure-execution.md): structural equality
and canonical zero permit the same `DensePoly` storage and kernels, without
field instances on raw syntax. Correctness uses an operation-preserving
interpretation which reflects zero; semantic identities test zero differences.

The additional arithmetic needed by signed remainder chains is total
pseudo-division, with no field division. Use ordinary operation instances and `DecidableEq D` for the usual
leading-coefficient cancellation algorithm. Its reconstruction and degree
laws require domain laws, or an operation-preserving, zero-reflecting
interpretation for noncanonical representation coefficients. Order is needed
only to choose the positive scale required by a signed chain. These are
ordinary typeclass operations and mathematical hypotheses, not a new
coefficient-operation record or a resource-budget interface.

For nonzero `B`, return `u,Q,R` satisfying

```text
u ≠ 0,   u*A = Q*B + R,
R = 0 or R.natDegree < B.natDegree.
```

With ordered-domain hypotheses the signed-chain variant chooses `u>0`.
For example, ordinary pseudo-division gives `u=lc(B)^k`; if it is negative,
negate `u,Q,R` together. A consumer forms the next signed remainder from
`-R`; it must not independently force every remainder to be positive-leading.
Zero divisor handling follows the existing division convention (unchanged
input as remainder), with reconstruction/degree theorems explicitly requiring
`B ≠ 0`. Zero dividends and dividends below the divisor degree need no
cancellation and use `u=1,Q=0,R=A`.

Termination follows from strict decrease of the nonzero remainder degree,
or from a computed bound of at most `A.natDegree-B.natDegree+1` cancellations
when `A≠0` and `deg B≤deg A`. A fuel-based implementation must prove its
internally computed bound suffices; it has no caller threshold or partial
result. `DensePoly.degree?` already distinguishes zero from nonzero constants.
There is no second raw polynomial representation or semantic-degree API.

Plain pseudo-gcd iterates pseudo-remainders without Bézout accumulators.
Its result is a gcd up to a nonzero scalar **over the fraction field of D**,
not necessarily a gcd in `D[X]`. If a consumer needs pseudo-xgcd, record
`S*A+T*B=c*G` with `c≠0`; do not assert an unscaled Bézout identity over the
coefficient domain. For instance `2*S+X*T=1` is impossible over `ℤ[X]`.
For `(0,0)` choose `G=S=T=0,c=1`; with one zero input return the other up to
its recorded nonzero scale. Add pseudo-xgcd only for a concrete use-site;
field inversion already has the existing `xgcd`/`xgcdLeft` APIs.

Field consumers reuse `divMod`, `gcd`, `xgcd`, `xgcdLeft` and `monicize`.
The current gcd is not assumed monic. Normalizing a gcd explicitly must
rescale any associated Bézout coefficients. Optimized integer content or
subresultant normalization belongs with its backend and proves the relevant
positive-scaling identities; it does not make all arithmetic return evidence.

Prove reconstruction, degree decrease, zero cases, divisibility and field
agreement as ordinary correctness theorems. Also provide companion transfer
lemmas for operation-preserving, zero-reflecting representation maps; unlike
the existing canonical polynomial equivalence, these maps need not be injective. The Mathlib companion relates
these to `Polynomial` and fraction-field arithmetic. Query certificates live
with the query owner, not on individual coefficient additions/multiplications.
No `Hex.PolyOps`, fallible arithmetic callbacks, shared limits/budgets or
per-operation certificates are part of this library.

Conformance covers negative leading coefficients, zero and constant inputs,
exact divisions, `(2,X)` over integers, repeated factors, reconstruction and
strict remainder degree. Compare the field specialization with existing
field division and gcd up to the recorded scale. Benchmark pseudo-division,
plain gcd and any required extended variant separately, recording coefficient
growth and verifying that plain gcd does not compute Bézout accumulators.

## Noninjective polynomial correspondence

Generic operation-only transfer lemmas belong here; Mathlib `Polynomial`
interpretation belongs in hex-poly-mathlib. For `eval : E → K`, assume zero
reflection and preservation of each scalar operation used by a kernel,
including natural casts where derivatives/powers need them. Do not assume
`eval` injective or ring/field laws on `E`. Prove coefficientwise interpretation
commutes with the actual division/gcd/xgcd algorithms, their size-derived
bounds, derivative, Horner evaluation and required pseudo-remainders. Compose
with the existing lawful-target theorems. Gcd results are up to a nonzero
scalar unless explicitly normalized, and monicization means leading value
one, not necessarily literal leading representative one.

Keep structural equality for array/context identity. Scalar and polynomial
semantic identities are checked by zero differences. No family implementation
or semantic-quotient construction becomes an import of hex-poly. In particular,
selected-root zero testing, storage retention and context refinement stay with
the extension owner.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_poly` via python-flint | informational | all `setup_benchmark` registrations against integer polynomial inputs |

FLINT's `fmpz_poly` is the standard reference for univariate
integer polynomial arithmetic. The comparator is `informational`
rather than `gating`: FLINT tunes Karatsuba/Toom-Cook/FFT
crossovers in `fmpz_poly_mul` and uses Newton-style algorithms for
division and GCD; this library deliberately supplies only the schoolbook
semantic foundation. The coefficient-specific and composed algorithms are
specified downstream in hex-poly-z and hex-poly-fast. The ratio is recorded
for orientation rather than as an
acceptance threshold. It is measured through a persistent Python process per
`SPEC/benchmarking.md §"External comparators" §"Process call"`.
