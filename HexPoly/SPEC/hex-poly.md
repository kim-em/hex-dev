# hex-poly (dense polynomial library, no dependencies)

The dense polynomial library.

**Dense representation:**
```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

The normalization invariant (no trailing zeros) ensures structural equality
= semantic equality. Every operation maintains this invariant.

The polynomial literal `#p[a₀, a₁, ...]` abbreviates
`DensePoly.ofCoeffs #[a₀, a₁, ...]`. Coefficients are listed in ascending
degree order, and the expected polynomial type determines the coefficient
type. As with `ofCoeffs`, trailing zero coefficients are removed. A polynomial prints, through its `Repr` instance, as that same literal,
so a printed value can be pasted back.

- Index = degree, `coeffs[i]` is coefficient of `x^i`
- Normalization invariant: no trailing zeros
- Structural equality = semantic equality
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
  [hex-poly-fast](../../SPEC/Libraries/hex-poly-fast.md) adds explicit lawful
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

## Fallible coefficient operations

The [ordered-field Sturm contract](../../SPEC/Libraries/hex-sturm.md) requires
new reusable polynomial routines below the real-closure family. This section
is planned infrastructure, not a description of capabilities already provided
by `HexPoly.Field`. Preserve the current total `DensePoly` APIs.

Use an explicit operation record, not new instances on raw representatives.
The following signatures are design shapes; `Result` distinguishes success,
invalid input, exhaustion and rejected evidence, and successful calls return
the residual budget. `C` is a representation type with a fixed context.

```text
CoeffOps C:
  zero, one : C
  validate : Budget → C → Result ValidityEvidence
  add, mul : Budget → C → C → Result (C × ArithmeticEvidence)
  neg      : Budget → C → Result (C × ArithmeticEvidence)
  zeroTest : Budget → C → Result (Bool × ZeroEvidence)
  sign     : Budget → C → Result (Sign × SignEvidence)
  checkArithmetic, checkZero, checkSign : Budget → Claim → Evidence → CheckResult
FieldOps C extends CoeffOps C:
  inv      : Budget → C → Result (C × InverseEvidence)
```

`Sign` has exactly negative, zero and positive values. Claims include the
context, operation and all operands/results; evidence cannot be reused for
another claim. Each checker is structurally terminating and kernel-reducible;
`CheckResult` distinguishes accepted, rejected and exhausted. Sign can supply
a zero decision, but an independent zero test must agree with it whenever
both succeed. Unknown is exhaustion, never zero or false. Equality is the
zero test of a difference; no structural `DecidableEq C` is required.
All callbacks, including arithmetic and validation, must terminate on invalid
inputs. Check allocation/work limits before allocating or invoking children,
and charge nested work to the parent budget without resetting it.

A separate Prop law package supplies a validity predicate and an
interpretation of valid representatives in a nontrivial ordered commutative
domain `D`, preservation of validity, ring-operation correspondence, and
soundness of accepted arithmetic/zero/sign evidence. It need not make the
interpretation injective or impose algebraic instances on `C`. Core
`Lean.Grind.CommRing`, `LE`, `LT`, `Std.IsLinearOrder`,
`Std.LawfulOrderLT`, and `Lean.Grind.OrderedRing` on the semantic carrier,
with the domain laws, suffice; alternatively package these laws explicitly.
No semantic decision procedure is needed to state successful-result
soundness. `FieldOps` adds a field interpretation and the inverse law for
certified nonzero inputs. Certified zero inversion is invalid, and an
undecided zero test propagates exhaustion.

Raw polynomial storage is an array of `C`, separate from `DensePoly C`.
`degreeWith` scans at most the stored length and returns `none` precisely
when every coefficient is semantically zero, or `some d` with a nonzero
coefficient at `d` and zero evidence above it. These are success values;
failure is carried by the outer result. All arithmetic, leading-coefficient
selection, remainder and stopping tests use this semantic degree. Trailing
structural nonzeros may denote zero. Polynomial identities use bounded
coefficientwise semantic equality, with corresponding evidence in replay.

Required routines and postconditions, interpreted coefficientwise, are:

| Routine | Successful result |
| --- | --- |
| `pseudoDivWith A B` | For `B ≠ 0`, return `u,Q,R` with `u>0`, `u*A=Q*B+R`, and `R=0` or `degree R < degree B`. |
| `pseudoGcdWith A B` | Return the last nonzero pseudo-remainder, a gcd representative **over the fraction field of D**, with the reduction identities; return zero on `(0,0)`. |
| `pseudoXgcdWith A B` | Additionally return `S,T,c` with `c ≠ 0` and `S*A+T*B=c*G`, where `G` has the fraction-field gcd property. Track scale changes explicitly. |
| `divModWith A B` | With `FieldOps` and `B ≠ 0`, return `Q,R` with `A=Q*B+R` and the same remainder bound. |
| `gcdWith A B` | With `FieldOps`, return a monic gcd (zero on `(0,0)`), dividing both inputs and divisible by every common divisor. |
| `xgcdWith A B` | With `FieldOps`, return `G,S,T` with the same monic gcd and `S*A+T*B=G`; choose all zero on `(0,0)`. |

The fraction-field assertion means that after the canonical embedding into
any fraction field, `G` divides both inputs and every common divisor divides
`G`. It does **not** assert a gcd or an unscaled Bézout identity in `D[x]`:
for example the fraction-field gcd of `2` and `x` is a unit, but
`2*S+x*T=1` is impossible in `ℤ[x]`. No fraction-field arithmetic or
`Field Int` instance is required at runtime. With one zero input the pseudo
gcd is the other input up to its recorded nonzero scale; for `(0,0)` the
pseudo-xgcd chooses `S=T=G=0,c=1`.

Pseudo-division uses positive leading-coefficient multipliers, for example
`abs(lc B)`, and tracks the quotient. For constant nonzero `B` it must still
produce the reconstruction identity, not merely return a zero remainder.
Zero `B` is invalid even when `A=0`; adapters check this before invoking the
existing total `DensePoly.divMod` convention. For nonzero `A,B` the bound is
`max(0, degree A - degree B + 1)` leading cancellations; zero `A` needs none.
Each cancellation checks strict semantic degree descent. A gcd loop swaps
inputs as needed and decreases the nonzero remainder degree; stored lengths
give conservative outer fuel even before normalization. At fuel zero check
for genuine termination or return exhaustion; never return a partial gcd.
The xgcd loop maintains the displayed linear-combination identities at each
step. Plain gcd must not compute growing Bézout accumulators.

Prove degree/reconstruction, gcd divisibility over the stated field,
Bézout, checker soundness, and success under complete callbacks with sufficient
fuel as distinct obligations. For a total lawful field carrier,
`DensePoly.divMod`, `gcd`, `xgcd` and `xgcdLeftMonic` in
[`Field.lean`](../Field.lean) are fast adapters. Prove field division equality
and gcd/xgcd agreement after the same monic normalization; Bézout coefficients
need not be equal for two valid extended-gcd algorithms. Exact-output equality
is required when the optimized adapter claims to implement the same chosen
algorithm. The current gcd need not be monic. Integer-specialized content
removal stays in its owning downstream backend and must supply its scale
identity; hex-poly gains no dependency on hex-real-roots or the family.

Conformance includes semantically zero trailing coefficients, constant and
zero divisors, gcd/xgcd zero cases, negative leading coefficients, the
`(2,x)` domain-versus-fraction-field distinction, failed coefficient decisions,
exhaustion and malformed scale/evidence data. Phase 4 separates remainder,
plain gcd, extended gcd, semantic-degree/sign work and evidence production;
record coefficient growth and verify the total adapter against existing
DensePoly routines under the shared benchmarking policy.

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
