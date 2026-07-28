/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBerlekampMathlib
import HexBerlekampZassenhausMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "`factor_poly` and `irreducibility`: certified factoring" =>
%%%
tag := "factor-tactics"
%%%

# Introduction
%%%
tag := "factor-tactics-intro"
%%%

The `factor_poly` and `irreducibility` tactics can be used to factorize a
specific polynomial, or prove that it is irreducible.

The tactics accept four input types, and become increasingly capable
as further libraries are imported.

Once `HexBerlekampZassenhausMathlib` is imported, the tactics
handle `Polynomial ℤ`, `Polynomial (ZMod q)`,
{name}`Hex.ZPoly` (dense integer polynomials),
and {name}`Hex.FpPoly` (dense polynomials over a prime field).

If you don't need all these capabilities (or want to avoid the extra dependencies),
`import HexBerlekampMathlib` suffices for `Polynomial (ZMod q)` and {name}`Hex.FpPoly`,
`import HexBerlekampZassenhaus` suffices for {name}`Hex.ZPoly`,
and `import HexBerlekamp` suffices for {name}`Hex.FpPoly` alone.

# Proving irreducibility
%%%
tag := "factor-tactics-irreducibility"
%%%

The bare tactic form closes an `Irreducible` goal. Here it proves
that `x² − 2` does not factor over `ℤ`, the algebraic core of the
irrationality of `√2`, in its Mathlib form over `Polynomial ℤ`:

```lean
open Polynomial

example : Irreducible (X ^ 2 - 2 : Polynomial ℤ) := by
  irreducibility
```

`irreducibility` can also be used as a term elaborator:

```lean
open Polynomial

theorem sqrt2_irred :
    Irreducible (X ^ 2 - 2 : Polynomial ℤ) :=
  irreducibility (X ^ 2 - 2 : Polynomial ℤ)
```

When the current goal is something else, `irreducibility f` adds the
corresponding theorem as `this`; the form `irreducibility h : f` gives it an
explicit name:

```lean
open Polynomial

example :
    Irreducible (X ^ 2 - 2 : Polynomial ℤ) ∧
      Irreducible (X ^ 2 + X + 1 : Polynomial ℤ) := by
  irreducibility (X ^ 2 - 2 : Polynomial ℤ)
  irreducibility h : (X ^ 2 + X + 1 : Polynomial ℤ)
  exact ⟨this, h⟩
```

Behind the call, the input expression is parsed to an executable
integer polynomial together with a proof that the parse is faithful,
and a compiled witness search finds a certificate: for `x² − 2` the
reduction mod `3` is irreducible, a single-prime modular witness,
which is reified into the proof term for the kernel to check. The
factorizer itself only runs when no witness exists, to report whether
the input is actually reducible or merely uncertifiable.

# Factoring: `factor_poly`
%%%
tag := "factor-tactics-factor-poly"
%%%

When the polynomial is not irreducible, `factor_poly f` produces the
whole certified factorization at once. For a `Polynomial ℤ` input the
result is a {name}`Hex.FactoredPoly`: a scalar, the list of
irreducible factors with multiplicity, and the two theorems that make
those fields a genuine factorization.

{docstring Hex.FactoredPoly}

```lean
open Polynomial

noncomputable def facSplit :=
  factor_poly ((X ^ 2 - 1) * (X + 2) : Polynomial ℤ)

example : facSplit.factors.length = 3 := rfl
example : facSplit.scalar = 1 := rfl
```

The reconstruction and irreducibility fields can be consumed directly:

```lean
open Polynomial

example :
    Polynomial.C facSplit.scalar * facSplit.factors.prod =
    ((X ^ 2 - 1) * (X + 2) : Polynomial ℤ) :=
  facSplit.factors_mul

example : ∀ q ∈ facSplit.factors, Irreducible q :=
  facSplit.factors_irred
```

`factor_poly` can also be invoked as a tactic. It introduces `scalar` and
`factors` as transparent `let` bindings, followed by the reconstruction
hypothesis `factors_mul` and the irreducibility hypothesis `factors_irred`:

```lean
open Polynomial

example :
    ∃ (scalar : ℤ) (factors : List (Polynomial ℤ)),
      Polynomial.C scalar * factors.prod =
          ((X ^ 2 - 1) * (X + 2) : Polynomial ℤ) ∧
        ∀ q ∈ factors, Irreducible q := by
  factor_poly ((X ^ 2 - 1) * (X + 2) : Polynomial ℤ)
  exact ⟨scalar, factors, factors_mul, factors_irred⟩
```

If you need to name these fields, it is best to use the term elaborator with `obtain`, e.g., as:

```lean
open Polynomial

example :
    ∃ (content : ℤ) (factors : List (Polynomial ℤ)),
      Polynomial.C content * factors.prod =
          ((X ^ 2 - 1) * (X + 2) : Polynomial ℤ) ∧
        ∀ q ∈ factors, Irreducible q := by
  obtain ⟨content, factors, hproduct, hirreducible⟩ :=
    factor_poly ((X ^ 2 - 1) * (X + 2) : Polynomial ℤ)
  exact ⟨content, factors, hproduct, hirreducible⟩
```

# The executable types
%%%
tag := "factor-tactics-executable"
%%%

The Mathlib-facing forms above are transports of the same machinery
working on the executable types. Over a prime field the input is a {name}`Hex.FpPoly`
(see the {ref "hex-poly-fp"}[HexPolyFp chapter]) and the result is an
{name}`Hex.FpPoly.Factored`:

{docstring Hex.FpPoly.Factored}

The literal `#p[a₀, a₁, ...]` lists polynomial coefficients in ascending
degree order.

The example below factors `3 * (x+1)² * (x²+2)` over `F₅`: non-monic
and non-square-free, so the scalar, multiplicity, and normalization
conventions are all visible. The factors come back monic, in
nondecreasing degree order, repeated to multiplicity, with the leading
unit in `scalar`:

```lean
open Hex

instance : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

/-- `3 · (x+1)² · (x²+2)` over `F₅`: non-monic and
non-square-free. -/
def testF : FpPoly 5 :=
  .C 3 * #p[1, 1] * #p[1, 1] * #p[2, 0, 1]

noncomputable def facF := factor_poly testF

example : facF.factors.length = 3 := rfl
example : facF.scalar = 3 := rfl

def irrF : FpPoly 5 := #p[2, 0, 1]

theorem irrF_irred : FpPoly.Irreducible irrF :=
  irreducibility irrF
```

Over the integers the input is a {name}`Hex.ZPoly` (see the
{ref "hex-poly-z"}[HexPolyZ chapter]) and the result is a
{name}`Hex.ZPoly.Factored`, with the signed content in `scalar` and
primitive positive-leading-coefficient factors:

{docstring Hex.ZPoly.Factored}

```lean
open Hex

def quadZ : ZPoly := #p[1, 0, 1]

theorem quadZ_irred : ZPoly.Irreducible quadZ :=
  irreducibility quadZ
```

Irreducibility of a `ZPoly` is stated with the Mathlib-free class
{name}`Hex.ZPoly.Irreducible`, which the correspondence library proves
equivalent to Mathlib's `Irreducible` under `toPolynomial`. Goal-mode
`irreducibility` closes all three spellings: `Hex.ZPoly.Irreducible f`,
`Irreducible (HexPolyZMathlib.toPolynomial f)`, and `Irreducible P` for
a parseable `P : Polynomial ℤ`.

# Runtime factorization and dispatch
%%%
tag := "factor-tactics-runtime"
%%%

The tactic result is proof-oriented. Runtime clients instead use the total
{name}`Hex.ZPoly.factorize` API, which stores multiplicities compactly:

{docstring Hex.Factorization}

{docstring Hex.ZPoly.factorize}

After removing content and repeated factors, modular factorization replaces a
problem over `ℤ` by one over a small finite field. For a suitable prime `p`,
factor the square-free polynomial modulo `p`, then use Hensel lifting to obtain
factors modulo a sufficiently large power `pᵃ`. Each irreducible integer
factor is represented by a product of some of these lifted modular factors.
The remaining problem—deciding which modular factors belong together—is
called *recombination*.

No single recombination method is best at every size. Classical Zassenhaus
recombination tries subsets of the lifted factors, reconstructs the
corresponding integer polynomial, and tests it by exact division. This has low
overhead when the number `r` of modular factors is small, but its worst-case
search is exponential in `r`.

[Van Hoeij's method](https://doi.org/10.1006/jnth.2001.2763) replaces that
subset search by a lattice problem. For a lifted factor `g`, its combined
logarithmic derivative is `Φ(g) = f · g′ / g` modulo `pᵃ`. The identity
`Φ(gh) = Φ(g) + Φ(h)` turns products of modular factors into sums of
coefficient vectors. LLL reduction then isolates the short indicator vectors
that can describe integer factors. Building and reducing the lattice costs
more for small examples, but avoids the exponential dependence on `r`.

This use of LLL should not be confused with the older *LLL factorization
algorithm*. The
[1982 Lenstra–Lenstra–Lovász paper](https://eudml.org/doc/182903) uses lattice
reduction to recover an integer factor itself from sufficiently accurate
modular information. Its historical significance is that it gave the first
polynomial-time algorithm for factoring univariate polynomials over `ℚ`.
That algorithm was not competitive with Berlekamp–Zassenhaus in practice: its
lattices had large dimensions and coefficients. Van Hoeij retains the
practical modular factorization and Hensel-lifting pipeline, and gives lattice
reduction the narrower job of determining which lifted factors belong
together.

The Isabelle/HOL development
[LLL Factorization](https://www.isa-afp.org/entries/LLL_Factorization.html)
formalizes the 1982 algorithm for square-free integer polynomials, including
its polynomial complexity. Hex does not implement that factorization
algorithm. {name}`Hex.lll` provides the lattice-basis reduction used by the
van Hoeij recombination tier, but factor recovery follows van Hoeij's CLD
method rather than the older LLL factorizer.

There is also a direct search for exact divisors over `ℤ`. It does not require
a suitable modular prime and therefore provides a slower but unconditional
last resort. These complementary costs explain the three tiers:

* {name}`Hex.factorClassical` runs subset recombination under a fixed search
  budget and returns `none` if that budget is exhausted or no admissible prime
  is found.
* {name}`Hex.factorLattice` runs van Hoeij recombination and returns `none` if
  the available prime or precision does not produce a verified answer.
* {name}`Hex.factorTrial` performs the direct exact search.
* {name}`Hex.ZPoly.factorize` tries the two optional methods in that order,
  accepts an answer only after its product reconstructs the input, and uses
  the direct search if both decline.
* {name}`Hex.factorTraced` returns the same result together with a
  {name}`Hex.FactorTrace` recording which route was taken.

For each optional tier there are two separate proof questions: whether a
successful answer is correct, and whether the tier is guaranteed to return an
answer. These should not be conflated.

On the first question, the Mathlib bridge already proves that every factor
which would be recorded from a successful default-bound classical run is
irreducible; the corresponding result holds for a successful lattice run at
the public precision cap. These are
{name}`HexBerlekampZassenhausMathlib.factorClassicalFactorsWithBound_factor_irreducible`
and
{name}`HexBerlekampZassenhausMathlib.factorLatticeFactorsWithBound_factor_irreducible`.
The library does not yet expose the complementary packed-product implications
`factorClassical f = some φ → φ.product = f` and
`factorLattice f = some φ → φ.product = f`. Consequently, the reconstruction
check in {name}`Hex.factorTraced` is not yet redundant: an optional answer is
accepted only if its product is `f`; otherwise the proved
{name}`Hex.factorTrial_product` backstop supplies the result. This case split
is what the current {name}`Hex.factorize_product` theorem uses.

On the second question, classical recombination is deliberately allowed to
decline when its resource budget is exhausted. The stronger theorem intended
for the lattice tier says that it cannot decline once the monic-core prime
selector has succeeded and the public precision cap is used. That conditional
completeness theorem has not yet been proved. It would not say that
{name}`Hex.factorLattice` succeeds on every input: the fixed admissible-prime
search can itself fail. A further selector theorem will give checkable
sufficient conditions for prime selection and, together with lattice
completeness and the two packed-product implications, show that the hybrid
never reaches trial division on those inputs. The trial tier remains the
unconditional backstop for arbitrary inputs.

Other formal precedents are the Isabelle/HOL developments
[Polynomial Factorization](https://www.isa-afp.org/entries/Polynomial_Factorization.html),
[The Factorization Algorithm of Berlekamp and Zassenhaus](https://www.isa-afp.org/entries/Berlekamp_Zassenhaus.html),
which verify the surrounding polynomial algorithms and classical
Berlekamp–Zassenhaus recombination.
The accompanying
[Isabelle LLL paper](https://doi.org/10.1007/s10817-020-09552-1) identifies a
verified van Hoeij algorithm as future work. We have not found a later
formalization in the current AFP or published prover literature, so, to the
best of our knowledge, Hex is the first implementation of van Hoeij's CLD
method inside an interactive theorem prover. This is a cautious claim about
the implementation, not a claim that the outstanding completeness theorem
above has already been proved.

For proof clients,
{name}`HexBerlekampZassenhausMathlib.factorize_normalized` gives the full
mathematical description of the output on a nonzero input. It proves that the
recorded product reconstructs the input; each factor is primitive,
irreducible, and has positive leading coefficient; every multiplicity is
positive; distinct factors are not associates; and the scalar is the signed
content of the input.

Finally, `Polynomial (ZMod q)` inputs reuse the prime-field pipeline
through the parser-with-proof of `HexBerlekampMathlib`, producing the
same {name}`Hex.FactoredPoly` shape as the integer case. The modulus
must be a literal prime inside the `ZMod64` bound (`q < 2³¹`), but the
per-factor Rabin-certificate budget binds first for every nonconstant
input: `(degree + 1) · q ≤ 2²⁶`, as described in the
{ref "factor-tactics-coverage"}[coverage section]. The primality checker
tests candidates from `2` through `⌊√q⌋`, so checking that part of the
emitted proof takes `Θ(√q)` remainder tests. The provider budgets that
exact worst-case candidate count against a separate `2¹⁶` ceiling;
throughout the `ZMod64` range it is at most `46,339`.

```lean
open Polynomial

theorem quad_irred :
    Irreducible (X ^ 2 + 2 : Polynomial (ZMod 5)) :=
  irreducibility (X ^ 2 + 2 : Polynomial (ZMod 5))

noncomputable def facP :=
  factor_poly
    ((X + 1) ^ 2 * (X ^ 2 + 2) * 3 : Polynomial (ZMod 5))

example : facP.factors.length = 3 := rfl
```

# What the proofs cost, and what to trust
%%%
tag := "factor-tactics-trust"
%%%

The trust model is uniform across all four input types. The Yun
square-free decomposition, the Berlekamp and Berlekamp-Zassenhaus
factorizers, and the certificate generators run only at elaboration
time, as compiled untrusted search. What lands in the proof term is a
reified literal factorization plus Boolean certificate checks on that
literal data, each discharged by `Eq.refl true`: a coefficient-level
product check reconstructing the input, and one certificate replay per
distinct factor (a Rabin certificate over `Fₚ`, or an integer witness
as described in {ref "factor-tactics-coverage"}[Coverage]). The
Mathlib providers additionally emit one kernel-checked transport
equation identifying the reified literal with the input polynomial.
The factorizer itself never runs in the kernel, except in the opt-in
{ref "factor-tactics-bang"}[bang forms].

Kernel time therefore scales with the certificate replays, not with
the search: it does not matter how many candidate recombinations the
elaboration-time factorizer explored. The generated proof adds no
project-specific axioms:

```lean (name := axiomsCheck)
#print axioms sqrt2_irred
```
```leanOutput axiomsCheck
'sqrt2_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
```

# Coverage and failure modes
%%%
tag := "factor-tactics-coverage"
%%%

All inputs must be closed terms: a polynomial mentioning a local
hypothesis or metavariable is rejected with `must be a closed term
(no local hypotheses or metavariables)`. Beyond that the contract
splits by input type. The executable types (`FpPoly p`, `ZPoly`) must
be evaluable and definitionally transparent: the compiled evaluator
has to see the actual coefficients at elaboration time (a definition
whose body it cannot access produces an evaluation error suggesting a
`public meta import` of its module), and the kernel must be able to
unfold the input to its literal coefficients. The `Polynomial` types
instead go through a syntax-directed parser covering `X`,
`Polynomial.C`, numerals, `+`, `-`, `*`, negation, `^` with literal
`Nat` exponents, and named definitions unfolded under a fuel guard;
an expression outside that grammar, say a raw `Polynomial.monomial`
application, is rejected as unsupported even when it is closed and
transparent.

Degenerate inputs get targeted messages rather than proofs: the zero
polynomial and units are reported as not irreducible, and a reducible
input to `irreducibility` reports the factor count that `factor_poly`
found.

For `FpPoly p` coverage is complete within that contract: any closed
input at a literal prime modulus inside the `ZMod64` bounds factors,
subject to the certificate replay budget: each Rabin-certified factor
must satisfy `(degree + 1) · p ≤ 2²⁶`, checked once per distinct
factor for `factor_poly` and against the input itself for
`irreducibility` (a replay costs roughly that many modular polynomial
operations in the kernel; over-budget inputs fail at elaboration time
with a clear message instead of emitting a proof the kernel cannot
afford). A composite modulus is declined: `Polynomial (ZMod 6)`
inputs report that the modulus is not prime, and `FpPoly 6` likewise.

Over the integers, the factor *search* always succeeds, but the
emitted proof needs a kernel-checkable irreducibility witness for each
factor, and the witness languages do not cover all of `ℤ[X]`. The free
layer supports four witness kinds: prime constants, primitive linear
polynomials, single-prime modular reduction (a reified Rabin
certificate for a prime where the factor stays irreducible), and
Eisenstein-after-shift. Each is found by a bounded search, so an
input can lie inside a certificate language yet outside the
implemented search: the single-prime search tries primes below `512`
(with the Rabin budget enforced separately), the Eisenstein search tries shifts
`0, ±1, ±2, ±3` with witness primes capped at `128` to keep that
auxiliary search bounded, and a prime-constant witness must itself fit
the replay budget. The
Eisenstein kind deserves a story: `x⁴ + 1` is irreducible over `ℤ`
yet reducible modulo *every* prime, so no single-prime witness
exists, but shifting by `1` gives
`(x+1)⁴ + 1 = x⁴ + 4x³ + 6x² + 4x + 2`, Eisenstein at `2`, and the
shift search finds exactly that certificate:

```lean
open Hex Polynomial

def x4p1 : ZPoly := #p[1, 0, 0, 0, 1]

theorem x4p1_irred : ZPoly.Irreducible x4p1 :=
  irreducibility x4p1

example : Irreducible (X ^ 4 + 1 : Polynomial ℤ) := by
  irreducibility
```

When no free-layer witness exists, `HexBerlekampZassenhausMathlib`
adds multi-prime degree-obstruction certificates: several primes
(drawn from a fixed pool, `3` through `71`) whose modular
factor-degree splittings jointly rule out every proper factor
degree. The quartic `x⁴ + 8x + 12` has Galois group `A₄`, so it is
reducible mod every prime and not Eisenstein at any small shift, but
its mod-`p` splittings `{1,3}` and `{2,2}` together obstruct all
proper degrees:

```lean
open Hex Polynomial

/-- `x⁴ + 8x + 12`, with Galois group `A₄`: certified by a
multi-prime degree obstruction, since no single-prime or
Eisenstein witness exists. -/
def quarticA4 : ZPoly :=
  #p[12, 8, 0, 0, 1]

theorem quarticA4_irred : ZPoly.Irreducible quarticA4 :=
  irreducibility quarticA4

example :
    Irreducible (X ^ 4 + C 8 * X + 12 : Polynomial ℤ) := by
  irreducibility
```

One class remains out of reach of every implemented search *and*
every certificate language: polynomials whose modular splittings are
balanced at every candidate prime, which are not Eisenstein at any
small shift, and whose proper
factor degrees survive the multi-prime obstruction. Swinnerton-Dyer
polynomials such as `x⁴ − 10x² + 1` (the minimal polynomial of
`√2 + √3`) are the canonical case. The plain tactics decline these
with a diagnostic naming the failing factor and pointing at the
kernel-decide fallbacks below; they never weaken the emitted statement
to make a proof go through.

# The kernel-decide fallbacks `irreducibility!` and `factor_poly!`
%%%
tag := "factor-tactics-bang"
%%%

`irreducibility!` and `factor_poly!` first run the normal certificate
pipeline; whenever the plain form fails, they fall back to a proof by
`decide`, making the kernel re-run the full factorization to verify
the claim. `irreducibility!` has all the plain forms: term, bare goal
mode, and the `irreducibility! f` / `irreducibility! h : f` tactics.
`factor_poly!` has the term form and the argument-taking tactic form.
This is the one exception to "the factorizer never runs in the
kernel": a kernel-decide fallback for small inputs whose replay stays
in the kernel-reducible classical tier, including the Swinnerton-Dyer
quartic:

```lean
open Hex Polynomial

def swinDyer : ZPoly :=
  #p[1, 0, -10, 0, 1]

theorem swinDyer_irred : ZPoly.Irreducible swinDyer := by
  irreducibility!

theorem sd_poly_irred :
    Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : Polynomial ℤ) :=
  irreducibility! (X ^ 4 - 10 * X ^ 2 + 1 : Polynomial ℤ)
```

On inputs the certificate pipeline serves, the bang forms are plain
pass-throughs and cost nothing extra. On genuine fallbacks the kernel
replay costs real time (quartics are sub-second, degree 8 takes
seconds, degree 12 tens of seconds), so a dense-size budget of 13
rejects larger inputs at elaboration time with a message quoting the
budget. Inputs whose factorization is routed to the native-LLL
lattice tier cannot be certified this way at any size: the FFI
`lllNative` has no kernel-reducible body for the kernel to re-run.
Two further costs land on the calling file when it uses the
module system: the kernel can only re-run definitions whose bodies it
can see, so a `module`-based caller must `import all` the executable
closure (the `HexBerlekampZassenhausMathlib.BangElab` module docstring
and `FactorPolyTests.lean` carry the working block). The examples in
this chapter need no such block because the manual's chapters are not
`module`-based, so every imported body is visible. The elaborator
prechecks kernel reducibility before emitting anything, so a missing
closure fails with a clear message rather than a kernel type
mismatch.

# Cross-references
%%%
tag := "factor-tactics-cross-references"
%%%

The tactic family is the user surface of the factoring pipeline, whose
pieces have their own chapters and libraries:

* {ref "hex-poly-fp"}[HexPolyFp] provides the prime-field polynomials
  {name}`Hex.FpPoly` and the square-free (Yun) decomposition the
  factor search starts from; {ref "hex-poly-z"}[HexPolyZ] provides
  {name}`Hex.ZPoly`, content and primitive parts.
* `HexBerlekamp` implements the finite-field factorizer and the Rabin
  irreducibility certificates, and declares the `factor_poly` /
  `irreducibility` drivers with their provider hook.
* {ref "hex-hensel"}[HexHensel] lifts modular factorizations to prime
  powers, and `HexBerlekampZassenhaus` builds the integer factorizer
  on top of it (with the {ref "hex-lll"}[HexLLL] lattice tier for
  adversarial recombination cases), registering the `Hex.ZPoly`
  provider and the free-layer witness classes.
* `HexBerlekampMathlib` and `HexBerlekampZassenhausMathlib` are the
  correspondence libraries: they identify the executable results with
  `Polynomial (ZMod q)` and `Polynomial ℤ` statements, register those
  providers, add the multi-prime certificates, and declare the bang
  forms.
