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

`factor_poly` and `irreducibility` factor a concrete polynomial, or
prove one irreducible, in a single call. The factorization runs as
compiled, untrusted search while the file elaborates; the emitted proof
term carries only certificate checks the kernel replays on literal
data. One call site, no visible certificates, no `native_decide`, and
no axioms beyond the standard three.

The tactics accept four input types, enabled by imports. The drivers
live in `HexBerlekamp` and handle {name}`Hex.FpPoly` (dense
polynomials over a prime field) natively. Importing
`HexBerlekampZassenhaus` adds {name}`Hex.ZPoly` (dense integer
polynomials); the correspondence libraries `HexBerlekampMathlib` and
`HexBerlekampZassenhausMathlib` add `Polynomial (ZMod q)` and
`Polynomial ℤ`. Each library registers its arm as a provider probed by
name at elaboration time, so the drivers need no imports in that
direction; with everything imported the tactics simply accept all four
types.

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

The same name is a term elaborator, so the proof can be a definition's
entire body:

```lean
open Polynomial

theorem sqrt2_irred :
    Irreducible (X ^ 2 - 2 : Polynomial ℤ) :=
  irreducibility (X ^ 2 - 2 : Polynomial ℤ)
```

Behind the call, the input expression is parsed to an executable
integer polynomial together with a proof that the parse is faithful,
the compiled factorizer confirms there is exactly one irreducible
factor, and a per-factor certificate (for `x² − 2`, a single-prime
modular witness) is reified into the proof term for the kernel to
check.

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

The structure unpacks with `obtain`, so the fields can be named and
used however a proof needs them:

```lean
open Polynomial

example : True := by
  obtain ⟨scalar, factors, factors_mul, factors_irred⟩ :=
    factor_poly (X ^ 2 - 2 : Polynomial ℤ)
  trivial
```

# The executable types
%%%
tag := "factor-tactics-executable"
%%%

The Mathlib-facing forms above are transports of the same machinery
working on the executable types, which are user surfaces in their
own right. Over a prime field the input is a {name}`Hex.FpPoly`
(see the {ref "hex-poly-fp"}[HexPolyFp chapter]) and the result is an
{name}`Hex.FpPoly.Factored`:

{docstring Hex.FpPoly.Factored}

The example below factors `3 · (x+1)² · (x²+2)` over `F₅`: non-monic
and non-square-free, so the scalar, multiplicity, and normalization
conventions are all visible. The factors come back monic, in
nondecreasing degree order, repeated to multiplicity, with the leading
unit in `scalar`:

```lean
open Hex

instance : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

def z (n : Nat) : ZMod64 5 := ZMod64.ofNat 5 n

/-- `3 · (x+1)² · (x²+2)` over `F₅`: non-monic and
non-square-free. -/
def testF : FpPoly 5 :=
  DensePoly.C (z 3) *
    (FpPoly.ofCoeffs #[z 1, z 1] *
     FpPoly.ofCoeffs #[z 1, z 1] *
     FpPoly.ofCoeffs #[z 2, z 0, z 1])

noncomputable def facF := factor_poly testF

example : facF.factors.length = 3 := rfl
example : facF.scalar = z 3 := rfl

def irrF : FpPoly 5 := FpPoly.ofCoeffs #[z 2, z 0, z 1]

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

def quadZ : ZPoly := DensePoly.ofCoeffs #[1, 0, 1]

theorem quadZ_irred : ZPoly.Irreducible quadZ :=
  irreducibility quadZ
```

Irreducibility of a `ZPoly` is stated with the Mathlib-free class
{name}`Hex.ZPoly.Irreducible`, which the correspondence library proves
equivalent to Mathlib's `Irreducible` under `toPolynomial`. Goal-mode
`irreducibility` closes all three spellings: `Hex.ZPoly.Irreducible f`,
`Irreducible (HexPolyZMathlib.toPolynomial f)`, and `Irreducible P` for
a parseable `P : Polynomial ℤ`.

Finally, `Polynomial (ZMod q)` inputs (literal prime `q < 2³¹`) reuse
the prime-field pipeline through the parser-with-proof of
`HexBerlekampMathlib`, producing the same
{name}`Hex.FactoredPoly` shape as the integer case:

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

# Tactic forms
%%%
tag := "factor-tactics-tactic-forms"
%%%

Both names are also tactics. For the executable types,
`factor_poly f` introduces `scalar` and `factors` as transparent `let`
bindings plus the two hypotheses `factors_mul` and `factors_irred`;
because the `let`s are transparent, facts about them are available by
`rfl`:

```lean
open Hex

example : True := by
  factor_poly testF
  have : factors.length = 3 := rfl
  exact True.intro
```

(For the `Polynomial` input types the tactic form instead lands the
whole structure as a single `factored` hypothesis.)

The `irreducibility` tactic has three forms: bare, closing an
`Irreducible` goal as in the {ref "factor-tactics-irreducibility"}[lead
example]; `irreducibility f`, adding the fact as an anonymous
hypothesis; and `irreducibility h : f`, naming it:

```lean
open Hex Polynomial

example : FpPoly.Irreducible irrF := by irreducibility

example : True := by
  irreducibility (X ^ 2 - 2 : Polynomial ℤ)
  irreducibility h : (X ^ 2 + X + 1 : Polynomial ℤ)
  exact True.intro
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
elaboration-time factorizer explored. And because everything is an
ordinary proof term, the axiom cone stays clean:

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

Inputs must be closed, kernel-transparent terms: the compiled
evaluator has to see the actual coefficients at elaboration time, so a
polynomial mentioning a local hypothesis or metavariable is rejected
with `must be a closed term (no local hypotheses or metavariables)`,
and a definition whose body the evaluator cannot access produces an
evaluation error suggesting a `public meta import` of its module.
Degenerate inputs get targeted messages rather than proofs: the zero
polynomial and units are reported as not irreducible, and a reducible
input to `irreducibility` reports the factor count that `factor_poly`
found.

For `FpPoly p` coverage is complete within that contract: any closed
input at a literal prime modulus inside the `ZMod64` bounds factors,
subject to the certificate replay budget `deg · p ≤ 2²⁶` (each Rabin
replay costs roughly `deg · p` modular polynomial operations in the
kernel; over-budget inputs fail at elaboration time with a clear
message instead of emitting a proof the kernel cannot afford). A
composite modulus is declined: `Polynomial (ZMod 6)` inputs report
that the modulus is not prime, and `FpPoly 6` likewise.

Over the integers, the factor *search* always succeeds, but the
emitted proof needs a kernel-checkable irreducibility witness for each
factor, and the witness languages do not cover all of `ℤ[X]`. The free
layer
certifies four classes: prime constants, primitive linear polynomials,
factors irreducible modulo a single good prime (a reified Rabin
certificate), and Eisenstein-after-shift. The last deserves a story:
`x⁴ + 1` is irreducible over `ℤ` yet reducible modulo *every* prime,
so no single-prime witness exists, but shifting by `1` gives
`(x+1)⁴ + 1 = x⁴ + 4x³ + 6x² + 4x + 2`, Eisenstein at `2`, and the
shift search (shifts `0, ±1, ±2, ±3`) finds exactly that certificate:

```lean
open Hex Polynomial

def x4p1 : ZPoly := DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

theorem x4p1_irred : ZPoly.Irreducible x4p1 :=
  irreducibility x4p1

example : Irreducible (X ^ 4 + 1 : Polynomial ℤ) := by
  irreducibility
```

When no free-layer witness exists, `HexBerlekampZassenhausMathlib`
adds multi-prime degree-obstruction certificates: several primes whose
modular factor-degree splittings jointly rule out every proper factor
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
  DensePoly.ofCoeffs #[12, 8, 0, 0, 1]

theorem quarticA4_irred : ZPoly.Irreducible quarticA4 :=
  irreducibility quarticA4

example :
    Irreducible (X ^ 4 + C 8 * X + 12 : Polynomial ℤ) := by
  irreducibility
```

One class remains out of reach of every certificate language:
polynomials whose modular splittings are balanced at every candidate
prime, which are not Eisenstein at any small shift, *and* whose proper
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

`irreducibility!` and `factor_poly!` (all the same term, tactic, and
goal forms) first run the normal certificate pipeline and fall back,
only when it declines, to a proof by `decide`: the kernel re-runs the
full factorization to verify the claim. This is the one exception to
"the factorizer never runs in the kernel", and it covers exactly the
inputs the certificate languages cannot, including the Swinnerton-Dyer
quartic:

```lean
open Hex Polynomial

def swinDyer : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, -10, 0, 1]

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
budget. Two further costs land on the calling file when it uses the
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
