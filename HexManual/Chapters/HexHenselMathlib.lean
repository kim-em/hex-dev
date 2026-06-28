/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexHenselMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexHenselMathlib: Hensel lifting correctness" =>
%%%
tag := "hex-hensel-mathlib"
%%%

# Introduction
%%%
tag := "hex-hensel-mathlib-intro"
%%%

`HexHenselMathlib` is the Mathlib correspondence layer for the
executable Hensel-lifting surface of {ref "hex-hensel"}[`HexHensel`].
The executable library lifts a mod-`p` factorization of an integer
polynomial to a factorization modulo `p ^ k`, computing on the fast
{name}`Hex.ZPoly` coefficient-array representation; this bridge
re-expresses each lifting step as a theorem about Mathlib's canonical
{name}`Polynomial` over `ℤ`, reduced through the ring maps
`ℤ →+* ZMod (p ^ k)`.

Unlike the ring-correspondence bridges
({ref "hex-poly-mathlib"}[`HexPolyMathlib`] and its siblings), this
layer carries no bundled equivalence. Hensel lifting is a *procedure*,
not an algebraic operation, so there is nothing to package as a
`≃+*`; what the bridge proves instead is a family of correctness and
uniqueness statements about the procedure's output. A downstream
Mathlib-side factorization argument uses these to know that the
executable lift produces a genuine factorization modulo `p ^ k`, that
it extends the given base factorization, that it preserves the degree
of the monic factor, and that the lift is the unique such
factorization with the given mod-`p` reduction.

The whole surface lives in namespace `HexHenselMathlib` and is
`noncomputable`: it exists only to justify the executable theory, not
to be evaluated. The statements are documented here by signature and
theorem, and the worked {ref "hex-hensel-mathlib-examples"}[examples]
below *typecheck* a transported statement rather than evaluating it.

# Coefficientwise reduction
%%%
tag := "hex-hensel-mathlib-reduction"
%%%

The lowest layer of the bridge reads divisibility off coefficients.
Mapping an integer polynomial through `ℤ →+* ZMod p` sends a
coefficient to zero exactly when `p` divides it, and equality after
reduction is divisibility of the coefficient difference.

{docstring HexHenselMathlib.coeff_map_intCastRingHom_eq_zero_iff_dvd}

{docstring HexHenselMathlib.coeff_map_intCastRingHom_eq_iff_dvd_sub}

When the divisibility is exact, the integer coefficient is recovered
from its quotient; both orientations of the cancellation are provided
for use in coefficientwise quotient rewrites.

{docstring HexHenselMathlib.coeff_ediv_mul_eq_of_dvd}

{docstring HexHenselMathlib.coeff_mul_ediv_eq_of_dvd}

# The reduction tower
%%%
tag := "hex-hensel-mathlib-tower"
%%%

Hensel lifting moves between the moduli `p`, `p ^ k`, and `p ^ (k+1)`,
so the bridge needs the canonical reductions of the tower
`ZMod (p ^ (k+1)) → ZMod (p ^ k) → ZMod p` to compose as expected.
The ring-map identities come first, at the level of `ℤ`-casts.

{docstring HexHenselMathlib.zmod_castHom_comp_intCastRingHom_pow_succ}

{docstring HexHenselMathlib.zmod_castHom_comp_intCastRingHom_pow_step}

Mapped over polynomials, the same two facts say that reducing a lifted
factor down the tower agrees with reducing the original directly — the
compatibility a precision-doubling argument rewrites with.

{docstring HexHenselMathlib.polynomial_map_zmod_pow_succ_to_base}

{docstring HexHenselMathlib.polynomial_map_zmod_pow_succ_to_pow}

The correction term added at each lifting step has the form
`C p * u`, which is nilpotent modulo `p ^ k`; this makes the Hensel
update factor `1 + C p * u` a unit, the algebraic fact behind the
step's invertibility.

{docstring HexHenselMathlib.isUnit_one_add_C_mul}

# Coprimality lifting
%%%
tag := "hex-hensel-mathlib-coprime"
%%%

A Hensel lift needs the input cofactors to stay coprime as the modulus
grows. Coprimality of the mod-`p` reductions lifts to coprimality
modulo `p ^ k`: a Bezout combination modulo `p` is corrected by the
nilpotent-unit lemma above into a Bezout combination modulo `p ^ k`.

{docstring HexHenselMathlib.coprime_mod_p_lifts}

The dual analytic fact is a coprime monic cancellation with a strict
degree bound — the load-bearing step for binary-Hensel uniqueness.
After reducing a difference equation modulo `p`, a coprime monic
divisor below its own degree forces both cofactors to vanish.

{docstring HexHenselMathlib.isCoprime_cancel_of_natDegree_lt}

# The congruence dictionary
%%%
tag := "hex-hensel-mathlib-dictionary"
%%%

The executable side states everything as a coefficientwise congruence
{name}`Hex.ZPoly.congr` modulo `m`; the Mathlib side states everything
as equality after `Polynomial.map (Int.castRingHom (ZMod m))`. The two
directions of this dictionary are the workhorses through which every
executable lifting spec crosses the bridge.

{docstring HexHenselMathlib.zpoly_congr_toPolynomial_map_eq}

{docstring HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq}

The executable monic predicate {name}`Hex.DensePoly.Monic` likewise
transfers to Mathlib's {name}`Polynomial.Monic`, since the leading
coefficient is carried across faithfully by
{name}`HexPolyMathlib.toPolynomial`.

{docstring HexHenselMathlib.toPolynomial_monic_of_dense_monic}

# Hensel correctness
%%%
tag := "hex-hensel-mathlib-correct"
%%%

The headline correctness statements concern the iterative executable
lift {name}`Hex.ZPoly.henselLift`. Given a base factorization of `f`
modulo `p` together with Bezout witnesses, the lift produces a genuine
factorization of `f` modulo `p ^ k`.

{docstring HexHenselMathlib.hensel_correct}

The lift extends the input factorization: reduced back modulo the base
prime `p`, the lifted factors recover the originals.

{docstring HexHenselMathlib.hensel_extends}

It also preserves the Mathlib degree of the monic lifted factor, so a
caller tracking degrees through the lift never recomputes them.

{docstring HexHenselMathlib.hensel_degree}

# The quadratic step
%%%
tag := "hex-hensel-mathlib-quadratic"
%%%

The quadratic variant {name}`Hex.ZPoly.quadraticHenselStep` doubles
the precision in one step, from a modulus `m` to `m * m`. Its
Mathlib-facing specs mirror the linear ones: the step gives a
factorization modulo `m * m`, refreshes the Bezout witnesses at the
doubled precision, and preserves monicity of the lifted factor.

{docstring HexHenselMathlib.quadraticHenselStep_factor_correct}

{docstring HexHenselMathlib.quadraticHenselStep_bezout_correct}

{docstring HexHenselMathlib.quadraticHenselStep_monic}

# Uniqueness
%%%
tag := "hex-hensel-mathlib-unique"
%%%

The uniqueness theorem pins the lift down completely: two coprime
monic factorizations of `f` that share a reduction modulo `p` agree
modulo every `p ^ k`. This is the statement that makes "the Hensel
lift" well-defined as a function of its base data, and it is proved by
induction on `k` using the coprime monic cancellation above.

{docstring HexHenselMathlib.hensel_unique}

Specialised to the quadratic step at doubled precision, uniqueness
says the quadratic lift coincides with any monic factorization sharing
its mod-`p` reduction — the bridge between the linear and quadratic
lifting paths.

{docstring HexHenselMathlib.quadraticHenselStep_unique_mod_pow_two_mul}

# Multifactor agreement
%%%
tag := "hex-hensel-mathlib-multifactor"
%%%

The executable theory carries two multifactor lifters — a linear one
and a quadratic one — over a whole list of factors. The bridge proves
they agree. First, the recursive linear invariant
{name}`Hex.ZPoly.MultifactorLiftInvariant` supplies enough mod-`p`
split data to initialise the quadratic invariant, given monic input
heads.

{docstring HexHenselMathlib.quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant}

The capstone of this layer states that the two lifters produce the
same factors modulo `p ^ k`. This is the lift-uniqueness obligation
that {ref "hex-hensel"}[`HexHensel`] defers to the Mathlib bridge: the
fast quadratic lifter and the reference linear lifter compute the same
factorization, so the executable factorization pipeline may use either.

{docstring HexHenselMathlib.multifactorLift_eq_multifactorLiftQuadratic}

# Worked examples
%%%
tag := "hex-hensel-mathlib-examples"
%%%

Because the surface is `noncomputable`, the examples type-check a
transported statement rather than evaluating it. The coefficientwise
reduction dictionary applies directly: the mod-`p` reduction of a
coefficient vanishes exactly when `p` divides it.

```lean
open HexHenselMathlib Polynomial

variable (f : Polynomial ℤ) (p n : ℕ)

example :
    (f.map (Int.castRingHom (ZMod p))).coeff n = 0
      ↔ (p : ℤ) ∣ f.coeff n :=
  coeff_map_intCastRingHom_eq_zero_iff_dvd f p n
```

Monicity transfers across the bridge, so a monic executable
polynomial is a monic Mathlib polynomial after transport:

```lean
open HexHenselMathlib

variable (g : Hex.ZPoly)

example (hg : Hex.DensePoly.Monic g) :
    (HexPolyMathlib.toPolynomial g).Monic :=
  toPolynomial_monic_of_dense_monic g hg
```

# Cross-references
%%%
tag := "hex-hensel-mathlib-cross-references"
%%%

`HexHenselMathlib` is the Mathlib bridge for the executable Hensel
library and is built on the dense-polynomial correspondence:

* {ref "hex-hensel"}[`HexHensel`] is the computational counterpart. It
  defines the executable lifters {name}`Hex.ZPoly.henselLift`,
  {name}`Hex.ZPoly.quadraticHenselStep`, and the multifactor lifters
  that this chapter transfers, together with the coefficientwise
  congruence {name}`Hex.ZPoly.congr` the executable specs are stated
  in. The executable side carries the runtime lifting paths; the
  bridge re-expresses each spec as a theorem about
  `Polynomial ℤ` reduced to `ZMod (p ^ k)`.
* {ref "hex-poly-mathlib"}[`HexPolyMathlib`] supplies the transfer map
  {name}`HexPolyMathlib.toPolynomial` and the coefficient lemma
  {name}`HexPolyMathlib.coeff_toPolynomial` through which every
  statement here crosses from {name}`Hex.ZPoly` to {name}`Polynomial`.
  The Hensel correctness theorems are the proof-side justification that
  the fast executable lifting computes the mathematically intended
  factorization modulo `p ^ k`.
