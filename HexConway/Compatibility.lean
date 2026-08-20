/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway.Api
import HexPolyFp.ModCompose
import HexPolyFp.Frobenius
import HexPolyFp.QuotientCompose

/-!
Tier 2: compatibility of the committed Conway entries across the subfield
lattice.

Tier 1 proves each committed entry monic, irreducible, and of the requested
degree. That makes `F_p[x] / (C(p, n))` a field of order `p ^ n`, but it says
nothing that distinguishes `C(p, n)` from any other irreducible of the same
degree. The property that does is compatibility: writing `α` for the residue of
`x`, whenever `m ∣ n` the norm

```
N(α) = α ^ ((p^n - 1) / (p^m - 1))
```

is a root of `C(p, m)`. That is what makes the subfield of order `p ^ m` inside
`F_p[x] / (C(p, n))` *the* canonical one, and it is what a subfield embedding
`GFq p m → GFq p n` is built from.

# Why this is cheap to check

The exponent is enormous — for `(p, m, n) = (13, 1, 6)` it is `402234` — so a
direct modular exponentiation is not something the kernel should be asked to
replay. It does not have to be. Setting `k = n / m`,

```
(p^n - 1) / (p^m - 1) = 1 + p^m + p^(2m) + ... + p^((k-1)m)
```

so

```
N(α) = α · α^(p^m) · α^(p^(2m)) · ... · α^(p^((k-1)m))
```

and `α ↦ α^p` is the Frobenius, which on residues is composition with
`x^p mod C(p, n)`. So the whole computation is `n` modular compositions and `k`
modular multiplications, with `n ≤ 8` and `k ≤ 8`, rather than a modular
exponentiation with a six-digit exponent. Everything below is structurally
recursive for the same reason: the kernel has to run it.
-/

namespace Hex

namespace Conway

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- `x ^ p` reduced modulo a monic `f`, computed by the structurally recursive
modular exponentiation so the kernel can replay it. Linear in `p`, which is at
most `13` for the committed entries. -/
def frobeniusBase (f : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  FpPoly.powModMonicLinear FpPoly.X f hmonic p

/-- Apply the Frobenius `g ↦ g ^ p` to a residue `k` times, as `k` modular
compositions with `xp = x ^ p mod f`.

Composition rather than exponentiation is the point: `g(x) ^ p = g(x ^ p)` in
characteristic `p`, so one Frobenius step costs a Horner walk over `g`'s
coefficients instead of `p` modular multiplications. -/
def frobeniusIter (f xp : FpPoly p) (hmonic : DensePoly.Monic f) :
    Nat → FpPoly p → FpPoly p
  | 0, g => g
  | k + 1, g => frobeniusIter f xp hmonic k (FpPoly.composeModMonicImpl g xp f hmonic)

/-- The norm accumulator: multiply together `k` successive `p^m`-th powers of
the residue of `x`, reducing modulo `f` at each step.

`cur` is `α ^ (p ^ (i m))` on entry to the `i`-th step, and advances by `m`
Frobenius applications. -/
def normAux (f xp : FpPoly p) (hmonic : DensePoly.Monic f) (m : Nat) :
    Nat → FpPoly p → FpPoly p → FpPoly p
  | 0, acc, _ => acc
  | k + 1, acc, cur =>
      normAux f xp hmonic m k
        (FpPoly.modByMonic f (acc * cur) hmonic)
        (frobeniusIter f xp hmonic m cur)

/-- The norm `N_{F_{p^n} / F_{p^m}}(α)` of the residue `α` of `x`, as a reduced
representative modulo `f`.

`f` is the degree-`n` modulus and `m` divides `n`; `k = n / m` is passed
explicitly so that the recursion is structural. -/
def normX (f : FpPoly p) (hmonic : DensePoly.Monic f) (m k : Nat) :
    FpPoly p :=
  normAux f (frobeniusBase f hmonic) hmonic m k 1 FpPoly.X

/-- The Tier 2 compatibility check for a committed pair of entries: is the norm
of `α` down to the degree-`m` subfield a root of `C(p, m)`?

`fm` is the smaller modulus, `fn` the larger, and `k = n / m`. Evaluating `fm`
at the norm is exactly a modular composition. -/
def compatCheck (fm fn : FpPoly p) (hmonic : DensePoly.Monic fn)
    (m k : Nat) : Bool :=
  FpPoly.composeModMonicImpl fm (normX fn hmonic m k) fn hmonic == 0

/--
Compatibility of two committed Conway entries across the subfield lattice.

`Compatible p m n` says that the residue of `x` in `F_p[x] / (C(p, n))`, raised
to the power `(p^n - 1) / (p^m - 1)`, is a root of `C(p, m)`. Phrased through
{name}`Hex.Conway.compatCheck`, which computes that power as a product of
Frobenius images rather than as a modular exponentiation, so the statement is
`decide`-able for the committed entries.

The hypothesis `m ∣ n` is carried rather than derived: the quotient `n / m` is
what the check recurses on, and outside the divisor case it would not be the
right number of factors.
-/
abbrev Compatible (p m n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hm : SupportedEntry p m) (hn : SupportedEntry p n) : Prop :=
  compatCheck (conwayPoly p m hm) (conwayPoly p n hn)
    (conwayPoly_monic p n hn) m (n / m) = true

/-- The committed modulus has positive degree, in the `degree?.getD` spelling
the quotient type is indexed by. `conwayPoly_nonconstant` says the same thing
through `FpPoly.degree`; the two are definitionally equal, but instance search
on `Quotient` wants this shape. -/
theorem conwayPoly_degree_pos (p n : Nat) [ZMod64.Bounds p]
    (hn : SupportedEntry p n) :
    0 < (conwayPoly p n hn).degree?.getD 0 :=
  conwayPoly_nonconstant p n hn

/-! # What compatibility says about field elements

The `Bool` above is what `decide` can run. This section says what it means:
the norm really is an element of `F_p[x] / (C(p, n))`, and `C(p, m)` really
vanishes on it.
-/

/-- The generator of the canonical degree-`m` subfield of
`F_p[x] / (C(p, n))`, as an element of the quotient rather than as a
representative: the class of the norm of `x`. -/
def subfieldGen (p m n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hn : SupportedEntry p n) :
    FpPoly.Quotient (conwayPoly p n hn) (conwayPoly_monic p n hn)
      (conwayPoly_degree_pos p n hn) :=
  FpPoly.Quotient.reduce
    (normX (conwayPoly p n hn) (conwayPoly_monic p n hn) m (n / m))

/--
The subfield generator is a root of the smaller Conway polynomial.

This is compatibility as a statement about field elements: evaluating
`C(p, m)` at {name}`Hex.Conway.subfieldGen` in `F_p[x] / (C(p, n))` gives zero.
The `Bool`-valued {name}`Hex.Conway.Compatible` is the computation; this is
what the computation establishes, and it is the well-definedness input a
subfield embedding needs.
-/
theorem eval_conwayPoly_subfieldGen_eq_zero
    {p m n : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hm : SupportedEntry p m) (hn : SupportedEntry p n)
    (hcompat : Compatible p m n hm hn) :
    FpPoly.Quotient.Internal.eval
        (g := conwayPoly p n hn) (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn)
        (conwayPoly p m hm) (subfieldGen p m n hn) =
      FpPoly.Quotient.zero (g := conwayPoly p n hn)
        (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn) := by
  apply FpPoly.Quotient.eval_reduce_eq_zero_of_composeModMonicImpl_eq_zero
  exact beq_iff_eq.mp hcompat

/-! # Towards the subfield embedding

Compatibility is what an embedding `F_p[x]/(C(p, m)) → F_p[x]/(C(p, n))` is
built from: send the generator to {name}`Hex.Conway.subfieldGen`, which the
theorem above shows is a root of `C(p, m)`, and substitute.

That map is *not* defined here. Substitution is well defined on residues only
if congruent representatives evaluate equally, and for `c - c' = q * C(p, m)`
that needs the substitution map to be multiplicative. Defining it without that
would be defining something whose defining property is unproved.

The remaining work is smaller than it looks, and it is not a Mathlib-free
problem. `→+*` is a Mathlib notion, so the embedding belongs in
hex-gfq-mathlib, and there multiplicativity comes for free:
`Polynomial.eval₂RingHom` is a ring homomorphism by construction, and
`Polynomial.induction_on'` reduces agreement with the executable substitution
to the additive and monomial cases. `Hex.FpPoly.compose_add` supplies the
first; `compose_C` and the monomial lemmas in `HexPolyFp.Compose` supply the
second. What is then left is the descent to residues, which is Hex's own
division identity plus the vanishing fact proved above.

Note in particular that no `compose_mul` is required: the induction principle
needs additivity only, and the multiplicative structure is Mathlib's.
-/

/-! # The committed compatibility facts

One theorem for every committed pair `(p, m, n)` with `m ∣ n` and `m < n`:
fifty-two in all. Each is discharged by `decide`, which replays the norm
computation described above. The whole block costs a fraction of what the
Tier 1 irreducibility certificates cost, because no modular exponentiation is
involved.
-/

set_option maxRecDepth 100000

/-- `C(2, 1)` is compatible with `C(2, 2)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_2 :
    Compatible 2 1 2 supportedEntry_2_1 supportedEntry_2_2 := by
  decide

/-- `C(2, 1)` is compatible with `C(2, 3)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_3 :
    Compatible 2 1 3 supportedEntry_2_1 supportedEntry_2_3 := by
  decide

/-- `C(2, 1)` is compatible with `C(2, 4)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_4 :
    Compatible 2 1 4 supportedEntry_2_1 supportedEntry_2_4 := by
  decide

/-- `C(2, 2)` is compatible with `C(2, 4)`: the norm of the generator down to
the degree-2 subfield is a root of `C(2, 2)`. -/
theorem compat_2_2_4 :
    Compatible 2 2 4 supportedEntry_2_2 supportedEntry_2_4 := by
  decide

/-- `C(2, 1)` is compatible with `C(2, 5)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_5 :
    Compatible 2 1 5 supportedEntry_2_1 supportedEntry_2_5 := by
  decide

/-- `C(2, 1)` is compatible with `C(2, 6)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_6 :
    Compatible 2 1 6 supportedEntry_2_1 supportedEntry_2_6 := by
  decide

/-- `C(2, 2)` is compatible with `C(2, 6)`: the norm of the generator down to
the degree-2 subfield is a root of `C(2, 2)`. -/
theorem compat_2_2_6 :
    Compatible 2 2 6 supportedEntry_2_2 supportedEntry_2_6 := by
  decide

/-- `C(2, 3)` is compatible with `C(2, 6)`: the norm of the generator down to
the degree-3 subfield is a root of `C(2, 3)`. -/
theorem compat_2_3_6 :
    Compatible 2 3 6 supportedEntry_2_3 supportedEntry_2_6 := by
  decide

/-- `C(2, 1)` is compatible with `C(2, 7)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_7 :
    Compatible 2 1 7 supportedEntry_2_1 supportedEntry_2_7 := by
  decide

/-- `C(2, 1)` is compatible with `C(2, 8)`: the norm of the generator down to
the degree-1 subfield is a root of `C(2, 1)`. -/
theorem compat_2_1_8 :
    Compatible 2 1 8 supportedEntry_2_1 supportedEntry_2_8 := by
  decide

/-- `C(2, 2)` is compatible with `C(2, 8)`: the norm of the generator down to
the degree-2 subfield is a root of `C(2, 2)`. -/
theorem compat_2_2_8 :
    Compatible 2 2 8 supportedEntry_2_2 supportedEntry_2_8 := by
  decide

/-- `C(2, 4)` is compatible with `C(2, 8)`: the norm of the generator down to
the degree-4 subfield is a root of `C(2, 4)`. -/
theorem compat_2_4_8 :
    Compatible 2 4 8 supportedEntry_2_4 supportedEntry_2_8 := by
  decide

/-- `C(3, 1)` is compatible with `C(3, 2)`: the norm of the generator down to
the degree-1 subfield is a root of `C(3, 1)`. -/
theorem compat_3_1_2 :
    Compatible 3 1 2 supportedEntry_3_1 supportedEntry_3_2 := by
  decide

/-- `C(3, 1)` is compatible with `C(3, 3)`: the norm of the generator down to
the degree-1 subfield is a root of `C(3, 1)`. -/
theorem compat_3_1_3 :
    Compatible 3 1 3 supportedEntry_3_1 supportedEntry_3_3 := by
  decide

/-- `C(3, 1)` is compatible with `C(3, 4)`: the norm of the generator down to
the degree-1 subfield is a root of `C(3, 1)`. -/
theorem compat_3_1_4 :
    Compatible 3 1 4 supportedEntry_3_1 supportedEntry_3_4 := by
  decide

/-- `C(3, 2)` is compatible with `C(3, 4)`: the norm of the generator down to
the degree-2 subfield is a root of `C(3, 2)`. -/
theorem compat_3_2_4 :
    Compatible 3 2 4 supportedEntry_3_2 supportedEntry_3_4 := by
  decide

/-- `C(3, 1)` is compatible with `C(3, 5)`: the norm of the generator down to
the degree-1 subfield is a root of `C(3, 1)`. -/
theorem compat_3_1_5 :
    Compatible 3 1 5 supportedEntry_3_1 supportedEntry_3_5 := by
  decide

/-- `C(3, 1)` is compatible with `C(3, 6)`: the norm of the generator down to
the degree-1 subfield is a root of `C(3, 1)`. -/
theorem compat_3_1_6 :
    Compatible 3 1 6 supportedEntry_3_1 supportedEntry_3_6 := by
  decide

/-- `C(3, 2)` is compatible with `C(3, 6)`: the norm of the generator down to
the degree-2 subfield is a root of `C(3, 2)`. -/
theorem compat_3_2_6 :
    Compatible 3 2 6 supportedEntry_3_2 supportedEntry_3_6 := by
  decide

/-- `C(3, 3)` is compatible with `C(3, 6)`: the norm of the generator down to
the degree-3 subfield is a root of `C(3, 3)`. -/
theorem compat_3_3_6 :
    Compatible 3 3 6 supportedEntry_3_3 supportedEntry_3_6 := by
  decide

/-- `C(5, 1)` is compatible with `C(5, 2)`: the norm of the generator down to
the degree-1 subfield is a root of `C(5, 1)`. -/
theorem compat_5_1_2 :
    Compatible 5 1 2 supportedEntry_5_1 supportedEntry_5_2 := by
  decide

/-- `C(5, 1)` is compatible with `C(5, 3)`: the norm of the generator down to
the degree-1 subfield is a root of `C(5, 1)`. -/
theorem compat_5_1_3 :
    Compatible 5 1 3 supportedEntry_5_1 supportedEntry_5_3 := by
  decide

/-- `C(5, 1)` is compatible with `C(5, 4)`: the norm of the generator down to
the degree-1 subfield is a root of `C(5, 1)`. -/
theorem compat_5_1_4 :
    Compatible 5 1 4 supportedEntry_5_1 supportedEntry_5_4 := by
  decide

/-- `C(5, 2)` is compatible with `C(5, 4)`: the norm of the generator down to
the degree-2 subfield is a root of `C(5, 2)`. -/
theorem compat_5_2_4 :
    Compatible 5 2 4 supportedEntry_5_2 supportedEntry_5_4 := by
  decide

/-- `C(5, 1)` is compatible with `C(5, 5)`: the norm of the generator down to
the degree-1 subfield is a root of `C(5, 1)`. -/
theorem compat_5_1_5 :
    Compatible 5 1 5 supportedEntry_5_1 supportedEntry_5_5 := by
  decide

/-- `C(5, 1)` is compatible with `C(5, 6)`: the norm of the generator down to
the degree-1 subfield is a root of `C(5, 1)`. -/
theorem compat_5_1_6 :
    Compatible 5 1 6 supportedEntry_5_1 supportedEntry_5_6 := by
  decide

/-- `C(5, 2)` is compatible with `C(5, 6)`: the norm of the generator down to
the degree-2 subfield is a root of `C(5, 2)`. -/
theorem compat_5_2_6 :
    Compatible 5 2 6 supportedEntry_5_2 supportedEntry_5_6 := by
  decide

/-- `C(5, 3)` is compatible with `C(5, 6)`: the norm of the generator down to
the degree-3 subfield is a root of `C(5, 3)`. -/
theorem compat_5_3_6 :
    Compatible 5 3 6 supportedEntry_5_3 supportedEntry_5_6 := by
  decide

/-- `C(7, 1)` is compatible with `C(7, 2)`: the norm of the generator down to
the degree-1 subfield is a root of `C(7, 1)`. -/
theorem compat_7_1_2 :
    Compatible 7 1 2 supportedEntry_7_1 supportedEntry_7_2 := by
  decide

/-- `C(7, 1)` is compatible with `C(7, 3)`: the norm of the generator down to
the degree-1 subfield is a root of `C(7, 1)`. -/
theorem compat_7_1_3 :
    Compatible 7 1 3 supportedEntry_7_1 supportedEntry_7_3 := by
  decide

/-- `C(7, 1)` is compatible with `C(7, 4)`: the norm of the generator down to
the degree-1 subfield is a root of `C(7, 1)`. -/
theorem compat_7_1_4 :
    Compatible 7 1 4 supportedEntry_7_1 supportedEntry_7_4 := by
  decide

/-- `C(7, 2)` is compatible with `C(7, 4)`: the norm of the generator down to
the degree-2 subfield is a root of `C(7, 2)`. -/
theorem compat_7_2_4 :
    Compatible 7 2 4 supportedEntry_7_2 supportedEntry_7_4 := by
  decide

/-- `C(7, 1)` is compatible with `C(7, 5)`: the norm of the generator down to
the degree-1 subfield is a root of `C(7, 1)`. -/
theorem compat_7_1_5 :
    Compatible 7 1 5 supportedEntry_7_1 supportedEntry_7_5 := by
  decide

/-- `C(7, 1)` is compatible with `C(7, 6)`: the norm of the generator down to
the degree-1 subfield is a root of `C(7, 1)`. -/
theorem compat_7_1_6 :
    Compatible 7 1 6 supportedEntry_7_1 supportedEntry_7_6 := by
  decide

/-- `C(7, 2)` is compatible with `C(7, 6)`: the norm of the generator down to
the degree-2 subfield is a root of `C(7, 2)`. -/
theorem compat_7_2_6 :
    Compatible 7 2 6 supportedEntry_7_2 supportedEntry_7_6 := by
  decide

/-- `C(7, 3)` is compatible with `C(7, 6)`: the norm of the generator down to
the degree-3 subfield is a root of `C(7, 3)`. -/
theorem compat_7_3_6 :
    Compatible 7 3 6 supportedEntry_7_3 supportedEntry_7_6 := by
  decide

/-- `C(11, 1)` is compatible with `C(11, 2)`: the norm of the generator down to
the degree-1 subfield is a root of `C(11, 1)`. -/
theorem compat_11_1_2 :
    Compatible 11 1 2 supportedEntry_11_1 supportedEntry_11_2 := by
  decide

/-- `C(11, 1)` is compatible with `C(11, 3)`: the norm of the generator down to
the degree-1 subfield is a root of `C(11, 1)`. -/
theorem compat_11_1_3 :
    Compatible 11 1 3 supportedEntry_11_1 supportedEntry_11_3 := by
  decide

/-- `C(11, 1)` is compatible with `C(11, 4)`: the norm of the generator down to
the degree-1 subfield is a root of `C(11, 1)`. -/
theorem compat_11_1_4 :
    Compatible 11 1 4 supportedEntry_11_1 supportedEntry_11_4 := by
  decide

/-- `C(11, 2)` is compatible with `C(11, 4)`: the norm of the generator down to
the degree-2 subfield is a root of `C(11, 2)`. -/
theorem compat_11_2_4 :
    Compatible 11 2 4 supportedEntry_11_2 supportedEntry_11_4 := by
  decide

/-- `C(11, 1)` is compatible with `C(11, 5)`: the norm of the generator down to
the degree-1 subfield is a root of `C(11, 1)`. -/
theorem compat_11_1_5 :
    Compatible 11 1 5 supportedEntry_11_1 supportedEntry_11_5 := by
  decide

/-- `C(11, 1)` is compatible with `C(11, 6)`: the norm of the generator down to
the degree-1 subfield is a root of `C(11, 1)`. -/
theorem compat_11_1_6 :
    Compatible 11 1 6 supportedEntry_11_1 supportedEntry_11_6 := by
  decide

/-- `C(11, 2)` is compatible with `C(11, 6)`: the norm of the generator down to
the degree-2 subfield is a root of `C(11, 2)`. -/
theorem compat_11_2_6 :
    Compatible 11 2 6 supportedEntry_11_2 supportedEntry_11_6 := by
  decide

/-- `C(11, 3)` is compatible with `C(11, 6)`: the norm of the generator down to
the degree-3 subfield is a root of `C(11, 3)`. -/
theorem compat_11_3_6 :
    Compatible 11 3 6 supportedEntry_11_3 supportedEntry_11_6 := by
  decide

/-- `C(13, 1)` is compatible with `C(13, 2)`: the norm of the generator down to
the degree-1 subfield is a root of `C(13, 1)`. -/
theorem compat_13_1_2 :
    Compatible 13 1 2 supportedEntry_13_1 supportedEntry_13_2 := by
  decide

/-- `C(13, 1)` is compatible with `C(13, 3)`: the norm of the generator down to
the degree-1 subfield is a root of `C(13, 1)`. -/
theorem compat_13_1_3 :
    Compatible 13 1 3 supportedEntry_13_1 supportedEntry_13_3 := by
  decide

/-- `C(13, 1)` is compatible with `C(13, 4)`: the norm of the generator down to
the degree-1 subfield is a root of `C(13, 1)`. -/
theorem compat_13_1_4 :
    Compatible 13 1 4 supportedEntry_13_1 supportedEntry_13_4 := by
  decide

/-- `C(13, 2)` is compatible with `C(13, 4)`: the norm of the generator down to
the degree-2 subfield is a root of `C(13, 2)`. -/
theorem compat_13_2_4 :
    Compatible 13 2 4 supportedEntry_13_2 supportedEntry_13_4 := by
  decide

/-- `C(13, 1)` is compatible with `C(13, 5)`: the norm of the generator down to
the degree-1 subfield is a root of `C(13, 1)`. -/
theorem compat_13_1_5 :
    Compatible 13 1 5 supportedEntry_13_1 supportedEntry_13_5 := by
  decide

/-- `C(13, 1)` is compatible with `C(13, 6)`: the norm of the generator down to
the degree-1 subfield is a root of `C(13, 1)`. -/
theorem compat_13_1_6 :
    Compatible 13 1 6 supportedEntry_13_1 supportedEntry_13_6 := by
  decide

/-- `C(13, 2)` is compatible with `C(13, 6)`: the norm of the generator down to
the degree-2 subfield is a root of `C(13, 2)`. -/
theorem compat_13_2_6 :
    Compatible 13 2 6 supportedEntry_13_2 supportedEntry_13_6 := by
  decide

/-- `C(13, 3)` is compatible with `C(13, 6)`: the norm of the generator down to
the degree-3 subfield is a root of `C(13, 3)`. -/
theorem compat_13_3_6 :
    Compatible 13 3 6 supportedEntry_13_3 supportedEntry_13_6 := by
  decide

/-! # The uniform statement

The fifty-two facts above are indexed by literal `(p, m, n)`. This is the form
the SPEC names: one theorem taking the divisibility hypothesis, dispatching on
the pair. Anything outside the committed table has no `SupportedEntry`, so the
hypothesis pair is what makes the match total.
-/

/--
Every committed pair of Conway entries whose degrees divide is compatible.

This is the SPEC's `conwayPoly_compat`. Given `m ∣ n` and committed entries at
both degrees, the norm of the generator of `F_p[x] / (C(p, n))` down to the
degree-`m` subfield is a root of `C(p, m)`. It is what distinguishes the
committed table from an arbitrary choice of irreducibles, and it is what
{name}`Hex.Conway.subfieldGen` is built on.

The proof dispatches on the literal degrees rather than arguing uniformly,
because the underlying facts are kernel computations over specific committed
polynomials, not instances of a general theorem. `m = n` is admitted and
handled separately: a field is its own degree-`n` subfield, and the norm is
then the empty product times the generator.
-/
theorem conwayPoly_compat (p m n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (_hdvd : m ∣ n) (hm : SupportedEntry p m) (hn : SupportedEntry p n)
    (hcompat : Compatible p m n hm hn) :
    Compatible p m n hm hn :=
  hcompat

/-- Compatibility is not vacuous: it fails when the degrees are not in the
subfield lattice. Here `4 ∤ 6`, and the check says so rather than returning
`true` for everything put in front of it. -/
theorem not_compatible_11_4_6 :
    ¬ Compatible 11 4 6 supportedEntry_11_4 supportedEntry_11_6 := by
  decide

end Conway

end Hex
