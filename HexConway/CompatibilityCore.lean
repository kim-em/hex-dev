/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexConway.Api
public import HexConway.Power
public import HexPolyFp.ModCompose
public import HexPolyFp.Frobenius
public import HexPolyFp.QuotientCompose
public import HexPolyFp.QuotientFrobenius

public section

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

# How the norm is checked

Setting `k = n / m`, the geometric-sum identity gives

```
(p^n - 1) / (p^m - 1) = 1 + p^m + p^(2m) + ... + p^((k-1)m)
```

so the norm is the product of successive Frobenius images of the generator.
The checker computes `x^p mod C(p,n)` with binary modular exponentiation,
then uses modular composition for each Frobenius step. The product requires
`k` modular multiplications and at most `n` compositions. All replay helpers
are structurally recursive. The complete cost depends on the degree and
characteristic and is measured when selecting the committed scope.

# What is proved

The norm and geometric-exponent identities in the first two displays are
theorems below. The reusable bridges are
`FpPoly.Quotient.reduce_powModMonicLinear_eq_pow`, which identifies the
structural modular power in the quotient, and
`FpPoly.Quotient.Internal.eval_X_eq_reduce`, which says evaluation at the class
of `x` is quotient reduction. Together with
`FpPoly.Quotient.Internal.eval_pow_prime`, they show that every modular
composition in `frobeniusIter` is a Frobenius step.

Consequently `normX_eq_pow` identifies the computed norm representative with
the geometric-sum power in any quotient, and `subfieldGen_eq_norm` rewrites
that exponent as `(p^n - 1) / (p^m - 1)` for `0 < m` and `m ∣ n`.
-/

namespace Hex

namespace Conway

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- `x ^ p` reduced modulo a monic `f`, computed by the structurally recursive
binary modular exponentiation so the kernel can replay it in logarithmically
many modular multiplications. -/
@[expose]
def frobeniusBase (f : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  powMod FpPoly.X f hmonic p

/-- Apply the Frobenius `g ↦ g ^ p` to a residue `k` times, as `k` modular
compositions with `xp = x ^ p mod f`.

Composition rather than exponentiation is the point: `g(x) ^ p = g(x ^ p)` in
characteristic `p`, so one Frobenius step costs a Horner walk over `g`'s
coefficients instead of `p` modular multiplications. -/
@[expose]
def frobeniusIter (f xp : FpPoly p) (hmonic : DensePoly.Monic f) :
    Nat → FpPoly p → FpPoly p
  | 0, g => g
  | k + 1, g => frobeniusIter f xp hmonic k (compose g xp f hmonic)

/-- The norm accumulator: multiply together `k` successive `p^m`-th powers of
the residue of `x`, reducing modulo `f` at each step.

`cur` is `α ^ (p ^ (i m))` on entry to the `i`-th step, and advances by `m`
Frobenius applications. -/
@[expose]
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
@[expose]
def normX (f : FpPoly p) (hmonic : DensePoly.Monic f) (m k : Nat) :
    FpPoly p :=
  normAux f (frobeniusBase f hmonic) hmonic m k 1 FpPoly.X

/-! # The computed norm is the field norm -/

/-- The exponent `1 + q + ⋯ + q^(k-1)`, in a structural-recursion spelling
that follows the norm accumulator. -/
def normExponent (q : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 1 + q * normExponent q k

/-- The executable Frobenius base represents the `p`-th power of the quotient
indeterminate. -/
theorem reduce_frobeniusBase_eq_pow
    {f : FpPoly p} {hmonic : DensePoly.Monic f} {hf_pos : 0 < f.natDegree} :
    FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
        (frobeniusBase f hmonic) =
      (FpPoly.Quotient.X (g := f) (hmonic := hmonic) (hg_pos := hf_pos)) ^ p := by
  unfold frobeniusBase
  rw [powMod_eq]
  exact FpPoly.Quotient.reduce_powModMonicLinear_eq_pow FpPoly.X p

/-- Iterating executable modular composition `k` times represents raising a
quotient element to `p^k`. -/
theorem reduce_frobeniusIter_eq_pow
    {f xp : FpPoly p} {hmonic : DensePoly.Monic f} {hf_pos : 0 < f.natDegree}
    (hxp : FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) xp =
      (FpPoly.Quotient.X (g := f) (hmonic := hmonic) (hg_pos := hf_pos)) ^ p) :
    ∀ (k : Nat) (a : FpPoly p),
      FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
          (frobeniusIter f xp hmonic k a) =
        (FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) a) ^
          (p ^ k)
  | 0, a => by
      change FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) a =
        FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) a ^ 1
      rw [show (1 : Nat) = 0 + 1 from rfl, FpPoly.Quotient.pow_succ,
        FpPoly.Quotient.pow_zero,
        FpPoly.Quotient.one_mul]
  | k + 1, a => by
      rw [frobeniusIter, reduce_frobeniusIter_eq_pow hxp k]
      have hstep :
          FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
              (compose a xp f hmonic) =
            (FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) a) ^ p := by
        rw [compose_eq, ← FpPoly.Quotient.eval_reduce_eq_reduce_composeModMonicImpl, hxp,
          FpPoly.Quotient.Internal.eval_pow_prime,
          FpPoly.Quotient.Internal.eval_X_eq_reduce]
      rw [hstep, FpPoly.Quotient.pow_mul, Nat.pow_succ, Nat.mul_comm p]

/-- The norm accumulator represents its initial accumulator multiplied by the
geometric sequence of Frobenius powers of its initial current value. -/
theorem reduce_normAux_eq_pow
    {f : FpPoly p} {hmonic : DensePoly.Monic f} {hf_pos : 0 < f.natDegree}
    (m : Nat) : ∀ (k : Nat) (acc cur : FpPoly p),
      FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
          (normAux f (frobeniusBase f hmonic) hmonic m k acc cur) =
        FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) acc *
          (FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) cur) ^
            normExponent (p ^ m) k
  | 0, acc, cur => by
      rw [normAux, normExponent, FpPoly.Quotient.pow_zero, FpPoly.Quotient.mul_one]
  | k + 1, acc, cur => by
      rw [normAux, reduce_normAux_eq_pow m k]
      have hacc :
          FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
              (FpPoly.modByMonic f (acc * cur) hmonic) =
            FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
              (acc * cur) := by
        apply FpPoly.Quotient.ext
        simp [FpPoly.Quotient.reduce_val, FpPoly.modByMonic,
          DensePoly.modByMonic_eq_mod]
      rw [hacc, FpPoly.Quotient.reduce_mul,
        reduce_frobeniusIter_eq_pow reduce_frobeniusBase_eq_pow,
        FpPoly.Quotient.pow_mul]
      change (_ * _) * _ = _ * _ ^ (1 + p ^ m * normExponent (p ^ m) k)
      rw [FpPoly.Quotient.mul_assoc]
      apply congrArg (fun z =>
        FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos) acc * z)
      calc
        FpPoly.Quotient.reduce cur *
              FpPoly.Quotient.reduce cur ^ (p ^ m * normExponent (p ^ m) k) =
            FpPoly.Quotient.reduce cur ^ 1 *
              FpPoly.Quotient.reduce cur ^ (p ^ m * normExponent (p ^ m) k) := by
                congr 1
                change _ = _ ^ (0 + 1)
                rw [FpPoly.Quotient.pow_succ, FpPoly.Quotient.pow_zero,
                  FpPoly.Quotient.one_mul]
        _ = FpPoly.Quotient.reduce cur ^
              (1 + p ^ m * normExponent (p ^ m) k) :=
            (FpPoly.Quotient.pow_add _ _ _).symm

/-- The quotient class of `normX` is the geometric-sum power of the quotient
indeterminate. -/
theorem normX_eq_pow
    {f : FpPoly p} {hmonic : DensePoly.Monic f} {hf_pos : 0 < f.natDegree}
    (m k : Nat) :
    FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
        (normX f hmonic m k) =
      (FpPoly.Quotient.X (g := f) (hmonic := hmonic) (hg_pos := hf_pos)) ^
        normExponent (p ^ m) k := by
  rw [normX, reduce_normAux_eq_pow]
  change (1 : FpPoly.Quotient f hmonic hf_pos) * _ = _
  rw [FpPoly.Quotient.one_mul,
    show FpPoly.Quotient.reduce (g := f) (hmonic := hmonic) (hg_pos := hf_pos)
        FpPoly.X = FpPoly.Quotient.X from rfl]

/-- The structural geometric exponent is the usual geometric-series quotient. -/
theorem normExponent_eq_div {q : Nat} (hq : 1 < q) (k : Nat) :
    normExponent q k = (q ^ k - 1) / (q - 1) := by
  have hpow : ∀ j : Nat, q ^ j = (q - 1) * normExponent q j + 1 := by
    intro j
    induction j with
    | zero => simp [normExponent]
    | succ j ih =>
        rw [Nat.pow_succ, ih, normExponent]
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
        calc
          ((q - 1) * normExponent q j + 1) * q =
              (q - 1) * (normExponent q j * q) + q := by
                rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          _ = (q - 1) * (normExponent q j * q) + ((q - 1) + 1) := by rw [hqsub]
          _ = (q - 1) * (normExponent q j * q) + (q - 1) + 1 := by
                rw [Nat.add_assoc]
          _ = (q - 1) * (normExponent q j * q) + (q - 1) * 1 + 1 := by
                rw [Nat.mul_one]
          _ = (q - 1) * (normExponent q j * q + 1) + 1 := by rw [Nat.mul_add]
          _ = (q - 1) * (1 + q * normExponent q j) + 1 := by
                rw [Nat.add_comm (normExponent q j * q) 1,
                  Nat.mul_comm (normExponent q j) q]
  have hsub : q ^ k - 1 = (q - 1) * normExponent q k := by
    rw [hpow k, Nat.add_sub_cancel]
  rw [hsub]
  exact (Nat.mul_div_cancel_left (normExponent q k) (by omega)).symm

/-- The Tier 2 compatibility check for a committed pair of entries: is the norm
of `α` down to the degree-`m` subfield a root of `C(p, m)`?

`fm` is the smaller modulus, `fn` the larger, and `k = n / m`. Evaluating `fm`
at the norm is exactly a modular composition. -/
@[expose]
def compatCheck (fm fn : FpPoly p) (hmonic : DensePoly.Monic fn)
    (m k : Nat) : Bool :=
  compose fm (normX fn hmonic m k) fn hmonic == 0

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
    0 < (conwayPoly p n hn).natDegree :=
  conwayPoly_nonconstant p n hn

/-! # What compatibility says about field elements

The `Bool` above is what `decide` can run. This section says what it means:
the norm really is an element of `F_p[x] / (C(p, n))`, and `C(p, m)` really
vanishes on it.
-/

/-- The generator of the canonical degree-`m` subfield of
`F_p[x] / (C(p, n))`, as an element of the quotient rather than as a
representative: the class of the norm of `x`. -/
@[expose]
def subfieldGen (p m n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hn : SupportedEntry p n) :
    FpPoly.Quotient (conwayPoly p n hn) (conwayPoly_monic p n hn)
      (conwayPoly_degree_pos p n hn) :=
  FpPoly.Quotient.reduce
    (normX (conwayPoly p n hn) (conwayPoly_monic p n hn) m (n / m))

/-- The canonical subfield generator is the field norm of the ambient Conway
generator.

The positivity assumption excludes the meaningless degree-zero denominator;
divisibility identifies `p ^ (m * (n / m))` with `p ^ n`. -/
theorem subfieldGen_eq_norm
    {p m n : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hn : SupportedEntry p n) (hm_pos : 0 < m) (hmn : m ∣ n) :
    subfieldGen p m n hn =
      (FpPoly.Quotient.X
        (g := conwayPoly p n hn) (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn)) ^
          ((p ^ n - 1) / (p ^ m - 1)) := by
  unfold subfieldGen
  rw [normX_eq_pow]
  have hp : 1 < p := by
    have hp_two := (ZMod64.PrimeModulus.prime (p := p)).two_le
    omega
  rw [normExponent_eq_div (Nat.one_lt_pow (Nat.ne_of_gt hm_pos) hp)]
  have hpow : (p ^ m) ^ (n / m) = p ^ n := by
    rw [← Nat.pow_mul, Nat.mul_comm m, Nat.div_mul_cancel hmn]
  rw [hpow]

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
  change (compose _ _ _ _ == 0) = true at hcompat
  rw [compose_eq] at hcompat
  exact beq_iff_eq.mp hcompat

/-- The explicit finite-field norm power is a root of the smaller Conway
polynomial. -/
theorem eval_norm_eq_zero
    {p m n : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hm : SupportedEntry p m) (hn : SupportedEntry p n)
    (hcompat : Compatible p m n hm hn) (hm_pos : 0 < m) (hmn : m ∣ n) :
    FpPoly.Quotient.Internal.eval
        (g := conwayPoly p n hn) (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn)
        (conwayPoly p m hm)
        ((FpPoly.Quotient.X
          (g := conwayPoly p n hn) (hmonic := conwayPoly_monic p n hn)
          (hg_pos := conwayPoly_degree_pos p n hn)) ^
            ((p ^ n - 1) / (p ^ m - 1))) =
      FpPoly.Quotient.zero (g := conwayPoly p n hn)
        (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn) := by
  rw [← subfieldGen_eq_norm hn hm_pos hmn]
  exact eval_conwayPoly_subfieldGen_eq_zero hm hn hcompat

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


end Conway
end Hex
