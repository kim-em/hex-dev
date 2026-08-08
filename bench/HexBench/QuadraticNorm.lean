/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Lean.Data.Json

/-!
# Iterated quadratic norms and their irreducibility certificates

Measurement support for issue #9133's go/no-go gate. Nothing here is reachable
from `Hex.ZPoly.factorize`; this is the prototype the gate is decided against,
kept outside the production cascade until the Mathlib correspondence exists.

**The construction.** For `d : ℤ` and monic `g ∈ ℤ[X]`, the *quadratic norm*
`N_d(g)` is the norm of `g(X - t)` along `ℤ[t]/(t² - d) → ℤ`, that is,
`N_d(g)(X) = g(X - t) * g(X + t)` with `t² = d`. It is again a monic integer
polynomial, `deg N_d(g) = 2 * deg g`, and its roots are `β ± √d` as `β` runs
over the roots of `g`. Iterating from `X - c` gives `F(c; d₁, …, dₙ)`, the
product of `X - c - ∑ᵢ εᵢ √dᵢ` over all `2ⁿ` sign patterns `ε ∈ {±1}ⁿ`.

**The certificate.** A `Certificate` is the translation `c` together with the
radicands `d₁, …, dₙ`. `Certificate.check` verifies two things: *independence*,
that no nonempty subproduct of the radicands is a perfect square, which is
exactly multiplicative independence of the `dᵢ` in `ℚ*/(ℚ*)²`; and
*identification*, that `F(c; d)` equals the input polynomial coefficientwise.

Together those imply `f` is irreducible: independence forces
`[ℚ(√d₁, …, √dₙ) : ℚ] = 2ⁿ`, the element `c + ∑ᵢ √dᵢ` generates that field, and
`F(c; d)` is its minimal polynomial. The Mathlib side of that implication is not
in this file; `reports/hexbz-quadratic-norm-certificate.md` carries the proof
and what a production version would have to discharge.

The independence check needs no factorization of the radicands: an integer is a
rational square exactly when it is a perfect square, so `2ⁿ - 1` integer square
tests settle it. That, with the polynomial identity, is the whole arithmetic
trust surface of the check.

**Recovery.** The search side may be arbitrary, since the check is what carries
the weight, but a closed form is available and is what this file uses. Summing
`exp(t αₑ)` over all sign patterns gives `2ⁿ * ∏ᵢ cosh(t √dᵢ)`, so writing `p_k`
for the power sums of the roots of the centred polynomial and
`u_k = p_{2k} / (2ⁿ (2k)!)`, the series `∑_k u_k sᵏ` equals `∏ᵢ C(dᵢ s)` where
`C(z) = cosh √z = ∑_j zʲ/(2j)!`. Taking logarithms turns that product into a
sum, and `[sᵏ] log C(z) = γ_k` is a nonzero rational independent of the input,
so `∑ᵢ dᵢᵏ = ([sᵏ] log ∑_k u_k sᵏ) / γ_k`. Newton's identities then recover the
`dᵢ` as the integer roots of one degree-`n` polynomial. Every step reads only
the top `2n + 1` coefficients of `f` and is exact rational arithmetic.
-/

namespace HexBench.QuadraticNorm

/-! # Dense integer polynomials

Ascending coefficient arrays: `p[i]` is the coefficient of `Xⁱ`. -/

/-- Drop trailing zero coefficients. -/
def trim (p : Array Int) : Array Int := Id.run do
  let mut q := p
  for _ in [0:p.size] do
    if q.size > 1 && q[q.size - 1]! == 0 then q := q.pop else break
  return q

/-- `p(X + c)`, by the in-place synthetic Taylor shift. -/
def shift (p : Array Int) (c : Int) : Array Int := Id.run do
  let n := p.size
  let mut q := p
  if n ≤ 1 then return q
  for i in [0:n-1] do
    for k in [0:n-1-i] do
      let j := n - 2 - k
      q := q.set! j (q[j]! + c * q[j+1]!)
  return q

/-- `N_d(g)` for monic `g`, computed in `ℤ[t]/(t² - d)`.

`g(X - t)` is formed by the same synthetic shift with the shift constant `-t`,
carried as a pair `(a, b) ↦ a + b t`; multiplying by the conjugate cancels the
`t` component coefficientwise, so only the rational part is materialized. -/
def quadNorm (d : Int) (g : Array Int) : Array Int := Id.run do
  let n := g.size
  if n ≤ 1 then return g
  -- `ha + hb * t` is `g(X - t)`.
  let mut ha := g
  let mut hb := Array.replicate n (0 : Int)
  for i in [0:n-1] do
    for k in [0:n-1-i] do
      let j := n - 2 - k
      -- `h[j] += (-t) * h[j+1]`, and `(-t)(a + b t) = -b d - a t`.
      let a := ha[j+1]!
      let b := hb[j+1]!
      ha := ha.set! j (ha[j]! - b * d)
      hb := hb.set! j (hb[j]! - a)
  let mut out := Array.replicate (2 * n - 1) (0 : Int)
  for i in [0:n] do
    let ai := ha[i]!
    let bi := hb[i]!
    if ai != 0 || bi != 0 then
      for j in [0:n] do
        out := out.set! (i + j) (out[i+j]! + ai * ha[j]! - bi * hb[j]! * d)
  return out

/-- `F(c; ds) = N_{dₖ}(⋯ N_{d₁}(X - c) ⋯)`. -/
def iteratedNorm (c : Int) (ds : Array Int) : Array Int :=
  ds.foldl (fun g d => quadNorm d g) #[-c, 1]

/-! # The certificate and its check -/

/-- Translation and radicands for one iterated quadratic norm. -/
structure Certificate where
  /-- The translation: the certified polynomial is `∏_ε (X - c - ∑ εᵢ √dᵢ)`. -/
  translation : Int
  /-- The radicands, in the order the norms are taken. -/
  radicands : Array Int
deriving Repr, Inhabited

/-- Is `m` the square of an integer? -/
def isPerfectSquare (m : Int) : Bool :=
  match m with
  | .ofNat n => let r := n.sqrt; r * r == n
  | .negSucc _ => false

/-- Are the radicands multiplicatively independent in `ℚ*/(ℚ*)²`?

Equivalently: is no nonempty subproduct a perfect square? A zero radicand and a
repeated radicand are both rejected by this, as they must be. -/
def independentSquareClasses (ds : Array Int) : Bool := Id.run do
  let n := ds.size
  for mask in [1:2 ^ n] do
    let mut prod : Int := 1
    for i in [0:n] do
      if mask / 2 ^ i % 2 == 1 then prod := prod * ds[i]!
    if isPerfectSquare prod then return false
  return true

/-- Divide out the unit, so that a negated iterated norm is still recognized.

Every `F(c; d)` is monic, and `-1` is a unit of `ℤ[X]`, so `f` and `-f` are
irreducible together. This is the whole normalization the identification needs:
no scaling and no content division, since a primitive integer polynomial with
leading coefficient outside `{1, -1}` is never `± F(c; d)`. -/
def unitNormalize (f : Array Int) : Array Int :=
  let f := trim f
  if f[f.size - 1]! < 0 then f.map (- ·) else f

/-- Does the certificate prove `f` irreducible?

A `true` result asserts both halves: the radicands are independent, and `f` is,
up to the unit `-1`, exactly the iterated quadratic norm they describe. -/
def Certificate.check (cert : Certificate) (f : Array Int) : Bool :=
  independentSquareClasses cert.radicands &&
    trim (iteratedNorm cert.translation cert.radicands) == unitNormalize f

/-! # Recovery

Exact rational arithmetic on the top `2n + 1` coefficients. Nothing below is
trusted: a wrong guess is rejected by `Certificate.check`. -/

/-- Factorials `0!, …, m!`. -/
private def factorials (m : Nat) : Array Nat := Id.run do
  let mut out := #[1]
  for i in [1:m+1] do
    out := out.push (out[i-1]! * i)
  return out

/-- Formal logarithm of a power series with constant term `1`, to degree `m`. -/
private def seriesLog (a : Array Rat) (m : Nat) : Array Rat := Id.run do
  let mut l := Array.replicate (m + 1) (0 : Rat)
  for k in [1:m+1] do
    let mut acc := a[k]! * (k : Rat)
    for j in [1:k] do
      acc := acc - (j : Rat) * l[j]! * a[k-j]!
    l := l.set! k (acc / (k : Rat))
  return l

/-- `γ_k = [w^{2k}] log cosh w` for `k = 1, …, m`; every one is nonzero. -/
private def logCoshCoeffs (m : Nat) : Array Rat :=
  let fact := factorials (2 * m + 1)
  let c := (Array.range (m + 1)).map fun j => (1 : Rat) / (fact[2*j]! : Rat)
  (seriesLog c m).extract 1 (m + 1)

/-- Power sums `p_1, …, p_count` of the roots of monic `f`, by Newton's
identities. -/
private def powerSums (f : Array Int) (count : Nat) : Array Int := Id.run do
  let n := f.size - 1
  let e : Nat → Int := fun k =>
    if k ≤ n then (if k % 2 == 0 then 1 else -1) * f[n - k]! else 0
  let mut p := Array.replicate (count + 1) (0 : Int)
  for k in [1:count+1] do
    let mut acc := (if k % 2 == 1 then 1 else -1) * (k : Int) * e k
    for i in [1:k] do
      acc := acc + (if i % 2 == 1 then 1 else -1) * e i * p[k-i]!
    p := p.set! k acc
  return p

/-- Integer roots of a monic integer polynomial, all of absolute value at most
`bound`; `none` if the search is abandoned. -/
private def integerRoots (coeffs : Array Int) (bound : Nat) : Option (Array Int) := Id.run do
  let mut p := trim coeffs
  let mut out : Array Int := #[]
  for _ in [0:coeffs.size] do
    if p.size ≤ 1 then break
    let const := p[0]!
    if p.size == 2 then
      -- A monic linear factor names its root, so the last one is free. Every
      -- run ends here, and a degree-two input never enters the search at all.
      out := out.push (-const)
      p := #[1]
    else if const == 0 then
      out := out.push 0
      p := p.extract 1 p.size
    else
      let mut hit : Option Int := none
      for r in [1:bound+1] do
        if hit.isNone && const % (r : Int) == 0 then
          for s in [(-1 : Int), 1] do
            if hit.isNone then
              let root := s * (r : Int)
              let mut acc : Int := 0
              for k in [0:p.size] do
                acc := acc * root + p[p.size - 1 - k]!
              if acc == 0 then hit := some root
      match hit with
      | none => return none
      | some root =>
          out := out.push root
          -- Synthetic division by `y - root`.
          let mut q := Array.replicate (p.size - 1) (0 : Int)
          let mut acc : Int := 0
          for k in [0:p.size-1] do
            let i := p.size - 1 - k
            acc := acc + p[i]!
            q := q.set! (i - 1) acc
            acc := acc * root
          p := q
  if p.size == 1 then return some out else return none

/-- Largest radicand magnitude the prototype's integer-root search will chase.

Only the search is capped: a genuine certificate above the cap is declined, not
mis-accepted. -/
def radicandBound : Nat := 1 <<< 20

/-- Recover the certificate `f` would satisfy, if any.

Returns `none` as soon as any structural requirement fails, so a polynomial
outside the class is rejected after a few coefficient operations. -/
def recover? (f : Array Int) : Option Certificate := Id.run do
  let f := unitNormalize f
  let deg := f.size - 1
  if deg < 2 then return none
  if f[deg]! != 1 then return none
  -- The degree must be a power of two, `2ⁿ`.
  let n := deg.log2
  if 2 ^ n != deg then return none
  -- The roots sum to `2ⁿ c`.
  if f[deg-1]! % (deg : Int) != 0 then return none
  let c := -(f[deg-1]! / (deg : Int))
  let centred := shift f c
  let p := powerSums centred (2 * n)
  let fact := factorials (2 * n)
  let mut u := #[(1 : Rat)]
  for k in [1:n+1] do
    u := u.push ((p[2*k]! : Rat) / ((deg : Rat) * (fact[2*k]! : Rat)))
  let l := seriesLog u n
  let γ := logCoshCoeffs n
  -- Power sums of the radicands.
  let mut pd := Array.replicate (n + 1) (0 : Rat)
  for k in [1:n+1] do
    pd := pd.set! k (l[k]! / γ[k-1]!)
  -- Newton's identities give the elementary symmetric functions.
  let mut e := #[(1 : Rat)]
  for k in [1:n+1] do
    let mut acc := (0 : Rat)
    for i in [1:k+1] do
      acc := acc + (if i % 2 == 1 then 1 else -1) * e[k-i]! * pd[i]!
    e := e.push (acc / (k : Rat))
  -- `∏ᵢ (y - dᵢ) = ∑_k (-1)ᵏ e_k y^{n-k}`, ascending.
  let mut coeffs : Array Int := #[]
  for j in [0:n+1] do
    let v := (if (n - j) % 2 == 0 then 1 else -1) * e[n-j]!
    if v.den != 1 then return none
    coeffs := coeffs.push v.num
  -- `∑ dᵢ²` bounds every `|dᵢ|`. With a single radicand the search never runs
  -- -- the degree-one factor names its root -- so neither the bound nor its cap
  -- is consulted, and `pd` has no second entry to consult them with.
  let mut bound := 0
  if 1 < n then
    let squares := pd[2]!
    if squares.den != 1 || squares.num < 0 then return none
    bound := squares.num.toNat.sqrt
    if bound > radicandBound then return none
  match integerRoots coeffs bound with
  | none => return none
  | some ds =>
      if ds.size != n then return none
      return some { translation := c, radicands := ds }

/-- Recover a certificate and check it. This is the whole prototype pipeline:
`some cert` means `f` is a certified-irreducible iterated quadratic norm. -/
def certify? (f : Array Int) : Option Certificate :=
  match recover? f with
  | none => none
  | some cert => if cert.check f then some cert else none

end HexBench.QuadraticNorm
