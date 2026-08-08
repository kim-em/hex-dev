/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.QuadraticNorm

public section

/-!
# Recovering an iterated-quadratic-norm certificate

{name}`Hex.QuadraticNormCertificate.check` is the trusted half: it decides, by
integer arithmetic alone, whether a translation and a list of radicands prove
its input irreducible. This module is the *untrusted* half, the search that
proposes the pair. Nothing here carries a proof obligation, because a wrong
proposal dies in the check; the only thing the search owes is that it is cheap
when it is going to fail.

**The closed form.** Summing `exp(t·α_ε)` over the `2ⁿ` sign patterns gives
`2ⁿ · ∏ᵢ cosh(t√dᵢ)`, so writing `p_k` for the power sums of the roots of the
centred polynomial `f(X + c)` and `u_k = p_{2k} / (2ⁿ · (2k)!)`, the series
`∑_k u_k sᵏ` equals `∏ᵢ C(dᵢ·s)` with `C(z) = cosh √z = ∑_j zʲ/(2j)!`. Taking
logarithms turns the product into a sum: the coefficient of `sᵏ` in
`log C(z)` is a nonzero rational `γ_k` independent of the input, so writing
`L_k` for the coefficient of `sᵏ` in `log ∑_k u_k sᵏ`,

    ∑ᵢ dᵢᵏ = L_k / γ_k,   k = 1, …, n.

Newton's identities turn those power sums into `∏ᵢ (y - dᵢ)`, whose integer
roots are the radicands. Every step is exact rational arithmetic on the top
`2n + 1` coefficients of `f`, and `∑ᵢ dᵢ²` bounds each `|dᵢ|`, which bounds the
root search.

**Failing cheaply.** A polynomial outside the class is refused at the first
structural test it meets: degree not a power of two, a leading coefficient
outside `{1, -1}`, `2ⁿ ∤ a_{N-1}`, a non-integral intermediate, a radicand
bound past `radicandBound`, or too few
integer roots. Most of a factorization corpus dies at the degree test.
-/

namespace Hex

namespace NormRecovery

/-- `p(X + c)` for a dense ascending coefficient array, by the synthetic Taylor
shift. -/
@[expose]
def taylorShift (p : Array Int) (c : Int) : Array Int := Id.run do
  let n := p.size
  let mut q := p
  if n ≤ 1 then return q
  for i in [0:n-1] do
    for k in [0:n-1-i] do
      let j := n - 2 - k
      q := q.set! j (q[j]! + c * q[j+1]!)
  return q

/-- The factorials `0!, …, m!`. -/
@[expose]
def factorials (m : Nat) : Array Nat := Id.run do
  let mut out := #[1]
  for i in [1:m+1] do
    out := out.push (out[i-1]! * i)
  return out

/-- The formal logarithm of a power series with constant term `1`, to degree `m`. -/
@[expose]
def seriesLog (a : Array Rat) (m : Nat) : Array Rat := Id.run do
  let mut l := Array.replicate (m + 1) (0 : Rat)
  for k in [1:m+1] do
    let mut acc := a[k]! * (k : Rat)
    for j in [1:k] do
      acc := acc - (j : Rat) * l[j]! * a[k-j]!
    l := l.set! k (acc / (k : Rat))
  return l

/-- `γ_k = [w^{2k}] log cosh w` for `k = 1, …, m`; every one is nonzero. -/
@[expose]
def logCoshCoeffs (m : Nat) : Array Rat :=
  let fact := factorials (2 * m + 1)
  let c := (Array.range (m + 1)).map fun j => (1 : Rat) / (fact[2*j]! : Rat)
  (seriesLog c m).extract 1 (m + 1)

/-- The power sums `p_1, …, p_count` of the roots of a monic dense integer
polynomial, by Newton's identities. -/
@[expose]
def powerSums (f : Array Int) (count : Nat) : Array Int := Id.run do
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

/-- The integer roots of a monic dense integer polynomial, all of absolute value
at most `bound`; `none` when the search is abandoned. -/
@[expose]
def integerRoots (coeffs : Array Int) (bound : Nat) : Option (Array Int) := Id.run do
  let mut p := coeffs
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

end NormRecovery

namespace QuadraticNormCertificate

open NormRecovery

/-- The largest radicand magnitude the integer-root search will chase.

Only the search is capped: a genuine certificate above the cap is declined, not
mis-accepted. -/
@[expose]
def radicandBound : Nat := 1 <<< 20

/-- Recover the certificate `f` would satisfy, if any.

Returns `none` as soon as any structural requirement fails, so a polynomial
outside the class is refused after a few coefficient operations. A `some`
result is a *proposal*: {name}`Hex.QuadraticNormCertificate.check` is what
decides it. -/
@[expose]
def recover? (f : ZPoly) : Option QuadraticNormCertificate := Id.run do
  let f := (ZPoly.normalizePrimitiveSign f).toArray
  if f.size < 3 then return none
  let deg := f.size - 1
  if f[deg]! != 1 then return none
  -- The degree must be a power of two, `2ⁿ`.
  let n := deg.log2
  if 2 ^ n != deg then return none
  -- The roots sum to `2ⁿ c`.
  if f[deg-1]! % (deg : Int) != 0 then return none
  let c := -(f[deg-1]! / (deg : Int))
  let centred := taylorShift f c
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
  -- `∑ᵢ dᵢ²` bounds every `|dᵢ|`. With a single radicand the search never runs
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

/-- Modular support width at or above which the certificate is attempted.

Recombination at width `w` walks up to `2 ^ (w - 1)` supports, so the gate is
stated as a width rather than as a node count: at the floor the walk is
`2 ^ 15 = 32768` nodes, an eighth of the `Hex.defaultSubsetBudget` the
recombination already carries, and it is the cost of that walk the certificate
is worth attempting to replace. Below the floor a row pays exactly nothing,
because nothing is constructed.

The floor is deliberately *not* `defaultSubsetBudget` itself. A width-16 walk
sits far under that budget and would never trip it, yet width 16 is where the
walk first costs tens of milliseconds -- three orders of magnitude above the
worst measured cost of a certificate that fails to apply. -/
@[expose]
def widthFloor : Nat := 16

/-- Recover a certificate for `f` and check it.

`some cert` means `cert.check f = true`, so `f` is a certified-irreducible
iterated quadratic norm; `none` carries no claim either way. -/
@[expose]
def certify? (f : ZPoly) : Option QuadraticNormCertificate :=
  match recover? f with
  | some cert => if cert.check f then some cert else none
  | none => none

/-- A recovered certificate has passed its own check: this is the only property
of the search anything downstream may use. -/
theorem check_of_certify? {f : ZPoly} {cert : QuadraticNormCertificate}
    (h : certify? f = some cert) : cert.check f = true := by
  unfold certify? at h
  cases hrec : recover? f with
  | none => rw [hrec] at h; exact absurd h (by simp)
  | some proposal =>
      rw [hrec] at h
      by_cases hcheck : proposal.check f = true
      · simp only [hcheck, if_true] at h
        rw [← Option.some.inj h]
        exact hcheck
      · simp only [Bool.not_eq_true] at hcheck
        simp [hcheck] at h

end QuadraticNormCertificate

/-- Does the budget-gated iterated-quadratic-norm certificate prove `core`
irreducible?

`width` is the number of modular factors, known once the modular factorization
is in hand. Below {name}`Hex.QuadraticNormCertificate.widthFloor` the answer is
`false` with nothing constructed, so a row that recombines cheaply pays nothing
for the attempt. Above it, {name}`Hex.QuadraticNormCertificate.recover?`
proposes a translation and radicands and
{name}`Hex.QuadraticNormCertificate.check` decides them; a failure at either
step is an ordinary `false` carrying no state.

**Normalization.** Every `F(c; d)` is monic, so the certificate applies to
`core` exactly when `core` has leading coefficient `1` or `-1`, and the only
normalization is negation: `-1` is a unit of `ℤ[X]`, so `core` and `-core` are
irreducible together. There is no scaling and no content division, because a
primitive integer polynomial with leading coefficient outside `{1, -1}` is
never `± F(c; d)`; {name}`Hex.ZPoly.normalizePrimitiveSign`, inside the check,
is that negation and nothing else. -/
@[expose]
def quadraticNormCertified (core : ZPoly) (width : Nat) : Bool :=
  QuadraticNormCertificate.widthFloor ≤ width &&
    (QuadraticNormCertificate.certify? core).isSome

end Hex
