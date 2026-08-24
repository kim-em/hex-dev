/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Subresultant
public meta import HexResultant.Subresultant

public section

/-!
Extended Brown subresultant chains.

The worker in this file follows exactly the same Brown recurrence and zero
conventions as `subresultantChain`.  In addition to each stored polynomial it
carries the two transformation cofactors expressing that polynomial in terms
of the caller's inputs.  Keeping this extension beside the original worker
lets integer and multivariate gcd consumers share both the sign convention and
the exact-scalar bookkeeping.
-/

namespace Hex

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

namespace SubresultantExt

/-- One extended Brown-chain entry `(u, v, s)`, representing `u*f + v*g = s`.
-/
abbrev Entry (R : Type u) [Zero R] [DecidableEq R] :=
  DensePoly R × DensePoly R × DensePoly R

/-- The polynomial component of an extended Brown-chain entry. -/
@[inline, expose]
def value (e : Entry R) : DensePoly R := e.2.2

/-- The numerator update for one transformation cofactor in a pseudo-division
step: `lc(curr)^d * prevCofactor - quotient * currCofactor`. -/
@[inline, expose]
def numerator [Add R] [Mul R] [Sub R]
    (a : R) (q prev curr : DensePoly R) :
    DensePoly R :=
  scaleImpl a prev - q * curr

end SubresultantExt

open SubresultantExt

/-- Fuel-bounded extended Brown recurrence after the initial pseudo-division.

The polynomial branch decisions and polynomial successor are byte-for-byte the
same expressions used by `subresultantAux`; the additional divisions update
only the two transformation cofactors. -/
@[expose]
def subresultantAuxExt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R)
    (prevU prevV currU currV : DensePoly R)
    (chain : Array (Entry R)) : Nat → Array (Entry R)
  | 0 => chain
  | fuel + 1 =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let qr := pseudoDivMod prev curr
      let q := qr.1
      let p := qr.2
      if p.isZero then
        chain
      else
        let divisor :=
          negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
        let next := divScalarImpl p divisor
        if next.isZero then
          chain
        else
          let a := powNat curr.leadingCoeff (delta + 1)
          let nextU := divScalarImpl (numerator a q prevU currU) divisor
          let nextV := divScalarImpl (numerator a q prevV currV) divisor
          subresultantAuxExt curr next hCurr currU currV nextU nextV
            (chain.push (nextU, nextV, next)) fuel

/-- Extended Brown recurrence for two nonzero, degree-ordered inputs, supplied
with their transformation cofactors relative to the caller's inputs. -/
@[expose]
def subresultantOrderedExt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g fU fV gU gV : DensePoly R) : Array (Entry R) :=
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let qr := pseudoDivMod f g
  let q := qr.1
  let p := qr.2
  let seed := #[(fU, fV, f), (gU, gV, g)]
  if p.isZero then
    seed
  else
    let sign := negOnePow (delta + 1)
    let g₃ := scaleImpl sign p
    if g₃.isZero then
      seed
    else
      let a := powNat g.leadingCoeff (delta + 1)
      let g₃U := scaleImpl sign (numerator a q fU gU)
      let g₃V := scaleImpl sign (numerator a q fV gV)
      subresultantAuxExt g g₃ h₂ gU gV g₃U g₃V
        (seed.push (g₃U, g₃V, g₃)) (g.size + 1)

/-- Brown's nonzero subresultant chain together with a caller-order-sensitive
Bezout representation for every stored entry.

Zero inputs follow `subresultantChain`: they are omitted, and the one remaining
input receives its evident unit cofactor.  Two nonzero inputs are ordered by
decreasing dense degree; equal-degree inputs retain caller order. -/
@[expose]
def subresultantChainExt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : Array (DensePoly R × DensePoly R × DensePoly R) :=
  if f.isZero then
    if g.isZero then #[] else #[(0, 1, g)]
  else if g.isZero then
    #[(1, 0, f)]
  else if f.size < g.size then
    subresultantOrderedExt g f 0 1 1 0
  else
    subresultantOrderedExt f g 1 0 0 1

/-- Projecting an extended worker result to its polynomial components gives
the original Brown worker result. -/
private theorem subresultantAuxExt_values [One R] [Add R] [Sub R] [Mul R]
    [Div R] (prev curr : DensePoly R) (hPrev : R)
    (prevU prevV currU currV : DensePoly R)
    (chain : Array (Entry R)) (plain : Array (DensePoly R)) (fuel : Nat)
    (hchain : chain.map value = plain) :
    (subresultantAuxExt prev curr hPrev prevU prevV currU currV chain fuel).map
        value =
      (subresultantAux prev curr hPrev plain fuel).chain := by
  induction fuel generalizing prev curr hPrev prevU prevV currU currV chain plain with
  | zero =>
      simpa [subresultantAuxExt, subresultantAux] using hchain
  | succ fuel ih =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let qr := pseudoDivMod prev curr
      let q := qr.1
      let p := qr.2
      cases hp : p.isZero with
      | true =>
          simpa [subresultantAuxExt, subresultantAux, delta, hCurr, qr, q,
            p, hp] using hchain
      | false =>
          let divisor :=
            negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
          let next := divScalarImpl p divisor
          cases hnext : next.isZero with
          | true =>
              simpa [subresultantAuxExt, subresultantAux, delta, hCurr, qr,
                q, p, hp, divisor, next, hnext] using hchain
          | false =>
              let a := powNat curr.leadingCoeff (delta + 1)
              let nextU :=
                divScalarImpl (numerator a q prevU currU) divisor
              let nextV :=
                divScalarImpl (numerator a q prevV currV) divisor
              have hpush :
                  (chain.push (nextU, nextV, next)).map value =
                    plain.push next := by
                simp only [Array.map_push, value]
                rw [hchain]
              have hrec := ih curr next hCurr currU currV nextU nextV
                (chain.push (nextU, nextV, next)) (plain.push next) hpush
              simpa [subresultantAuxExt, subresultantAux, delta, hCurr, qr,
                q, p, hp, divisor, next, hnext, a, nextU, nextV] using hrec

/-- Projecting an extended degree-ordered run gives the existing ordered
Brown chain. -/
private theorem subresultantOrderedExt_values [One R] [Add R] [Sub R] [Mul R]
    [Div R] (f g fU fV gU gV : DensePoly R) :
    (subresultantOrderedExt f g fU fV gU gV).map value =
      (subresultantOrdered f g).chain := by
  unfold subresultantOrderedExt subresultantOrdered subresultantOrderedFuel
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let qr := pseudoDivMod f g
  let q := qr.1
  let p := qr.2
  let seed : Array (Entry R) := #[(fU, fV, f), (gU, gV, g)]
  have hseed : seed.map value = #[f, g] := by
    simp [seed, value]
  cases hp : p.isZero with
  | true =>
      simp [qr, p, hp, value]
  | false =>
      let sign := negOnePow (R := R) (delta + 1)
      let g₃ := scaleImpl sign p
      cases hg₃ : g₃.isZero with
      | true =>
          simp [delta, qr, p, hp, sign, g₃, hg₃, value]
      | false =>
          let a := powNat g.leadingCoeff (delta + 1)
          let g₃U := scaleImpl sign (numerator a q fU gU)
          let g₃V := scaleImpl sign (numerator a q fV gV)
          have hseed₃ :
              (seed.push (g₃U, g₃V, g₃)).map value = #[f, g, g₃] := by
            simp [seed, value]
          have haux := subresultantAuxExt_values g g₃ h₂ gU gV g₃U g₃V
            (seed.push (g₃U, g₃V, g₃)) #[f, g, g₃] (g.size + 1)
            hseed₃
          simpa [delta, h₂, qr, q, p, seed, hp, sign, g₃, hg₃, a,
            g₃U, g₃V] using haux

/-- Forgetting the two cofactors recovers `subresultantChain`, including its
input ordering and all zero-input conventions. -/
theorem subresultantChainExt_values [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) :
    (subresultantChainExt f g).map SubresultantExt.value =
      subresultantChain f g := by
  unfold subresultantChainExt subresultantChain subresultantRun
  cases hf : f.isZero with
  | true =>
      cases hg : g.isZero with
      | true => simp
      | false => simp [SubresultantExt.value]
  | false =>
      cases hg : g.isZero with
      | true => simp [SubresultantExt.value]
      | false =>
          by_cases hfg : f.size < g.size
          · simpa [hf, hg, hfg] using
              subresultantOrderedExt_values g f (0 : DensePoly R) 1 1 0
          · simpa [hf, hg, hfg] using
              subresultantOrderedExt_values f g (1 : DensePoly R) 0 0 1

namespace SubresultantExt

/-- Brown's accumulated principal-subresultant scale associated to a stored
chain entry.  The value at index `1` is the ordered worker's initial `h₂`;
later values apply the unchanged `divExp` recurrence. -/
def brownScale [One R] [Mul R] [Div R] (chain : Array (Entry R)) : Nat → R
  | 0 => 1
  | 1 =>
      let first := value (chain.getD 0 (0, 0, 0))
      let second := value (chain.getD 1 (0, 0, 0))
      powNat second.leadingCoeff (first.size - second.size)
  | i + 2 =>
      let prev := value (chain.getD (i + 1) (0, 0, 0))
      let curr := value (chain.getD (i + 2) (0, 0, 0))
      divExp curr.leadingCoeff (brownScale chain (i + 1))
        (prev.size - curr.size)

/-- Exact coefficientwise divisibility at a noninitial Brown step.

Index `2` is the signed first pseudo-remainder and involves no exact scalar
division.  Every entry at index at least `3` is obtained from the two preceding
entries by the scalar division recorded here. -/
def CofactorStep [One R] [Add R] [Sub R] [Mul R] [Div R]
    (chain : Array (Entry R)) (i : Nat) : Prop :=
  let prev := chain.getD (i - 2) (0, 0, 0)
  let curr := chain.getD (i - 1) (0, 0, 0)
  let next := chain.getD i (0, 0, 0)
  let delta := (value prev).size - (value curr).size
  let a := powNat (value curr).leadingCoeff (delta + 1)
  let q := (pseudoDivMod (value prev) (value curr)).1
  let divisor :=
    negOnePow (delta + 1) * (value prev).leadingCoeff *
      powNat (brownScale chain (i - 2)) delta
  numerator a q prev.1 curr.1 = scale divisor next.1 ∧
    numerator a q prev.2.1 curr.2.1 = scale divisor next.2.1

/-- Algebraic contract of an extended Brown chain: every stored triple is a
Bezout identity for the caller's inputs, and every post-initial transformation
row is coefficientwise divisible by the exact Brown scalar before division. -/
def Law [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) (chain : Array (Entry R)) : Prop :=
  (∀ e, e ∈ chain → e.1 * f + e.2.1 * g = value e) ∧
    ∀ i, 3 ≤ i → i < chain.size → CofactorStep chain i

end SubresultantExt

/-- The extended Brown recurrence has exact transformation rows and every
stored entry satisfies its caller-order-sensitive Bezout identity. -/
theorem subresultantChainExt_law {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) :
    SubresultantExt.Law f g (subresultantChainExt f g) := by
  sorry

/-- Every extended-chain entry reconstructs from the two caller inputs. -/
theorem subresultantChainExt_bezout {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (e : SubresultantExt.Entry S)
    (he : e ∈ subresultantChainExt f g) :
    e.1 * f + e.2.1 * g = e.2.2 :=
  (subresultantChainExt_law f g).1 e he

/-- At every divided Brown step, both transformation numerators reconstruct
as the Brown scalar times the stored executable quotients. -/
theorem subresultantChainExt_exact {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (i : Nat) (hi : 3 ≤ i)
    (hbound : i < (subresultantChainExt f g).size) :
    SubresultantExt.CofactorStep (subresultantChainExt f g) i :=
  (subresultantChainExt_law f g).2 i hi hbound

/-! # Core executable pins -/

-- A four-entry defective chain exercises both transformation-row divisions.
#guard
  let f : DensePoly Int := ofList [0, 0, 0, 0, -1]
  let g : DensePoly Int := ofList [-1, 0, 0, 2]
  let ext := subresultantChainExt f g
  ext.size = 4 &&
    ext.map SubresultantExt.value = subresultantChain f g &&
    ext.all fun e => e.1 * f + e.2.1 * g = e.2.2

-- Caller-sensitive cofactors survive degree ordering and the zero wrappers.
#guard
  let linear : DensePoly Int := ofList [1, 1]
  let quadratic : DensePoly Int := ofList [1, 0, 1]
  let reversed := subresultantChainExt linear quadratic
  reversed.getD 0 (0, 0, 0) = (0, 1, quadratic) &&
    reversed.getD 1 (0, 0, 0) = (1, 0, linear) &&
    subresultantChainExt (0 : DensePoly Int) linear = #[(0, 1, linear)] &&
    subresultantChainExt linear 0 = #[(1, 0, linear)] &&
    subresultantChainExt (0 : DensePoly Int) 0 = #[]

end DensePoly
end Hex
