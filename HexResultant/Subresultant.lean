/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Basic
public import HexResultant.ExactDiv
public meta import HexResultant.ExactDiv
public meta import HexPoly.Dense
public meta import HexPoly.Euclid.DivGcd
public meta import HexPoly.Operations

public section

/-!
Brown's exact subresultant pseudo-remainder sequence.

The worker stores only nonzero PRS terms. Its separate `scale` field is the
corrected principal subresultant `h`; when the terminal polynomial is constant,
that field rather than the polynomial's constant coefficient is the resultant.
Fuel makes the operations-only implementation total. On a lawful exact-division
domain, strict degree descent reaches the terminal pseudo-remainder before fuel
is exhausted.
-/
namespace Hex

universe u

/-- Executable result of an ordered Brown PRS run. -/
structure PRSResult (R : Type u) [Zero R] [DecidableEq R] where
  /-- Brown's nonzero `G₁, …, Gₖ`, excluding the generated terminal zero. -/
  chain : Array (DensePoly R)
  /-- Corrected terminal principal-subresultant scalar `hₖ`. -/
  scale : R

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- The ring element `(-1)^n`, expressed using only `Zero`, `One`, and `Sub`. -/
@[expose]
def negOnePow [One R] [Sub R] (n : Nat) : R :=
  if n % 2 = 0 then 1 else 0 - 1

/-- Fuel-bounded Brown recurrence after the initial pseudo-division.

`prev`, `curr`, and `hPrev` are `Gᵢ₋₁`, `Gᵢ`, and `hᵢ₋₁`. A valid
state has nonzero adjacent polynomials of strictly decreasing degree and a
nonzero scale. The zero checks preserve the public nonzero-only chain
convention even on junk coefficient structures. -/
@[expose]
def subresultantAux [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R) (chain : Array (DensePoly R)) :
    Nat → PRSResult R
  | 0 => ⟨chain, hPrev⟩
  | fuel + 1 =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      if p.isZero then
        ⟨chain, hCurr⟩
      else
        let divisor := negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
        let next := divScalarImpl p divisor
        if next.isZero then
          ⟨chain, hCurr⟩
        else
          subresultantAux curr next hCurr (chain.push next) fuel

/-- Brown's recurrence for two nonzero inputs already ordered by decreasing
dense degree. -/
@[expose]
def subresultantOrdered [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : PRSResult R :=
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  if p.isZero then
    ⟨#[f, g], h₂⟩
  else
    let g₃ := scaleImpl (negOnePow (delta + 1)) p
    if g₃.isZero then
      ⟨#[f, g], h₂⟩
    else
      subresultantAux g g₃ h₂ #[f, g, g₃] (g.size + 1)

/-- Total Brown run. Zero inputs are omitted; two nonzero inputs are ordered by
decreasing dense degree before entering `subresultantOrdered`. -/
@[expose]
def subresultantRun [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : PRSResult R :=
  if f.isZero then
    if g.isZero then ⟨#[], 1⟩ else ⟨#[g], 1⟩
  else if g.isZero then
    ⟨#[f], 1⟩
  else if f.size < g.size then
    subresultantOrdered g f
  else
    subresultantOrdered f g

/-- Brown's nonzero subresultant pseudo-remainder sequence. -/
@[expose]
def subresultantChain [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : Array (DensePoly R) :=
  (subresultantRun f g).chain

/-- Both zero inputs produce the empty nonzero chain. -/
@[simp, grind =]
theorem subresultantChain_zero_zero [One R] [Add R] [Sub R] [Mul R] [Div R] :
    subresultantChain (0 : DensePoly R) 0 = #[] := by
  rfl

/-- A nonzero left input paired with zero is the singleton chain. -/
theorem subresultantChain_zero_right [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f : DensePoly R) (hf : f ≠ 0) : subresultantChain f 0 = #[f] := by
  unfold subresultantChain subresultantRun
  have hfz : f.isZero = false := by
    rw [isZero_eq_false_iff]
    by_cases hpos : 0 < f.size
    · exact hpos
    · exfalso
      apply hf
      apply ext_coeff
      intro i
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le f (by omega)
  have hzz : (0 : DensePoly R).isZero = true := rfl
  simp [hfz, hzz]

/-- Every stored term is nonzero over a lawful exact-division domain. -/
theorem subresultantChain_ne_zero_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (p : DensePoly S) (hp : p ∈ subresultantChain f g) :
    p ≠ 0 := by
  sorry

/-- After the possibly equal-degree ordered inputs, stored degrees strictly
decrease. -/
theorem subresultantChain_strict_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (i : Nat) (hi : 1 ≤ i)
    (hnext : i + 1 < (subresultantChain f g).size) :
    ((subresultantChain f g).getD (i + 1) 0).size <
      ((subresultantChain f g).getD i 0).size := by
  sorry

/-- The nonzero Brown chain stores at most two inputs plus one term for every
possible degree at or below the smaller input degree. -/
theorem subresultantChain_size_le_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hf : f ≠ 0) (hg : g ≠ 0) :
    (subresultantChain f g).size ≤
      min (f.degree?.getD 0) (g.degree?.getD 0) + 2 := by
  sorry

/-! Compiled regression checks for the exact Brown state. -/

-- `X-a`, `X-b` ends in the signed constant `a-b`.
#guard
    let run := subresultantRun
      (ofList ([-2, 1] : List Int)) (ofList ([-5, 1] : List Int))
    run.chain.map (fun p => p.toArray.toList) =
      #[[-2, 1], [-5, 1], [-3]] && run.scale = -3

-- A common linear factor terminates before storing the generated zero.
#guard
    let run := subresultantRun
      (ofList ([-1, 0, 1] : List Int)) (ofList ([-1, 1] : List Int))
    run.chain.map (fun p => p.toArray.toList) =
      #[[-1, 0, 1], [-1, 1]] && run.scale = 1

-- A defective drop: the final polynomial is `4`, but the corrected scale is `16`.
#guard
    let run := subresultantRun
      (ofList ([2, 1, 0, 2, 2] : List Int)) (ofList ([1, 0, 0, 2] : List Int))
    run.chain.map (fun p => p.toArray.toList) =
      #[[2, 1, 0, 2, 2], [1, 0, 0, 2], [4]] && run.scale = 16

-- Both nonunit divisions and the odd sign occur in this defective chain.
#guard
    let run := subresultantRun
      (ofList ([0, 0, 0, 0, -1] : List Int)) (ofList ([-1, 0, 0, 2] : List Int))
    run.chain.map (fun p => p.toArray.toList) =
      #[[0, 0, 0, 0, -1], [-1, 0, 0, 2], [0, -2], [-1]] && run.scale = -1

-- The same defective scale update executes exact division in `DensePoly Int`.
#guard
    let t : DensePoly Int := ofList [0, 1]
    let one : DensePoly Int := 1
    let g : DensePoly (DensePoly Int) := ofList [one, 0, 0, t]
    let f : DensePoly (DensePoly Int) := ofList [one + one, one, 0, t, t]
    let run := subresultantRun f g
    run.chain.size = 3 && run.chain.getD 2 0 = C (t * t) &&
      run.scale = powNat t 4

-- Reversed inputs are degree-ordered; zero inputs are omitted.
#guard
    let linear := ofList ([1, 1] : List Int)
    let quadratic := ofList ([1, 0, 1] : List Int)
    (subresultantChain linear quadratic).getD 0 0 = quadratic &&
      subresultantChain 0 linear = #[linear] &&
      subresultantChain (0 : DensePoly Int) 0 = #[]

end DensePoly
end Hex
