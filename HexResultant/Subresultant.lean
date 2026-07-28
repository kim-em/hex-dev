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

/-- Executable result of a degree-ordered Brown PRS run.

`scale` belongs to the ordered chain. In particular, `subresultantRun` does
not record whether it swapped its arguments, so this structure alone is not a
caller-order-sensitive resultant; use `resultant` for that value. -/
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

/-- The exactness and nonzero obligations for every reachable Brown worker
state. A valid state must terminate naturally before its fuel reaches zero;
the adjacent polynomials have strictly decreasing size, the current and
successor scales are nonzero, both scalar divisions reconstruct their
numerators, the Brown divisor and quotient are nonzero, and the successor is
valid. -/
@[expose]
def BrownLaw [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R) : Nat → Prop
  | 0 => False
  | fuel + 1 =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      prev ≠ 0 ∧ curr ≠ 0 ∧ curr.size < prev.size ∧
        hPrev ≠ 0 ∧ hCurr ≠ 0 ∧
        powNat curr.leadingCoeff delta = powNat hPrev (delta - 1) * hCurr ∧
        if p.isZero then
          True
        else
          let divisor :=
            negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
          let next := divScalar p divisor
          divisor ≠ 0 ∧ p = scale divisor next ∧ next ≠ 0 ∧
            BrownLaw curr next hCurr fuel

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
dense degree, with an explicit proof-audit fuel parameter. -/
@[expose]
def subresultantOrderedFuel [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) (fuel : Nat) : PRSResult R :=
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
      subresultantAux g g₃ h₂ #[f, g, g₃] fuel

/-- Brown's recurrence for two nonzero inputs already ordered by decreasing
dense degree. One fuel unit per possible degree, plus the terminal step, is
sufficient on a lawful exact-division domain. -/
@[expose]
def subresultantOrdered [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : PRSResult R :=
  subresultantOrderedFuel f g (g.size + 1)

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

/-- Ordered nonzero inputs establish every nonzero-denominator and exactness
obligation recorded by `BrownLaw`, including the unreachability of the junk
zero-quotient branch. -/
theorem subresultantOrdered_brownLaw {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hf : f ≠ 0) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let delta := f.size - g.size
    let h₂ := powNat g.leadingCoeff delta
    let p := (pseudoDivMod f g).2
    if p.isZero then
      h₂ ≠ 0
    else
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      g₃ ≠ 0 ∧ BrownLaw g g₃ h₂ (g.size + 1) := by
  sorry

/-- The public ordered-run fuel is sufficient: adding any extra fuel leaves
the result unchanged over a lawful exact-division domain. -/
theorem subresultantOrderedFuel_eq {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hf : f ≠ 0) (hg : g ≠ 0) (hgf : g.size ≤ f.size)
    (extra : Nat) :
    subresultantOrderedFuel f g (g.size + 1 + extra) =
      subresultantOrdered f g := by
  sorry

/-- Extract the resultant value from an ordered nonzero Brown run. The
corrected terminal scale is returned exactly when the last stored term is a
nonzero constant. -/
@[expose]
def resultantOrdered [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : R :=
  let run := subresultantOrdered f g
  let last := run.chain.getD (run.chain.size - 1) 0
  if last.size = 1 then run.scale else 0

/-- Executable polynomial resultant with default formal-degree conventions.

Zero polynomials are treated as degree zero, so two constants (including two
zeros) have resultant one. Reversed nonzero inputs are ordered for the Brown
run and receive the standard degree-product sign. -/
@[expose]
def resultant [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) : R :=
  if f.isZero then
    if g.size ≤ 1 then 1 else 0
  else if g.isZero then
    if f.size ≤ 1 then 1 else 0
  else if f.size < g.size then
    negOnePow ((f.size - 1) * (g.size - 1)) * resultantOrdered g f
  else
    resultantOrdered f g

/-! Compiled regression checks for resultant extraction. -/

-- Linear/quadratic values, including a strict odd-degree reversal whose sign
-- factor is `-1`.
#guard
    let xSub2 := ofList ([-2, 1] : List Int)
    let xSub5 := ofList ([-5, 1] : List Int)
    let xSqAdd1 := ofList ([1, 0, 1] : List Int)
    let xSub1 := ofList ([-1, 1] : List Int)
    let cubic := ofList ([-1, 0, 0, 1] : List Int)
    resultant xSub2 xSub5 = -3 &&
      resultant xSqAdd1 xSub1 = 2 &&
      resultant xSub1 xSqAdd1 = 2 &&
      resultant xSub2 cubic = 7

-- Default formal degrees make zero/constant resultants total.
#guard
    let c2 := C (2 : Int)
    let c3 := C (3 : Int)
    let quadratic := ofList ([1, 0, 1] : List Int)
    resultant 0 0 = (1 : Int) &&
      resultant c2 0 = 1 &&
      resultant quadratic 0 = 0 &&
      resultant quadratic c3 = 9 &&
      resultant c2 c3 = 1 &&
      resultant quadratic 1 = 1

-- Common roots, self-resultants, and both defective Brown drops produce their
-- pinned values.
#guard
    let commonLeft := ofList ([-1, 0, 1] : List Int)
    let commonRight := ofList ([-1, 1] : List Int)
    let defective1 := ofList ([2, 1, 0, 2, 2] : List Int)
    let defective2 := ofList ([1, 0, 0, 2] : List Int)
    let nonunit1 := ofList ([0, 0, 0, 0, -1] : List Int)
    let nonunit2 := ofList ([-1, 0, 0, 2] : List Int)
    resultant commonLeft commonRight = 0 &&
      resultant commonLeft commonLeft = 0 &&
      resultant defective1 defective2 = 16 &&
      resultant nonunit1 nonunit2 = -1

-- Bivariate elimination executes the recursive exact-division instance.
#guard
    let t : DensePoly Int := ofList [0, 1]
    let one : DensePoly Int := 1
    let ySqSubT : DensePoly (DensePoly Int) := ofList [0 - t, 0, one]
    let ySubT : DensePoly (DensePoly Int) := ofList [0 - t, one]
    resultant ySqSubT ySubT = t * t - t

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

/-- A nonzero right input paired with zero is the singleton chain. -/
theorem subresultantChain_zero_left [One R] [Add R] [Sub R] [Mul R] [Div R]
    (g : DensePoly R) (hg : g ≠ 0) : subresultantChain 0 g = #[g] := by
  unfold subresultantChain subresultantRun
  have hgz : g.isZero = false := by
    rw [isZero_eq_false_iff]
    by_cases hpos : 0 < g.size
    · exact hpos
    · exfalso
      apply hg
      apply ext_coeff
      intro i
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le g (by omega)
  have hzz : (0 : DensePoly R).isZero = true := rfl
  simp [hgz, hzz]

/-- Every stored term is nonzero over a lawful exact-division domain. -/
theorem subresultantChain_ne_zero {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (p : DensePoly S) (hp : p ∈ subresultantChain f g) :
    p ≠ 0 := by
  sorry

/-- After the possibly equal-degree ordered inputs, stored degrees strictly
decrease. -/
theorem subresultantChain_size_strict {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (i : Nat) (hi : 1 ≤ i)
    (hnext : i + 1 < (subresultantChain f g).size) :
    ((subresultantChain f g).getD (i + 1) 0).size <
      ((subresultantChain f g).getD i 0).size := by
  sorry

/-- The nonzero Brown chain stores at most two inputs plus one term for every
possible degree at or below the smaller input degree. -/
theorem subresultantChain_size_le {S : Type u}
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

-- Lifting the integer defective chain executes coefficientwise division by a
-- nonunit polynomial scalar and the odd-sign branch in the recursive ring.
#guard
    let zero : DensePoly Int := 0
    let mone : DensePoly Int := C (-1)
    let two : DensePoly Int := C 2
    let f : DensePoly (DensePoly Int) := ofList [zero, zero, zero, zero, mone]
    let g : DensePoly (DensePoly Int) := ofList [mone, zero, zero, two]
    let run := subresultantRun f g
    run.chain.size = 4 && run.chain.getD 3 0 = C mone && run.scale = mone

-- Reversed inputs are degree-ordered; zero inputs are omitted.
#guard
    let linear := ofList ([1, 1] : List Int)
    let quadratic := ofList ([1, 0, 1] : List Int)
    (subresultantChain linear quadratic).getD 0 0 = quadratic &&
      subresultantChain 0 linear = #[linear] &&
      subresultantChain (0 : DensePoly Int) 0 = #[]

end DensePoly
end Hex
