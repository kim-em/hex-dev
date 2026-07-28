/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.ExactDiv
public import HexResultant.PseudoDivMod
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

/-- A polynomial rejected by the executable zero test is propositionally
nonzero. -/
private theorem ne_zero_of_isZero_false (p : DensePoly R)
    (hp : p.isZero = false) : p ≠ 0 := by
  intro hzero
  subst p
  change true = false at hp
  exact Bool.noConfusion hp

/-- A polynomial accepted by the executable zero test is propositionally
zero. -/
private theorem eq_zero_of_isZero_true (p : DensePoly R)
    (hp : p.isZero = true) : p = 0 := by
  apply (size_eq_zero_iff p).mp
  exact (isZero_eq_true_iff p).1 hp

/-- A propositionally nonzero polynomial is rejected by the executable zero
test. -/
private theorem isZero_false_of_ne_zero (p : DensePoly R) (hp : p ≠ 0) :
    p.isZero = false := by
  cases hzero : p.isZero with
  | false => rfl
  | true => exact (hp (eq_zero_of_isZero_true p hzero)).elim

/-- A propositionally nonzero dense polynomial stores at least one
coefficient. -/
private theorem size_pos_of_ne_zero (p : DensePoly R) (hp : p ≠ 0) :
    0 < p.size :=
  (isZero_eq_false_iff p).1 (isZero_false_of_ne_zero p hp)

/-- Once the worker has more fuel than the current polynomial has stored
coefficients, its result is independent of the exact fuel value. Every
recursive call first takes a pseudo-remainder and then maps its coefficients,
so the next current polynomial is strictly smaller even when an exact quotient
falls into a junk branch. -/
private theorem subresultantAux_fuel_eq
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R) (chain : Array (DensePoly R))
    (fuel fuel' : Nat) (hcurr : curr ≠ 0)
    (hfuel : curr.size < fuel) (hfuel' : curr.size < fuel') :
    subresultantAux prev curr hPrev chain fuel =
      subresultantAux prev curr hPrev chain fuel' := by
  induction fuel generalizing prev curr hPrev chain fuel' with
  | zero => omega
  | succ fuel ih =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          let delta := prev.size - curr.size
          let hCurr := divExp curr.leadingCoeff hPrev delta
          let p := (pseudoDivMod prev curr).2
          cases hp : p.isZero with
          | true =>
              simp [subresultantAux, p, hp]
          | false =>
              let divisor :=
                negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
              let next := divScalarImpl p divisor
              cases hnext : next.isZero with
              | true =>
                  simp [subresultantAux, delta, p, hp, divisor, next,
                    hnext]
              | false =>
                  have hnext_ne : next ≠ 0 :=
                    ne_zero_of_isZero_false next hnext
                  have hp_size : p.size < curr.size := by
                    simpa only [p] using
                      (pseudoDivMod_remainder_lt prev curr hcurr)
                  have hnext_size : next.size < curr.size := by
                    have hmap : next.size ≤ p.size := by
                      simpa only [next] using size_divScalarImpl_le p divisor
                    omega
                  have hrec := ih curr next hCurr (chain.push next) fuel'
                    hnext_ne (by omega) (by omega)
                  simpa [subresultantAux, delta, hCurr, p, hp, divisor, next,
                    hnext] using hrec

/-- The worker preserves the invariant that every stored chain term is
nonzero. The invariant uses only the explicit zero guard before each push. -/
private theorem subresultantAux_ne_zero
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R) (chain : Array (DensePoly R))
    (fuel : Nat) (hchain : ∀ q, q ∈ chain → q ≠ 0) :
    ∀ q, q ∈ (subresultantAux prev curr hPrev chain fuel).chain → q ≠ 0 := by
  induction fuel generalizing prev curr hPrev chain with
  | zero =>
      simpa [subresultantAux] using hchain
  | succ fuel ih =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      cases hp : p.isZero with
      | true =>
          simpa [subresultantAux, p, hp] using hchain
      | false =>
          let divisor :=
            negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
          let next := divScalarImpl p divisor
          cases hnext : next.isZero with
          | true =>
              have hp' : (pseudoDivMod prev curr).2.isZero = false := by
                simpa only [p] using hp
              have hnext' :
                  (divScalarImpl (pseudoDivMod prev curr).2
                    (negOnePow (prev.size - curr.size + 1) *
                      prev.leadingCoeff * powNat hPrev (prev.size - curr.size))).isZero =
                    true := by
                simpa only [next, divisor, delta, p] using hnext
              simpa [subresultantAux, hp', hnext'] using hchain
          | false =>
              have hnext_ne : next ≠ 0 :=
                ne_zero_of_isZero_false next hnext
              have hpush : ∀ q, q ∈ chain.push next → q ≠ 0 := by
                intro q hq
                rcases Array.mem_push.mp hq with hq | rfl
                · exact hchain q hq
                · exact hnext_ne
              have hrec := ih curr next hCurr (chain.push next) hpush
              simpa [subresultantAux, delta, hCurr, p, hp, divisor, next,
                hnext] using hrec

/-- Ordered nonzero inputs seed a worker chain containing only nonzero terms. -/
private theorem subresultantOrdered_ne_zero
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∀ q, q ∈ (subresultantOrdered f g).chain → q ≠ 0 := by
  unfold subresultantOrdered subresultantOrderedFuel
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  have hseed : ∀ q, q ∈ #[f, g] → q ≠ 0 := by
    intro q hq
    have hq' := Array.mem_def.mp hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact hf
    · exact hg
  cases hp : p.isZero with
  | true =>
      simpa [delta, h₂, p, hp] using hseed
  | false =>
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      cases hg₃ : g₃.isZero with
      | true =>
          simpa [delta, h₂, p, hp, g₃, hg₃] using hseed
      | false =>
          have hg₃_ne : g₃ ≠ 0 := ne_zero_of_isZero_false g₃ hg₃
          have hseed₃ : ∀ q, q ∈ #[f, g, g₃] → q ≠ 0 := by
            intro q hq
            have hq' := Array.mem_def.mp hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
            rcases hq' with rfl | rfl | rfl
            · exact hf
            · exact hg
            · exact hg₃_ne
          simpa [delta, h₂, p, hp, g₃, hg₃] using
            subresultantAux_ne_zero g g₃ h₂ #[f, g, g₃] (g.size + 1)
              hseed₃

/-- Strict descent for every adjacent pair after the two ordered inputs. -/
private def ChainStrict (chain : Array (DensePoly R)) : Prop :=
  ∀ i, 1 ≤ i → i + 1 < chain.size →
    (chain.getD (i + 1) 0).size < (chain.getD i 0).size

/-- A push leaves every old default-indexed array read unchanged. -/
private theorem getD_push_old {A : Type u} (xs : Array A) (x fallback : A)
    (i : Nat) (hi : i < xs.size) :
    (xs.push x).getD i fallback = xs.getD i fallback := by
  have hi' : i < (xs.push x).size := by
    rw [Array.size_push]
    omega
  rw [← Array.getElem_eq_getD fallback (h := hi'),
    Array.getElem_push_lt hi, Array.getElem_eq_getD fallback]

/-- The new final default-indexed array read is the pushed value. -/
private theorem getD_push_last {A : Type u} (xs : Array A) (x fallback : A) :
    (xs.push x).getD xs.size fallback = x := by
  have hi : xs.size < (xs.push x).size := by
    rw [Array.size_push]
    omega
  rw [← Array.getElem_eq_getD fallback (h := hi), Array.getElem_push_eq]

/-- Appending a smaller successor preserves strict tail descent. -/
private theorem ChainStrict.push
    (chain : Array (DensePoly R)) (curr next : DensePoly R)
    (hlast : chain.getD (chain.size - 1) 0 = curr)
    (hstrict : ChainStrict chain) (hnext : next.size < curr.size) :
    ChainStrict (chain.push next) := by
  intro i hi hbound
  by_cases hold : i + 1 < chain.size
  · rw [getD_push_old _ _ _ _ hold,
      getD_push_old _ _ _ _ (by omega)]
    exact hstrict i hi hold
  · have heq : i + 1 = chain.size := by
      rw [Array.size_push] at hbound
      omega
    have hiold : i < chain.size := by omega
    rw [heq, getD_push_last, getD_push_old _ _ _ _ hiold]
    have hiEq : i = chain.size - 1 := by omega
    rw [hiEq, hlast]
    exact hnext

/-- The worker preserves strict tail descent when its seed ends in the current
polynomial. -/
private theorem subresultantAux_strict
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R) (chain : Array (DensePoly R))
    (fuel : Nat) (hcurr : curr ≠ 0)
    (hlast : chain.getD (chain.size - 1) 0 = curr)
    (hstrict : ChainStrict chain) :
    ChainStrict (subresultantAux prev curr hPrev chain fuel).chain := by
  induction fuel generalizing prev curr hPrev chain with
  | zero =>
      simpa [subresultantAux] using hstrict
  | succ fuel ih =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      cases hp : p.isZero with
      | true =>
          simpa [subresultantAux, p, hp] using hstrict
      | false =>
          let divisor :=
            negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
          let next := divScalarImpl p divisor
          cases hnext : next.isZero with
          | true =>
              have hnext' :
                  (divScalarImpl (pseudoDivMod prev curr).2
                    (negOnePow (prev.size - curr.size + 1) *
                      prev.leadingCoeff * powNat hPrev (prev.size - curr.size))).isZero =
                    true := by
                simpa only [next, divisor, delta, p] using hnext
              simpa [subresultantAux, hp, hnext'] using hstrict
          | false =>
              have hnext_ne : next ≠ 0 :=
                ne_zero_of_isZero_false next hnext
              have hp_size : p.size < curr.size := by
                simpa only [p] using
                  (pseudoDivMod_remainder_lt prev curr hcurr)
              have hnext_size : next.size < curr.size := by
                have hmap : next.size ≤ p.size := by
                  simpa only [next] using size_divScalarImpl_le p divisor
                omega
              have hstrict' : ChainStrict (chain.push next) :=
                hstrict.push chain curr next hlast hnext_size
              have hlast' :
                  (chain.push next).getD ((chain.push next).size - 1) 0 =
                    next := by
                rw [Array.size_push, show chain.size + 1 - 1 = chain.size by omega,
                  getD_push_last]
              have hrec := ih curr next hCurr (chain.push next) hnext_ne
                hlast' hstrict'
              simpa [subresultantAux, delta, hCurr, p, hp, divisor, next,
                hnext] using hrec

/-- Ordered nonzero inputs produce a chain with strict descent after its first
two entries. -/
private theorem subresultantOrdered_strict
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) (hg : g ≠ 0) :
    ChainStrict (subresultantOrdered f g).chain := by
  unfold subresultantOrdered subresultantOrderedFuel
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  have hseed : ChainStrict (#[f, g] : Array (DensePoly R)) := by
    intro i hi hnext
    simp at hnext
    omega
  cases hp : p.isZero with
  | true =>
      simpa [delta, h₂, p, hp] using hseed
  | false =>
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      cases hg₃ : g₃.isZero with
      | true =>
          simpa [delta, h₂, p, hp, g₃, hg₃] using hseed
      | false =>
          have hg₃_ne : g₃ ≠ 0 := ne_zero_of_isZero_false g₃ hg₃
          have hp_size : p.size < g.size := by
            simpa only [p] using (pseudoDivMod_remainder_lt f g hg)
          have hg₃_size : g₃.size < g.size := by
            have hmap : g₃.size ≤ p.size := by
              simpa only [g₃] using
                size_scaleImpl_le (negOnePow (delta + 1)) p
            omega
          have hlast :
              (#[f, g] : Array (DensePoly R)).getD
                ((#[f, g] : Array (DensePoly R)).size - 1) 0 = g := by
            rfl
          have hseed₃ : ChainStrict (#[f, g, g₃] : Array (DensePoly R)) := by
            change ChainStrict ((#[f, g] : Array (DensePoly R)).push g₃)
            exact hseed.push #[f, g] g g₃ hlast hg₃_size
          simpa [delta, h₂, p, hp, g₃, hg₃] using
            subresultantAux_strict g g₃ h₂ #[f, g, g₃] (g.size + 1)
              hg₃_ne (by rfl) hseed₃

/-- A worker can append at most one term for each unit of size lost by its
current polynomial. -/
private theorem subresultantAux_size_le
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (prev curr : DensePoly R) (hPrev : R) (chain : Array (DensePoly R))
    (fuel : Nat) (hcurr : curr ≠ 0) :
    (subresultantAux prev curr hPrev chain fuel).chain.size + 1 ≤
      chain.size + curr.size := by
  induction fuel generalizing prev curr hPrev chain with
  | zero =>
      simp only [subresultantAux]
      have hpos := size_pos_of_ne_zero curr hcurr
      omega
  | succ fuel ih =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      cases hp : p.isZero with
      | true =>
          simp only [subresultantAux, p, hp, ↓reduceIte]
          have hpos := size_pos_of_ne_zero curr hcurr
          omega
      | false =>
          let divisor :=
            negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
          let next := divScalarImpl p divisor
          cases hnext : next.isZero with
          | true =>
              have hp' : (pseudoDivMod prev curr).2.isZero = false := by
                simpa only [p] using hp
              have hnext' :
                  (divScalarImpl (pseudoDivMod prev curr).2
                    (negOnePow (prev.size - curr.size + 1) *
                      prev.leadingCoeff * powNat hPrev (prev.size - curr.size))).isZero =
                    true := by
                simpa only [next, divisor, delta, p] using hnext
              simp only [subresultantAux, hp', Bool.false_eq_true, ↓reduceIte,
                hnext']
              have hpos := size_pos_of_ne_zero curr hcurr
              omega
          | false =>
              have hnext_ne : next ≠ 0 :=
                ne_zero_of_isZero_false next hnext
              have hp_size : p.size < curr.size := by
                simpa only [p] using
                  (pseudoDivMod_remainder_lt prev curr hcurr)
              have hnext_size : next.size < curr.size := by
                have hmap : next.size ≤ p.size := by
                  simpa only [next] using size_divScalarImpl_le p divisor
                omega
              have hrec := ih curr next hCurr (chain.push next) hnext_ne
              have hrec' :
                  (subresultantAux curr next hCurr (chain.push next) fuel).chain.size + 1 ≤
                    chain.size + 1 + next.size := by
                simpa only [Array.size_push] using hrec
              simpa [subresultantAux, delta, hCurr, p, hp, divisor, next,
                hnext] using (show
                  (subresultantAux curr next hCurr (chain.push next) fuel).chain.size + 1 ≤
                    chain.size + curr.size by omega)

/-- An ordered run stores at most the two inputs plus one term per possible
degree of the smaller input. -/
private theorem subresultantOrdered_size_le
    [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) (hg : g ≠ 0) :
    (subresultantOrdered f g).chain.size ≤ g.size + 1 := by
  unfold subresultantOrdered subresultantOrderedFuel
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  have hgpos := size_pos_of_ne_zero g hg
  cases hp : p.isZero with
  | true =>
      simp [p, hp]
      omega
  | false =>
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      cases hg₃ : g₃.isZero with
      | true =>
          simp [delta, p, hp, g₃, hg₃]
          omega
      | false =>
          have hg₃_ne : g₃ ≠ 0 := ne_zero_of_isZero_false g₃ hg₃
          have hp_size : p.size < g.size := by
            simpa only [p] using (pseudoDivMod_remainder_lt f g hg)
          have hg₃_size : g₃.size < g.size := by
            have hmap : g₃.size ≤ p.size := by
              simpa only [g₃] using
                size_scaleImpl_le (negOnePow (delta + 1)) p
            omega
          have haux := subresultantAux_size_le g g₃ h₂ #[f, g, g₃]
            (g.size + 1) hg₃_ne
          have haux' :
              (subresultantAux g g₃ h₂ #[f, g, g₃]
                (g.size + 1)).chain.size + 1 ≤ 3 + g₃.size := by
            simpa using haux
          simpa [delta, h₂, p, hp, g₃, hg₃] using
            (show
              (subresultantAux g g₃ h₂ #[f, g, g₃]
                (g.size + 1)).chain.size ≤ g.size + 1 by omega)

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

/-- Adding fuel beyond the public ordered-run budget leaves the result
unchanged. This is a structural consequence of strict remainder-size descent
and needs no divisibility laws. -/
theorem subresultantOrderedFuel_eq {S : Type u}
    [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (f g : DensePoly S) (hg : g ≠ 0) (extra : Nat) :
    subresultantOrderedFuel f g (g.size + 1 + extra) =
      subresultantOrdered f g := by
  unfold subresultantOrdered subresultantOrderedFuel
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  cases hp : p.isZero with
  | true =>
      simp [p, hp]
  | false =>
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      cases hg₃ : g₃.isZero with
      | true =>
          simp [delta, p, hp, g₃, hg₃]
      | false =>
          have hg₃_ne : g₃ ≠ 0 := ne_zero_of_isZero_false g₃ hg₃
          have hp_size : p.size < g.size := by
            simpa only [p] using (pseudoDivMod_remainder_lt f g hg)
          have hg₃_size : g₃.size < g.size := by
            have hmap : g₃.size ≤ p.size := by
              simpa only [g₃] using
                size_scaleImpl_le (negOnePow (delta + 1)) p
            omega
          have hfuel := subresultantAux_fuel_eq g g₃ h₂ #[f, g, g₃]
            (g.size + 1 + extra) (g.size + 1) hg₃_ne (by omega) (by omega)
          simpa [delta, h₂, p, hp, g₃, hg₃] using hfuel

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
      exact (size_eq_zero_iff f).mp (by omega)
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
      exact (size_eq_zero_iff g).mp (by omega)
  have hzz : (0 : DensePoly R).isZero = true := rfl
  simp [hgz, hzz]

/-- Every stored term is nonzero. This follows from the worker's explicit zero
guards and needs no divisibility laws. -/
theorem subresultantChain_ne_zero {S : Type u}
    [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (f g : DensePoly S) (p : DensePoly S) (hp : p ∈ subresultantChain f g) :
    p ≠ 0 := by
  unfold subresultantChain subresultantRun at hp
  cases hfz : f.isZero with
  | true =>
      cases hgz : g.isZero with
      | true =>
          simp [hfz, hgz] at hp
      | false =>
          have hg : g ≠ 0 := ne_zero_of_isZero_false g hgz
          have hp_single : p ∈ #[g] := by simpa [hfz, hgz] using hp
          have hp' := Array.mem_def.mp hp_single
          simp only [List.mem_singleton] at hp'
          subst p
          exact hg
  | false =>
      have hf : f ≠ 0 := ne_zero_of_isZero_false f hfz
      cases hgz : g.isZero with
      | true =>
          have hp_single : p ∈ #[f] := by simpa [hfz, hgz] using hp
          have hp' := Array.mem_def.mp hp_single
          simp only [List.mem_singleton] at hp'
          subst p
          exact hf
      | false =>
          have hg : g ≠ 0 := ne_zero_of_isZero_false g hgz
          by_cases hfg : f.size < g.size
          · apply subresultantOrdered_ne_zero g f hg hf p
            simpa [hfz, hgz, hfg] using hp
          · apply subresultantOrdered_ne_zero f g hf hg p
            simpa [hfz, hgz, hfg] using hp

/-- After the possibly equal-degree ordered inputs, stored degrees strictly
decrease. -/
theorem subresultantChain_size_strict {S : Type u}
    [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (f g : DensePoly S) (i : Nat) (hi : 1 ≤ i)
    (hnext : i + 1 < (subresultantChain f g).size) :
    ((subresultantChain f g).getD (i + 1) 0).size <
      ((subresultantChain f g).getD i 0).size := by
  unfold subresultantChain subresultantRun at hnext ⊢
  cases hfz : f.isZero with
  | true =>
      cases hgz : g.isZero with
      | true => simp [hfz, hgz] at hnext
      | false => simp [hfz, hgz] at hnext
  | false =>
      have hf : f ≠ 0 := ne_zero_of_isZero_false f hfz
      cases hgz : g.isZero with
      | true => simp [hfz, hgz] at hnext
      | false =>
          have hg : g ≠ 0 := ne_zero_of_isZero_false g hgz
          by_cases hfg : f.size < g.size
          · have hnext' : i + 1 < (subresultantOrdered g f).chain.size := by
              simpa [hfz, hgz, hfg] using hnext
            have hstrict := subresultantOrdered_strict g f hf i hi hnext'
            simpa [hfz, hgz, hfg] using hstrict
          · have hnext' : i + 1 < (subresultantOrdered f g).chain.size := by
              simpa [hfz, hgz, hfg] using hnext
            have hstrict := subresultantOrdered_strict f g hg i hi hnext'
            simpa [hfz, hgz, hfg] using hstrict

/-- The nonzero Brown chain stores at most two inputs plus one term for every
possible degree at or below the smaller input degree. -/
theorem subresultantChain_size_le {S : Type u}
    [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (f g : DensePoly S) (hf : f ≠ 0) (hg : g ≠ 0) :
    (subresultantChain f g).size ≤
      min (f.degree?.getD 0) (g.degree?.getD 0) + 2 := by
  have hfz : f.isZero = false := isZero_false_of_ne_zero f hf
  have hgz : g.isZero = false := isZero_false_of_ne_zero g hg
  have hfpos : 0 < f.size := (isZero_eq_false_iff f).1 hfz
  have hgpos : 0 < g.size := (isZero_eq_false_iff g).1 hgz
  have hfdeg : f.degree?.getD 0 = f.size - 1 := by
    simp [degree?, Nat.ne_of_gt hfpos]
  have hgdeg : g.degree?.getD 0 = g.size - 1 := by
    simp [degree?, Nat.ne_of_gt hgpos]
  by_cases hfg : f.size < g.size
  · have hchain :
        subresultantChain f g = (subresultantOrdered g f).chain := by
      simp [subresultantChain, subresultantRun, hfz, hgz, hfg]
    rw [hchain, hfdeg, hgdeg, Nat.min_eq_left (by omega)]
    have hbound := subresultantOrdered_size_le g f hf
    omega
  · have hchain :
        subresultantChain f g = (subresultantOrdered f g).chain := by
      simp [subresultantChain, subresultantRun, hfz, hgz, hfg]
    rw [hchain, hfdeg, hgdeg, Nat.min_eq_right (by omega)]
    have hbound := subresultantOrdered_size_le f g hg
    omega

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
