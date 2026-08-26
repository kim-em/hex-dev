/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.Subresultant
public import HexResultant.SubresultantCofactor
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

private theorem getD_push_old {A : Type u} (xs : Array A) (x fallback : A)
    (i : Nat) (hi : i < xs.size) :
    (xs.push x).getD i fallback = xs.getD i fallback := by
  have hi' : i < (xs.push x).size := by
    rw [Array.size_push]
    omega
  rw [← Array.getElem_eq_getD fallback (h := hi'),
    Array.getElem_push_lt hi, Array.getElem_eq_getD fallback]

private theorem getD_push_last {A : Type u} (xs : Array A) (x fallback : A) :
    (xs.push x).getD xs.size fallback = x := by
  have hi : xs.size < (xs.push x).size := by
    rw [Array.size_push]
    omega
  rw [← Array.getElem_eq_getD fallback (h := hi), Array.getElem_push_eq]

/-- Appending an entry does not alter any earlier accumulated Brown scale. -/
private theorem brownScale_push_old [One R] [Mul R] [Div R]
    (chain : Array (Entry R)) (x : Entry R) (k : Nat) (hk : k < chain.size) :
    brownScale (chain.push x) k = brownScale chain k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      cases k with
      | zero =>
          simp only [brownScale]
          rw [getD_push_old, getD_push_old] <;> omega
      | succ i =>
          simp only [brownScale]
          rw [getD_push_old, getD_push_old, ih (by omega)] <;> omega

/-- A previously recorded exact cofactor step is unchanged by appending a
later entry. -/
private theorem cofactorStep_push_old [One R] [Add R] [Sub R] [Mul R] [Div R]
    (chain : Array (Entry R)) (x : Entry R) (i : Nat)
    (hi : i < chain.size) (hstep : CofactorStep chain i) :
    CofactorStep (chain.push x) i := by
  unfold CofactorStep at hstep ⊢
  rw [getD_push_old, getD_push_old, getD_push_old,
    brownScale_push_old] <;> try omega

/-- Pushing a Bezout entry and its new exact step preserves the chain law. -/
private theorem Law.push [One R] [Add R] [Sub R] [Mul R] [Div R]
    (f g : DensePoly R) (chain : Array (Entry R)) (x : Entry R)
    (hlaw : Law f g chain) (hbez : x.1 * f + x.2.1 * g = value x)
    (hstep : 3 ≤ chain.size → CofactorStep (chain.push x) chain.size) :
    Law f g (chain.push x) := by
  constructor
  · intro e he
    rcases Array.mem_push.mp he with he | rfl
    · exact hlaw.1 e he
    · exact hbez
  · intro i hi hbound
    rw [Array.size_push] at hbound
    by_cases hold : i < chain.size
    · exact cofactorStep_push_old chain x i hold (hlaw.2 i hi hold)
    · have hieq : i = chain.size := by omega
      subst i
      exact hstep hi

/-- The recursive extended worker preserves the chain law from any reachable
integral Brown state. -/
private theorem subresultantAuxExt_law {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (F G prev curr : DensePoly S) (hPrev : S)
    (prevU prevV currU currV : DensePoly S)
    (chain : Array (Entry S)) (fuel : Nat)
    (hinv : _root_.Hex.DensePoly.BrownInv F G prev curr hPrev)
    (hGF : G.size ≤ F.size) (hprevG : prev.size ≤ G.size)
    (hcurrG : curr.size ≤ G.size)
    (hlaw : Law F G chain) (hsize : 3 ≤ chain.size)
    (hprevBez : prevU * F + prevV * G = prev)
    (hcurrBez : currU * F + currV * G = curr)
    (hlastPrev : chain.getD (chain.size - 2) (0, 0, 0) =
      (prevU, prevV, prev))
    (hlastCurr : chain.getD (chain.size - 1) (0, 0, 0) =
      (currU, currV, curr))
    (hscale : brownScale chain (chain.size - 2) = hPrev)
    (hprevU : prevU.size ≤ Subresultant.formalDegree G - (curr.size - 2))
    (hprevV : prevV.size ≤ Subresultant.formalDegree F - (curr.size - 2))
    (hcurrU : currU.size ≤ Subresultant.formalDegree G - (curr.size - 2))
    (hcurrV : currV.size ≤ Subresultant.formalDegree F - (curr.size - 2))
    (hcurrUStrong : currU.size ≤ Subresultant.formalDegree G - (prev.size - 2))
    (hcurrVStrong : currV.size ≤ Subresultant.formalDegree F - (prev.size - 2)) :
    Law F G
      (subresultantAuxExt prev curr hPrev prevU prevV currU currV chain fuel) := by
  induction fuel generalizing prev curr hPrev prevU prevV currU currV chain with
  | zero => simpa [subresultantAuxExt] using hlaw
  | succ fuel ih =>
      unfold _root_.Hex.DensePoly.BrownInv at hinv
      rcases hinv with ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let qr := pseudoDivMod prev curr
      let q := qr.1
      let p := qr.2
      have hinv : _root_.Hex.DensePoly.BrownInv F G prev curr hPrev :=
        by exact ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
      cases hpzero : p.isZero with
      | true =>
          simpa [subresultantAuxExt, delta, hCurr, qr, q, p, hpzero] using hlaw
      | false =>
          have hp : p ≠ 0 := by
            intro hz
            have hz' : p.isZero = true := by rw [hz]; rfl
            rw [hz'] at hpzero
            exact Bool.noConfusion hpzero
          let divisor :=
            negOnePow (R := S) (delta + 1) * prev.leadingCoeff *
              powNat hPrev delta
          let next := divScalar p divisor
          let nextImpl := divScalarImpl p divisor
          have hpRaw : (pseudoDivMod prev curr).2 ≠ 0 := by
            simpa only [p, qr] using hp
          have hfactorRaw := _root_.Hex.DensePoly.BrownInv.factor F G prev curr hPrev hinv hpRaw
          rcases hfactorRaw with
            ⟨hdivRaw, hpScaleRaw, hnextRaw, hnextEqRaw⟩
          have hdivisor : divisor ≠ 0 := by
            simpa only [divisor, delta] using hdivRaw
          have hpScale : p = scale divisor next := by
            simpa only [p, divisor, next, delta, qr] using hpScaleRaw
          have hnext : next ≠ 0 := by
            simpa only [p, divisor, next, delta, qr] using hnextRaw
          have hnextEq : next = Subresultant.poly (curr.size - 2) F G := by
            simpa only [p, divisor, next, delta, qr] using hnextEqRaw
          have hnextImplEq : nextImpl = next := by
            dsimp only [nextImpl, next]
            exact (divScalar_eq_divScalarImpl p divisor).symm
          have hnextImpl : nextImpl ≠ 0 := by
            rw [hnextImplEq]
            exact hnext
          have hnextZero : nextImpl.isZero = false := by
            cases hz : nextImpl.isZero with
            | false => rfl
            | true =>
                exact False.elim
                  (hnextImpl ((size_eq_zero_iff nextImpl).mp
                    ((isZero_eq_true_iff nextImpl).1 hz)))
          let J := curr.size - 2
          let a := powNat curr.leadingCoeff (delta + 1)
          let numU := numerator a q prevU currU
          let numV := numerator a q prevV currV
          let nextU := divScalarImpl numU divisor
          let nextV := divScalarImpl numV divisor
          have hcurrBig : 2 ≤ curr.size := by
            have hpSize : p.size < curr.size := by
              simpa only [p, qr] using pseudoDivMod_remainder_lt prev curr hcurr
            have hpPos : 0 < p.size := by
              by_cases hs : 0 < p.size
              · exact hs
              · exact False.elim (hp ((size_eq_zero_iff p).mp (by omega)))
            omega
          have hJ : J < Subresultant.formalDegree G := by
            dsimp only [J, Subresultant.formalDegree]
            have hGpos : 0 < G.size := by omega
            omega
          have hnumRepr : numU * F + numV * G = scale divisor next := by
            have hrec := pseudoDivMod_reconstruct prev curr hcurr
              (Nat.le_of_lt hlt)
            have ha : a = curr.leadingCoeff ^ (prev.size - curr.size + 1) := by
              simp only [a, delta, powNat_eq_pow]
            have hnum : numU * F + numV * G = p := by
              dsimp only [numU, numV, numerator]
              rw [← scale_eq_scaleImpl, ← scale_eq_scaleImpl]
              have hdistU : (scale a prevU - q * currU) * F =
                  scale a prevU * F - (q * currU) * F := by grind
              have hdistV : (scale a prevV - q * currV) * G =
                  scale a prevV * G - (q * currV) * G := by grind
              rw [hdistU, hdistV, ← scale_mul, ← scale_mul]
              have hrearr :
                  scale a (prevU * F) - (q * currU) * F +
                      (scale a (prevV * G) - (q * currV) * G) =
                    scale a (prevU * F + prevV * G) -
                      q * (currU * F + currV * G) := by
                rw [scale_add]
                grind
              rw [hrearr, hprevBez, hcurrBez, ha]
              simpa only [q, p, qr] using (show
                scale (curr.leadingCoeff ^ (prev.size - curr.size + 1)) prev -
                    (pseudoDivMod prev curr).1 * curr =
                  (pseudoDivMod prev curr).2 by grind)
            rw [hnum, hpScale]
          have hqSize : q.size ≤ prev.size - curr.size + 1 := by
            simpa only [q, qr] using pseudoDivMod_quotient_size_le prev curr
          have hGpos : 0 < G.size := by omega
          have hFpos : 0 < F.size := by omega
          have hprevBig : 2 ≤ prev.size := by omega
          have hnumU : numU.size ≤ Subresultant.formalDegree G - J := by
            dsimp only [numU, numerator]
            apply Nat.le_trans (Subresultant.size_sub_le_max _ _)
            apply Nat.max_le.mpr
            constructor
            · exact Nat.le_trans (size_scaleImpl_le _ _) hprevU
            · apply Nat.le_trans (size_mul_le q currU)
              dsimp only [J, Subresultant.formalDegree] at hcurrUStrong ⊢
              omega
          have hnumV : numV.size ≤ Subresultant.formalDegree F - J := by
            dsimp only [numV, numerator]
            apply Nat.le_trans (Subresultant.size_sub_le_max _ _)
            apply Nat.max_le.mpr
            constructor
            · exact Nat.le_trans (size_scaleImpl_le _ _) hprevV
            · apply Nat.le_trans (size_mul_le q currV)
              dsimp only [J, Subresultant.formalDegree] at hcurrVStrong ⊢
              omega
          have hcanonical := Subresultant.eq_scaled_cofactor J divisor F G numU numV
            hGF hJ (by rw [← hnextEq]; exact hnext) hnumU hnumV
            (by rw [hnextEq] at hnumRepr; exact hnumRepr)
          have hnextUEq : nextU = Subresultant.cofactorU J F G := by
            dsimp only [nextU]
            rw [← divScalar_eq_divScalarImpl, hcanonical.1,
              divScalar_scale _ hdivisor]
          have hnextVEq : nextV = Subresultant.cofactorV J F G := by
            dsimp only [nextV]
            rw [← divScalar_eq_divScalarImpl, hcanonical.2,
              divScalar_scale _ hdivisor]
          have hnumUExact : numU = scale divisor nextU := by
            rw [hnextUEq, hcanonical.1]
          have hnumVExact : numV = scale divisor nextV := by
            rw [hnextVEq, hcanonical.2]
          have hnextBez : nextU * F + nextV * G = nextImpl := by
            rw [hnextUEq, hnextVEq, Subresultant.cofactor_bezout J F G hGF hJ,
              ← hnextEq, hnextImplEq]
          have hstep : _root_.Hex.DensePoly.BrownInv F G curr next hCurr := by
            have hs := _root_.Hex.DensePoly.BrownInv.step F G prev curr hPrev hinv hpRaw
            simpa only [delta, hCurr, p, divisor, next, qr] using hs
          have hstepImpl : _root_.Hex.DensePoly.BrownInv F G curr nextImpl hCurr := by
            rw [hnextImplEq]
            exact hstep
          have hnextLt : nextImpl.size < curr.size := hstepImpl.2.2.1
          let x : Entry S := (nextU, nextV, nextImpl)
          have hlawPush : Law F G (chain.push x) := by
            apply Law.push F G chain x hlaw hnextBez
            intro _hthree
            unfold CofactorStep
            rw [getD_push_old, getD_push_old, getD_push_last,
              brownScale_push_old, hlastPrev, hlastCurr, hscale]
            · simpa only [x, value, delta, a, q, divisor, numU, numV]
                using ⟨hnumUExact, hnumVExact⟩
            all_goals omega
          have hlastPrev' :
              (chain.push x).getD ((chain.push x).size - 2) (0, 0, 0) =
                (currU, currV, curr) := by
            rw [Array.size_push, show chain.size + 1 - 2 = chain.size - 1 by omega,
              getD_push_old, hlastCurr] <;> omega
          have hlastCurr' :
              (chain.push x).getD ((chain.push x).size - 1) (0, 0, 0) =
                (nextU, nextV, nextImpl) := by
            rw [Array.size_push, show chain.size + 1 - 1 = chain.size by omega,
              getD_push_last]
          have hscale' :
              brownScale (chain.push x) ((chain.push x).size - 2) = hCurr := by
            rw [Array.size_push, show chain.size + 1 - 2 = chain.size - 1 by omega,
              show chain.size - 1 = (chain.size - 3) + 2 by omega]
            simp only [brownScale]
            rw [show chain.size - 3 + 1 = chain.size - 2 by omega,
              show chain.size - 3 + 2 = chain.size - 1 by omega]
            rw [getD_push_old, getD_push_old, brownScale_push_old,
              hlastPrev, hlastCurr, hscale] <;> try omega
            rfl
          have hnextUStrong : nextU.size ≤ Subresultant.formalDegree G - J := by
            rw [hnextUEq]
            exact Subresultant.cofactorU_size_le J F G
          have hnextVStrong : nextV.size ≤ Subresultant.formalDegree F - J := by
            rw [hnextVEq]
            exact Subresultant.cofactorV_size_le J F G
          have hcurrU' : currU.size ≤
              Subresultant.formalDegree G - (nextImpl.size - 2) := by
            dsimp only [Subresultant.formalDegree] at hcurrU ⊢
            omega
          have hcurrV' : currV.size ≤
              Subresultant.formalDegree F - (nextImpl.size - 2) := by
            dsimp only [Subresultant.formalDegree] at hcurrV ⊢
            omega
          have hnextU' : nextU.size ≤
              Subresultant.formalDegree G - (nextImpl.size - 2) := by
            dsimp only [J, Subresultant.formalDegree] at hnextUStrong ⊢
            omega
          have hnextV' : nextV.size ≤
              Subresultant.formalDegree F - (nextImpl.size - 2) := by
            dsimp only [J, Subresultant.formalDegree] at hnextVStrong ⊢
            omega
          have hrec := ih curr nextImpl hCurr currU currV nextU nextV
            (chain.push x) hstepImpl hcurrG (by omega) hlawPush
            (by rw [Array.size_push]; omega) hcurrBez hnextBez
            hlastPrev' hlastCurr' hscale'
            hcurrU' hcurrV' hnextU' hnextV' hnextUStrong hnextVStrong
          simpa [subresultantAuxExt, delta, hCurr, qr, q, p, hpzero,
            divisor, nextImpl, hnextZero, a, numU, numV, nextU, nextV, x]
            using hrec

/-- The degree-ordered extended worker satisfies the law in ordered input
coordinates. -/
private theorem subresultantOrderedExt_law {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    Law f g (subresultantOrderedExt f g 1 0 0 1) := by
  unfold subresultantOrderedExt
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let qr := pseudoDivMod f g
  let q := qr.1
  let p := qr.2
  let seed : Array (Entry S) := #[(1, 0, f), (0, 1, g)]
  cases hpzero : p.isZero with
  | true =>
      have hseed : Law f g seed := by
        constructor
        · intro e he
          have he' := Array.mem_def.mp he
          simp only [seed, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl
          · change (1 : DensePoly S) * f + 0 * g = f
            grind
          · change (0 : DensePoly S) * f + 1 * g = g
            grind
        · intro i hi hbound
          simp [seed] at hbound
          exact False.elim (by omega)
      simpa [delta, h₂, qr, q, p, seed, hpzero] using hseed
  | false =>
      have hp : p ≠ 0 := by
        intro hz
        have hz' : p.isZero = true := by rw [hz]; rfl
        rw [hz'] at hpzero
        exact Bool.noConfusion hpzero
      let sign := negOnePow (R := S) (delta + 1)
      let g₃ := scaleImpl sign p
      have hgpos : 0 < g.size := by
        by_cases hs : 0 < g.size
        · exact hs
        · exact False.elim (hg ((size_eq_zero_iff g).mp (by omega)))
      have hglc := leadingCoeff_ne_zero_of_pos_size g hgpos
      have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hglc
      have hsign : sign ≠ 0 := negOnePow_ne_zero h1 (delta + 1)
      have hg₃Eq : g₃ = scale sign p := by
        exact (scale_eq_scaleImpl sign p).symm
      have hg₃ : g₃ ≠ 0 := by
        rw [hg₃Eq]
        exact scale_ne_zero hsign hp
      have hg₃Zero : g₃.isZero = false := by
        cases hz : g₃.isZero with
        | false => rfl
        | true =>
            exact False.elim (hg₃ ((size_eq_zero_iff g₃).mp
              ((isZero_eq_true_iff g₃).1 hz)))
      let a := powNat g.leadingCoeff (delta + 1)
      let g₃U := scaleImpl sign (numerator a q 1 0)
      let g₃V := scaleImpl sign (numerator a q 0 1)
      have hgBig : 2 ≤ g.size := by
        have hpSize : p.size < g.size := by
          simpa only [p, qr] using pseudoDivMod_remainder_lt f g hg
        have hpPos : 0 < p.size := by
          by_cases hs : 0 < p.size
          · exact hs
          · exact False.elim (hp ((size_eq_zero_iff p).mp (by omega)))
        omega
      let J := g.size - 2
      have hJ : J < Subresultant.formalDegree g := by
        dsimp only [J, Subresultant.formalDegree]
        omega
      have hroot : Subresultant.poly J f g = g₃ := by
        have h := Subresultant.poly_prem f g hgBig hgf
        rw [hg₃Eq]
        simpa [J, delta, sign, p, qr, negOnePow_eq_sign] using h
      have hg₃Bez : g₃U * f + g₃V * g = g₃ := by
        have hrec := pseudoDivMod_reconstruct f g hg hgf
        dsimp only [g₃U, g₃V, numerator]
        rw [← scale_eq_scaleImpl, ← scale_eq_scaleImpl,
          ← scale_eq_scaleImpl, ← scale_eq_scaleImpl]
        have ha : a = g.leadingCoeff ^ (f.size - g.size + 1) := by
          simp only [a, delta, powNat_eq_pow]
        have hinner :
            (scale a 1 - q * 0) * f + (scale a 0 - q * 1) * g = p := by
          have hbaseF : (1 : DensePoly S) * f + 0 * g = f := by grind
          have hbaseG : (0 : DensePoly S) * f + 1 * g = g := by grind
          have hrearr :
              (scale a 1 - q * 0) * f + (scale a 0 - q * 1) * g =
                scale a ((1 : DensePoly S) * f + 0 * g) -
                  q * ((0 : DensePoly S) * f + 1 * g) := by
            rw [scale_add, scale_mul, scale_mul]
            grind
          rw [hrearr, hbaseF, hbaseG]
          rw [ha]
          simpa only [q, p, qr] using (show
            scale (g.leadingCoeff ^ (f.size - g.size + 1)) f -
                (pseudoDivMod f g).1 * g = (pseudoDivMod f g).2 by grind)
        rw [← scale_mul, ← scale_mul]
        rw [← scale_add, hinner, ← hg₃Eq]
      have hg₃UStrong : g₃U.size ≤ Subresultant.formalDegree g - J := by
        dsimp only [g₃U]
        apply Nat.le_trans (size_scaleImpl_le _ _)
        dsimp only [numerator]
        apply Nat.le_trans (Subresultant.size_sub_le_max _ _)
        apply Nat.max_le.mpr
        constructor
        · apply Nat.le_trans (size_scaleImpl_le _ _)
          rw [size_one h1]
          dsimp only [J, Subresultant.formalDegree]
          omega
        · have hmul : q * (0 : DensePoly S) = 0 := by grind
          rw [hmul, size_zero]
          omega
      have hg₃VStrong : g₃V.size ≤ Subresultant.formalDegree f - J := by
        dsimp only [g₃V]
        apply Nat.le_trans (size_scaleImpl_le _ _)
        dsimp only [numerator]
        apply Nat.le_trans (Subresultant.size_sub_le_max _ _)
        apply Nat.max_le.mpr
        constructor
        · apply Nat.le_trans (size_scaleImpl_le _ _)
          rw [size_zero]
          omega
        · apply Nat.le_trans (size_mul_le q (1 : DensePoly S))
          have hqSize := pseudoDivMod_quotient_size_le f g
          rw [size_one h1]
          dsimp only [q, qr, J, Subresultant.formalDegree] at hqSize ⊢
          omega
      let chain := seed.push (g₃U, g₃V, g₃)
      have hlaw : Law f g chain := by
        constructor
        · intro e he
          rcases Array.mem_push.mp he with he | rfl
          · have he' := Array.mem_def.mp he
            simp only [seed, List.mem_cons, List.not_mem_nil, or_false] at he'
            rcases he' with rfl | rfl
            · change (1 : DensePoly S) * f + 0 * g = f
              grind
            · change (0 : DensePoly S) * f + 1 * g = g
              grind
          · exact hg₃Bez
        · intro i hi hbound
          simp [chain, seed] at hbound
          exact False.elim (by omega)
      have hinvRaw := brownInv_init f g hg hgf (by simpa only [p, qr] using hp)
      have hinv : _root_.Hex.DensePoly.BrownInv f g g g₃ h₂ := by
        rw [hg₃Eq]
        simpa only [delta, h₂, p, sign, qr] using hinvRaw
      have hprevU : (0 : DensePoly S).size ≤
          Subresultant.formalDegree g - (g₃.size - 2) := by
        rw [size_zero]
        omega
      have hprevV : (1 : DensePoly S).size ≤
          Subresultant.formalDegree f - (g₃.size - 2) := by
        have hg₃lt := hinv.2.2.1
        dsimp only [Subresultant.formalDegree]
        rw [size_one h1]
        omega
      have hcurrU : g₃U.size ≤
          Subresultant.formalDegree g - (g₃.size - 2) := by
        have hg₃lt := hinv.2.2.1
        dsimp only [J, Subresultant.formalDegree] at hg₃UStrong ⊢
        omega
      have hcurrV : g₃V.size ≤
          Subresultant.formalDegree f - (g₃.size - 2) := by
        have hg₃lt := hinv.2.2.1
        dsimp only [J, Subresultant.formalDegree] at hg₃VStrong ⊢
        omega
      have hprevBez : (0 : DensePoly S) * f + 1 * g = g := by grind
      have hchainSize : 3 ≤ chain.size := by simp [chain, seed]
      have hg₃G : g₃.size ≤ g.size := Nat.le_of_lt hinv.2.2.1
      have haux := subresultantAuxExt_law f g g g₃ h₂ 0 1 g₃U g₃V
        chain (g.size + 1) hinv hgf (Nat.le_refl _) hg₃G hlaw
        hchainSize hprevBez hg₃Bez (by rfl) (by rfl)
        (by rfl)
        hprevU hprevV hcurrU hcurrV hg₃UStrong hg₃VStrong
      simpa [delta, h₂, qr, q, p, hpzero, sign, g₃, hg₃Zero, a,
        g₃U, g₃V, seed, chain] using haux

/-- Exchange the two caller-coordinate cofactors of an extended entry. -/
@[inline]
private def swap (e : Entry R) : Entry R := (e.2.1, e.1, e.2.2)

/-- The recursive worker is equivariant under exchange of its two cofactor
coordinates. -/
private theorem subresultantAuxExt_swap [One R] [Add R] [Sub R] [Mul R]
    [Div R] (prev curr : DensePoly R) (hPrev : R)
    (prevU prevV currU currV : DensePoly R) (chain : Array (Entry R))
    (fuel : Nat) :
    subresultantAuxExt prev curr hPrev prevV prevU currV currU
        (chain.map swap) fuel =
      (subresultantAuxExt prev curr hPrev prevU prevV currU currV chain fuel).map
        swap := by
  induction fuel generalizing prev curr hPrev prevU prevV currU currV chain with
  | zero => rfl
  | succ fuel ih =>
      unfold subresultantAuxExt
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let qr := pseudoDivMod prev curr
      let q := qr.1
      let p := qr.2
      cases hp : p.isZero with
      | true => simp [qr, p, hp]
      | false =>
          let divisor :=
            negOnePow (delta + 1) * prev.leadingCoeff * powNat hPrev delta
          let next := divScalarImpl p divisor
          cases hnext : next.isZero with
          | true =>
              simp [delta, qr, p, hp, divisor, next, hnext]
          | false =>
              let a := powNat curr.leadingCoeff (delta + 1)
              let nextU :=
                divScalarImpl (numerator a q prevU currU) divisor
              let nextV :=
                divScalarImpl (numerator a q prevV currV) divisor
              have hrec := ih curr next hCurr currU currV nextU nextV
                (chain.push (nextU, nextV, next))
              simpa [delta, hCurr, qr, q, p, hp, divisor, next, hnext, a,
                nextU, nextV, Array.map_push, swap] using hrec

/-- The ordered worker is equivariant under exchange of its two supplied
cofactor coordinates. -/
private theorem subresultantOrderedExt_swap [One R] [Add R] [Sub R] [Mul R]
    [Div R] (f g fU fV gU gV : DensePoly R) :
    subresultantOrderedExt f g fV fU gV gU =
      (subresultantOrderedExt f g fU fV gU gV).map swap := by
  unfold subresultantOrderedExt
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let qr := pseudoDivMod f g
  let q := qr.1
  let p := qr.2
  cases hp : p.isZero with
  | true => simp [qr, p, hp, swap]
  | false =>
      let sign := negOnePow (R := R) (delta + 1)
      let g₃ := scaleImpl sign p
      cases hg₃ : g₃.isZero with
      | true => simp [delta, qr, p, hp, sign, g₃, hg₃, swap]
      | false =>
          let a := powNat g.leadingCoeff (delta + 1)
          let g₃U := scaleImpl sign (numerator a q fU gU)
          let g₃V := scaleImpl sign (numerator a q fV gV)
          have haux := subresultantAuxExt_swap g g₃ h₂ gU gV g₃U g₃V
            (#[(fU, fV, f), (gU, gV, g), (g₃U, g₃V, g₃)]) (g.size + 1)
          simpa [delta, h₂, qr, q, p, hp, sign, g₃, hg₃, a, g₃U, g₃V,
            Array.map_push, swap] using haux

private theorem getD_map_swap (chain : Array (Entry R)) (i : Nat) :
    (chain.map swap).getD i (0, 0, 0) =
      swap (chain.getD i (0, 0, 0)) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  cases chain[i]? <;> rfl

private theorem brownScale_map_swap [One R] [Mul R] [Div R]
    (chain : Array (Entry R)) (i : Nat) :
    brownScale (chain.map swap) i = brownScale chain i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      cases i with
      | zero =>
          simp only [brownScale]
          rw [getD_map_swap, getD_map_swap]
          rfl
      | succ i =>
          simp only [brownScale]
          rw [getD_map_swap, getD_map_swap, ih]
          rfl

private theorem CofactorStep.swap [One R] [Add R] [Sub R] [Mul R] [Div R]
    (chain : Array (Entry R)) (i : Nat) (h : CofactorStep chain i) :
    CofactorStep (chain.map swap) i := by
  unfold CofactorStep at h ⊢
  rw [getD_map_swap, getD_map_swap, getD_map_swap, brownScale_map_swap]
  exact ⟨h.2, h.1⟩

/-- Exchanging both caller inputs and both cofactor coordinates preserves the
extended-chain law. -/
private theorem Law.swap {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (f g : DensePoly S) (chain : Array (Entry S)) (h : Law f g chain) :
    Law g f (chain.map swap) := by
  constructor
  · intro e he
    have he' := Array.mem_def.mp he
    simp only [Array.toList_map] at he'
    rcases List.mem_map.mp he' with ⟨x, hx, rfl⟩
    have hx' : x ∈ chain := Array.mem_def.mpr hx
    have hbez := h.1 x hx'
    change x.2.1 * g + x.1 * f = value x
    rw [add_comm_poly (x.2.1 * g) (x.1 * f)]
    exact hbez
  · intro i hi hbound
    have hbound' : i < chain.size := by simpa using hbound
    exact (h.2 i hi hbound').swap

end SubresultantExt

/-- The extended Brown recurrence has exact transformation rows and every
stored entry satisfies its caller-order-sensitive Bezout identity. -/
theorem subresultantChainExt_law {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) :
    SubresultantExt.Law f g (subresultantChainExt f g) := by
  unfold subresultantChainExt
  cases hf : f.isZero with
  | true =>
      cases hg : g.isZero with
      | true =>
          simp [SubresultantExt.Law]
      | false =>
          have hsingle : SubresultantExt.Law f g #[(0, 1, g)] := by
            constructor
            · intro e he
              have he' := Array.mem_def.mp he
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
              rcases he' with rfl
              change (0 : DensePoly S) * f + 1 * g = g
              grind
            · intro i hi hbound
              simp at hbound
              exact False.elim (by omega)
          simpa [hf, hg] using hsingle
  | false =>
      have hf0 : f ≠ 0 := by
        intro hz
        have : f.isZero = true := by rw [hz]; rfl
        rw [this] at hf
        exact Bool.noConfusion hf
      cases hg : g.isZero with
      | true =>
          have hsingle : SubresultantExt.Law f g #[(1, 0, f)] := by
            constructor
            · intro e he
              have he' := Array.mem_def.mp he
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
              rcases he' with rfl
              change (1 : DensePoly S) * f + 0 * g = f
              grind
            · intro i hi hbound
              simp at hbound
              exact False.elim (by omega)
          simpa [hf, hg] using hsingle
      | false =>
          have hg0 : g ≠ 0 := by
            intro hz
            have : g.isZero = true := by rw [hz]; rfl
            rw [this] at hg
            exact Bool.noConfusion hg
          by_cases hfg : f.size < g.size
          · have hord := SubresultantExt.subresultantOrderedExt_law g f hf0
                (Nat.le_of_lt hfg)
            have hswap := SubresultantExt.Law.swap g f
              (subresultantOrderedExt g f 1 0 0 1) hord
            rw [← SubresultantExt.subresultantOrderedExt_swap g f
              (1 : DensePoly S) 0 0 1] at hswap
            simpa [hf, hg, hfg] using hswap
          · have hgf : g.size ≤ f.size := by omega
            have hord := SubresultantExt.subresultantOrderedExt_law f g hg0 hgf
            simpa [hf, hg, hfg] using hord

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
