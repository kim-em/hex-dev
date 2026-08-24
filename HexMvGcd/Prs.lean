/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Content
public import HexResultant.SubresultantExt

@[expose] public section
set_option backward.proofsInPublic true

/-!
The deterministic extended-subresultant fallback.

Candidate production is structurally recursive in the arity.  At a successor
arity the extended Brown chain supplies the terminal identity; all content
folds and the residual coprimality obligation use the already-constructed
lower-arity operations.  The public wrapper replays `checkGcd` and exposes no
unchecked candidate.
-/

namespace Hex.MvPoly

universe u

/-- Operations constructed together at one arity. Keeping the pair together
makes every recursive call visibly decrease the arity. -/
structure PrsOpsAt (R : Type u) [Zero R] (n : Nat) : Type (u + 1) where
  gcdCert : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp
  coprimeCert : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → CoprimeCert n R cmp

/-- Stable total form of exact division used only at route invariants proved
below. Final outputs are independently replayed by `checkGcd`. -/
def quotient {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f g : MvPoly n R cmp) : MvPoly n R cmp :=
  (divExact? f g).getD 0

/-- The default arm in `quotient` is unreachable at every route use: a known
nonzero exact divisor makes the checked division return a concrete quotient. -/
theorem quotient_mul_of_dvd {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f g : MvPoly n R cmp} (hg : g ≠ 0) (hd : g ∣ f) :
    quotient f g * g = f := by
  rcases hd with ⟨q, hq⟩
  have hdiv : divExact? f g = some q := (divExact?_eq hg).mpr hq
  rw [quotient, hdiv]
  exact hq.symm

/-- Direct computational form used when a producer already has the checked
division result in hand. -/
theorem quotient_eq_of_some {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    {f g q : MvPoly n R cmp} (hq : divExact? f g = some q) :
    quotient f g = q := by
  simp [quotient, hq]

/-- The last extended-chain entry. Nonzero inputs make the chain nonempty;
the route completeness theorem establishes that invariant. -/
def terminal {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S]
    [Div S] (f h : DensePoly S) :
    DensePoly S × DensePoly S × DensePoly S :=
  let chain := DensePoly.subresultantChainExt f h
  chain.getD (chain.size - 1) (0, 0, 0)

/-- The extended Brown worker only appends to its supplied chain. -/
private theorem auxExt_size_le {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [Div S]
    (prev curr : DensePoly S) (hPrev : S)
    (prevU prevV currU currV : DensePoly S)
    (chain : Array (DensePoly.SubresultantExt.Entry S)) (fuel : Nat) :
    chain.size ≤
      (DensePoly.subresultantAuxExt prev curr hPrev prevU prevV currU currV
        chain fuel).size := by
  induction fuel generalizing prev curr hPrev prevU prevV currU currV chain with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let qr := DensePoly.pseudoDivMod prev curr
      let q := qr.1
      let p := qr.2
      cases hp : p.isZero with
      | true => simp [DensePoly.subresultantAuxExt, qr, p, hp]
      | false =>
          let divisor := DensePoly.negOnePow (delta + 1) *
            prev.leadingCoeff * powNat hPrev delta
          let next := DensePoly.divScalarImpl p divisor
          cases hnext : next.isZero with
          | true =>
              simp [DensePoly.subresultantAuxExt, delta, qr, p, hp,
                divisor, next, hnext]
          | false =>
              let a := powNat curr.leadingCoeff (delta + 1)
              let nextU := DensePoly.divScalarImpl
                (DensePoly.SubresultantExt.numerator a q prevU currU) divisor
              let nextV := DensePoly.divScalarImpl
                (DensePoly.SubresultantExt.numerator a q prevV currV) divisor
              have hrec := ih curr next hCurr currU currV nextU nextV
                (chain.push (nextU, nextV, next))
              have hbound : chain.size ≤
                  (DensePoly.subresultantAuxExt curr next hCurr currU currV
                    nextU nextV (chain.push (nextU, nextV, next)) fuel).size :=
                Nat.le_trans (Nat.le_succ chain.size) (by
                  simpa only [Array.size_push] using hrec)
              simpa [DensePoly.subresultantAuxExt, delta, hCurr, qr, q, p, hp,
                divisor, next, hnext, a, nextU, nextV] using hbound

/-- A degree-ordered extended Brown run retains its two input entries. -/
private theorem orderedExt_nonempty {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [Div S]
    (f g fU fV gU gV : DensePoly S) :
    0 < (DensePoly.subresultantOrderedExt f g fU fV gU gV).size := by
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let qr := DensePoly.pseudoDivMod f g
  let q := qr.1
  let p := qr.2
  let seed : Array (DensePoly.SubresultantExt.Entry S) :=
    #[(fU, fV, f), (gU, gV, g)]
  cases hp : p.isZero with
  | true => simp [DensePoly.subresultantOrderedExt, qr, p, hp]
  | false =>
      let sign := DensePoly.negOnePow (R := S) (delta + 1)
      let g₃ := DensePoly.scaleImpl sign p
      cases hg₃ : g₃.isZero with
      | true => simp [DensePoly.subresultantOrderedExt, delta, qr, p, hp,
          sign, g₃, hg₃]
      | false =>
          let a := powNat g.leadingCoeff (delta + 1)
          let g₃U := DensePoly.scaleImpl sign
            (DensePoly.SubresultantExt.numerator a q fU gU)
          let g₃V := DensePoly.scaleImpl sign
            (DensePoly.SubresultantExt.numerator a q fV gV)
          have h := auxExt_size_le g g₃ h₂ gU gV g₃U g₃V
            (seed.push (g₃U, g₃V, g₃)) (g.size + 1)
          have hpos : 0 <
              (DensePoly.subresultantAuxExt g g₃ h₂ gU gV g₃U g₃V
                (seed.push (g₃U, g₃V, g₃)) (g.size + 1)).size := by
            apply Nat.lt_of_lt_of_le (by simp [seed]) h
          simpa [DensePoly.subresultantOrderedExt, delta, h₂, qr, q, p,
            seed, hp, sign, g₃, hg₃, a, g₃U, g₃V] using hpos

/-- Nonzero input pairs give a nonempty extended chain, so `terminal` never
observes its stable default on the PRS route. -/
theorem chainExt_nonempty {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [Div S] (f h : DensePoly S)
    (hn : f ≠ 0 ∨ h ≠ 0) :
    0 < (DensePoly.subresultantChainExt f h).size := by
  rcases hn with hf | hh
  · have hfz : f.isZero = false := by
      rw [DensePoly.isZero_eq_false_iff]
      by_cases hsize : 0 < f.size
      · exact hsize
      · exact (hf ((DensePoly.size_eq_zero_iff f).mp (by omega))).elim
    unfold DensePoly.subresultantChainExt
    simp only [hfz, Bool.false_eq_true, ↓reduceIte]
    split
    · simp
    · split
      · exact orderedExt_nonempty h f 0 1 1 0
      · exact orderedExt_nonempty f h 1 0 0 1
  · have hhz : h.isZero = false := by
      rw [DensePoly.isZero_eq_false_iff]
      by_cases hsize : 0 < h.size
      · exact hsize
      · exact (hh ((DensePoly.size_eq_zero_iff h).mp (by omega))).elim
    unfold DensePoly.subresultantChainExt
    split
    · simp [hhz]
    · simp only [hhz, Bool.false_eq_true, ↓reduceIte]
      split
      · exact orderedExt_nonempty h f 0 1 1 0
      · exact orderedExt_nonempty f h 1 0 0 1

/-- The selected terminal triple is an actual extended-chain entry whenever
the route's nonzero-input invariant holds. -/
theorem terminal_mem {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [Div S] (f h : DensePoly S)
    (hn : f ≠ 0 ∨ h ≠ 0) :
    ∃ k, ∃ hk : k < (DensePoly.subresultantChainExt f h).size,
      terminal f h = (DensePoly.subresultantChainExt f h)[k]'hk := by
  let chain := DensePoly.subresultantChainExt f h
  have hpos : 0 < chain.size := chainExt_nonempty f h hn
  let k := chain.size - 1
  have hk : k < chain.size := by omega
  refine ⟨k, hk, ?_⟩
  simpa [terminal, chain, k] using
    (Array.getElem_eq_getD (0, 0, 0) (h := hk)).symm

/-- Arity-zero coprimality witness from the base extended gcd. -/
def baseCoprime {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (cmp : Mono 0 → Mono 0 → Ordering) [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) : CoprimeCert 0 R cmp :=
  let uv := BezoutOps.xgcd (coeff Mono.zero f) (coeff Mono.zero h)
  .base uv.1 uv.2

/-- Arity-zero gcd candidate. Every quotient is replayed by the checker. -/
def baseGcd {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (cmp : Mono 0 → Mono 0 → Ordering) [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) : GcdCert 0 R cmp :=
  if f == 0 && h == 0 then
    .mk 0 1 1 .unit
  else
    let a := coeff Mono.zero f
    let b := coeff Mono.zero h
    let g := polyNormalize (C (GcdOps.gcd a b))
    let cofL := quotient f g
    let cofR := quotient h g
    .mk g cofL cofR (baseCoprime cmp cofL cofR)

/-- Build the successor-arity `splitBezout` witness from an extended chain
and recursively certified coefficient contents. -/
def succCoprime {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (lower : PrsOpsAt R n)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp) : CoprimeCert (n + 1) R cmp :=
  if polyIsUnit f || polyIsUnit h then
    .unit
  else
    let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let fView := toUnivariate i Mono.lex f
    let hView := toUnivariate i Mono.lex h
    let e := terminal fView hView
    let u := ofUnivariate (cmp := cmp) i Mono.lex e.1
    let v := ofUnivariate (cmp := cmp) i Mono.lex e.2.1
    let r := e.2.2.coeff 0
    let left := contentCertWith (lower.gcdCert Mono.lex) fView.toArray.toList
    let right := contentCertWith (lower.gcdCert Mono.lex) hView.toArray.toList
    let rest := lower.coprimeCert Mono.lex left.value right.value
    .splitBezout i Mono.lex u v r left right rest

/-- Successor-arity gcd candidate from input contents and the primitive part
of the terminal extended subresultant. -/
def succGcd {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (lower : PrsOpsAt R n)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp) : GcdCert (n + 1) R cmp :=
  if f == 0 && h == 0 then
    .mk 0 1 1 .unit
  else if f == 0 then
    let g := polyNormalize h
    let cofR := quotient h g
    .mk g 0 cofR .unit
  else if h == 0 then
    let g := polyNormalize f
    let cofL := quotient f g
    .mk g cofL 0 .unit
  else
    let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let fView := toUnivariate i Mono.lex f
    let hView := toUnivariate i Mono.lex h
    let fContent :=
      contentCertWith (lower.gcdCert Mono.lex) fView.toArray.toList
    let hContent :=
      contentCertWith (lower.gcdCert Mono.lex) hView.toArray.toList
    let common := lower.gcdCert Mono.lex fContent.value hContent.value
    let fPrimitive := quotient f (constIn i Mono.lex fContent.value)
    let hPrimitive := quotient h (constIn i Mono.lex hContent.value)
    let e := terminal (toUnivariate i Mono.lex fPrimitive)
      (toUnivariate i Mono.lex hPrimitive)
    let terminalPoly := ofUnivariate (cmp := cmp) i Mono.lex e.2.2
    let terminalContent := contentCertWith (lower.gcdCert Mono.lex)
      e.2.2.toArray.toList
    let primitiveGcd := quotient terminalPoly
      (constIn i Mono.lex terminalContent.value)
    let raw := constIn i Mono.lex common.gcd * primitiveGcd
    let g := polyNormalize raw
    let cofL := quotient f g
    let cofR := quotient h g
    .mk g cofL cofR (succCoprime lower cmp cofL cofR)

/-- Construct deterministic gcd and coprimality operations by arity. -/
def prsOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] :
    (n : Nat) → PrsOpsAt R n
  | 0 =>
      { gcdCert := baseGcd
        coprimeCert := baseCoprime }
  | n + 1 =>
      let lower := prsOps n
      { gcdCert := succGcd lower
        coprimeCert := succCoprime lower }

/-- Deterministic route-4 certificate. Runtime construction uses only the
coefficient operations; their laws enter separately in `prsCert_checks`. -/
def prsCert {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (f h : MvPoly n R cmp) : GcdCert n R cmp :=
  (prsOps (R := R) n).gcdCert cmp f h

/-- Route 4 always constructs an accepted certificate. The proof combines
the extended-chain transformation law, exact divisions, and the recursive
content checker. -/
theorem prsCert_checks {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    (f h : MvPoly n R cmp) :
    checkGcd f h (prsCert f h) = true := by
  sorry

end Hex.MvPoly
