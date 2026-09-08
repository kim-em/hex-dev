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
structure PrsOpsAt (R : Type u) [Lean.Grind.CommRing R] (n : Nat) : Type (u + 1) where
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

private theorem dvd_polyNormalize_prs {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : p ∣ polyNormalize p := by
  refine ⟨polyNormUnit p, ?_⟩
  unfold polyNormalize
  exact MvPoly.mul_comm p (polyNormUnit p)

private theorem polyNormalize_dvd_prs {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : polyNormalize p ∣ p := by
  rcases (polyIsUnit_iff (polyNormUnit p)).mp (polyNormUnit_isUnit p) with
    ⟨v, hv⟩
  refine ⟨v, ?_⟩
  unfold polyNormalize
  grind

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

/-- The selected terminal entry retains its Bezout identity. -/
theorem terminal_bezout {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] [Div S] [ExactDivLaws S]
    (f h : DensePoly S) (hn : f ≠ 0 ∨ h ≠ 0) :
    let e := terminal f h
    e.1 * f + e.2.1 * h = e.2.2 := by
  rcases terminal_mem f h hn with ⟨k, hk, heq⟩
  have hmem : terminal f h ∈ DensePoly.subresultantChainExt f h := by
    rw [heq]
    exact Array.getElem_mem hk
  exact DensePoly.subresultantChainExt_bezout f h (terminal f h) hmem

/-! # Fraction-field meaning of the terminal PRS value -/

private def lastExt {S : Type u} [Zero S] [DecidableEq S]
    (chain : Array (DensePoly.SubresultantExt.Entry S)) : DensePoly S :=
  DensePoly.SubresultantExt.value
    (chain.getD (chain.size - 1) (0, 0, 0))

private theorem lastExt_push {S : Type u} [Zero S] [DecidableEq S]
    (chain : Array (DensePoly.SubresultantExt.Entry S))
    (e : DensePoly.SubresultantExt.Entry S) :
    lastExt (chain.push e) = DensePoly.SubresultantExt.value e := by
  unfold lastExt
  have hi : chain.size < (chain.push e).size := by simp
  have hindex : (chain.push e).size - 1 = chain.size := by simp
  rw [hindex, ← Array.getElem_eq_getD (0, 0, 0) (h := hi),
    Array.getElem_push_eq]

private theorem denseScale_one {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p : DensePoly S) : DensePoly.scale 1 p = p := by
  apply DensePoly.ext_coeff
  intro k
  rw [DensePoly.coeff_scale_semiring]
  exact Lean.Grind.Semiring.one_mul _

private theorem denseScale_eq_C_mul {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (a : S) (p : DensePoly S) :
    DensePoly.scale a p = DensePoly.C a * p := by
  have h : DensePoly.scale a (1 : DensePoly S) = DensePoly.C a := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_scale_semiring]
    change a * (DensePoly.C 1).coeff i = (DensePoly.C a).coeff i
    simp only [DensePoly.coeff_C]
    split
    · exact Lean.Grind.Semiring.mul_one a
    · exact Lean.Grind.Semiring.mul_zero a
  rw [← h, ← DensePoly.scale_mul]
  congr 1
  grind

private theorem denseDvd_scale {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] {d p : DensePoly S} (c : S) (hd : d ∣ p) :
    d ∣ DensePoly.scale c p := by
  rcases hd with ⟨q, hq⟩
  refine ⟨DensePoly.scale c q, ?_⟩
  calc
    DensePoly.scale c p = DensePoly.scale c (d * q) := by rw [hq]
    _ = d * DensePoly.scale c q := DensePoly.mul_scale c d q

private theorem denseDvd_of_scale {S : Type u} [Lean.Grind.Field S]
    [DecidableEq S] {d p : DensePoly S} {c : S} (hc : c ≠ 0)
    (hd : d ∣ DensePoly.scale c p) : d ∣ p := by
  rcases hd with ⟨q, hq⟩
  refine ⟨DensePoly.scale c⁻¹ q, ?_⟩
  calc
    p = DensePoly.scale 1 p := (denseScale_one p).symm
    _ = DensePoly.scale (c⁻¹ * c) p := by
      rw [Lean.Grind.Field.inv_mul_cancel hc]
    _ = DensePoly.scale c⁻¹ (DensePoly.scale c p) :=
      (DensePoly.scale_scale c⁻¹ c p).symm
    _ = DensePoly.scale c⁻¹ (d * q) := by rw [hq]
    _ = d * DensePoly.scale c⁻¹ q := DensePoly.mul_scale c⁻¹ d q

private theorem denseDvd_refl {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p : DensePoly S) : p ∣ p := by
  exact DensePoly.dvd_refl_poly p

private theorem denseDvd_trans {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] {a b c : DensePoly S} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc
    c = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := DensePoly.mul_assoc_poly _ _ _

private theorem pseudoDvd_left_fraction {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    [Hex.Fraction.NonzeroOne S]
    (f g : DensePoly S) (hg : g ≠ 0) (hgf : g.size ≤ f.size)
    {d : DensePoly (Hex.Fraction S)}
    (hdg : d ∣ DensePoly.Fraction.map g)
    (hdp : d ∣ DensePoly.Fraction.map (DensePoly.pseudoDivMod f g).2) :
    d ∣ DensePoly.Fraction.map f := by
  let c := g.leadingCoeff ^ (f.size - g.size + 1)
  have hgpos : 0 < g.size := Nat.pos_of_ne_zero fun hz =>
    hg ((DensePoly.size_eq_zero_iff g).mp hz)
  have hlc : g.leadingCoeff ≠ 0 :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size g hgpos
  have hc : c ≠ 0 :=
    Hex.pow_ne_zero Hex.Fraction.NonzeroOne.one_ne_zero hlc _
  have hcMap : Hex.Fraction.ofCoeff c ≠ (0 : Hex.Fraction S) := by
    intro hz
    exact hc ((Hex.Fraction.ofCoeff_eq_zero_iff c).mp hz)
  have hpseudo := DensePoly.pseudoDivMod_reconstruct f g hg hgf
  have hmap := congrArg DensePoly.Fraction.map hpseudo
  rw [DensePoly.Fraction.map_scale, DensePoly.Fraction.map_add,
    DensePoly.Fraction.map_mul] at hmap
  have hsum : d ∣
      DensePoly.Fraction.map (DensePoly.pseudoDivMod f g).1 *
          DensePoly.Fraction.map g +
        DensePoly.Fraction.map (DensePoly.pseudoDivMod f g).2 :=
    DensePoly.dvd_add_poly (DensePoly.dvd_mul_left_poly _ hdg) hdp
  apply denseDvd_of_scale hcMap
  change d ∣ DensePoly.scale
    (Hex.Fraction.ofCoeff (g.leadingCoeff ^ (f.size - g.size + 1)))
      (DensePoly.Fraction.map f)
  rw [hmap]
  exact hsum

private theorem auxExt_last_dvd_fraction {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    [Hex.Fraction.NonzeroOne S]
    (prev curr : DensePoly S) (hPrev : S)
    (prevU prevV currU currV : DensePoly S)
    (chain : Array (DensePoly.SubresultantExt.Entry S)) (fuel : Nat)
    (hbrown : DensePoly.BrownLaw prev curr hPrev fuel)
    (hpos : 0 < chain.size) (hlast : lastExt chain = curr) :
    let out := DensePoly.subresultantAuxExt prev curr hPrev
      prevU prevV currU currV chain fuel
    DensePoly.Fraction.map (lastExt out) ∣ DensePoly.Fraction.map prev ∧
      DensePoly.Fraction.map (lastExt out) ∣ DensePoly.Fraction.map curr := by
  induction fuel generalizing prev curr hPrev prevU prevV currU currV chain with
  | zero => simp [DensePoly.BrownLaw] at hbrown
  | succ fuel ih =>
      simp only [DensePoly.BrownLaw] at hbrown
      rcases hbrown with ⟨hprev, hcurr, hsize, hhPrev, hhCurr,
        hscale, hstep⟩
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let qr := DensePoly.pseudoDivMod prev curr
      let q := qr.1
      let p := qr.2
      cases hpzero : p.isZero with
      | true =>
          have hp : p = 0 := by
            apply (DensePoly.size_eq_zero_iff p).mp
            exact (DensePoly.isZero_eq_true_iff p).mp hpzero
          let c := curr.leadingCoeff ^ (prev.size - curr.size + 1)
          have hcurrPos : 0 < curr.size := by
            exact Nat.pos_of_ne_zero fun hz =>
              hcurr ((DensePoly.size_eq_zero_iff curr).mp hz)
          have hlc : curr.leadingCoeff ≠ 0 :=
            DensePoly.leadingCoeff_ne_zero_of_pos_size curr hcurrPos
          have hc : c ≠ 0 := by
            exact Hex.pow_ne_zero Hex.Fraction.NonzeroOne.one_ne_zero hlc _
          have hcMap : Hex.Fraction.ofCoeff c ≠ (0 : Hex.Fraction S) := by
            intro hz
            exact hc ((Hex.Fraction.ofCoeff_eq_zero_iff c).mp hz)
          have hrec := DensePoly.pseudoDivMod_reconstruct prev curr hcurr
            (Nat.le_of_lt hsize)
          have hpRaw : qr.2 = 0 := by simpa only [p] using hp
          rw [hpRaw] at hrec
          have hrecMap := congrArg DensePoly.Fraction.map hrec
          have hscaleDvd : DensePoly.Fraction.map curr ∣
              DensePoly.scale (Hex.Fraction.ofCoeff c)
                (DensePoly.Fraction.map prev) := by
            refine ⟨DensePoly.Fraction.map q, ?_⟩
            calc
              DensePoly.scale (Hex.Fraction.ofCoeff c)
                  (DensePoly.Fraction.map prev) =
                  DensePoly.Fraction.map (qr.1 * curr + 0) := by
                simpa only [c, DensePoly.Fraction.map_scale,
                  Hex.Fraction.ofCoeff_pow] using hrecMap
              _ = DensePoly.Fraction.map q *
                    DensePoly.Fraction.map curr := by
                simp only [q, DensePoly.Fraction.map_add,
                  DensePoly.Fraction.map_mul, DensePoly.Fraction.map_zero,
                  DensePoly.add_zero_poly]
              _ = DensePoly.Fraction.map curr *
                    DensePoly.Fraction.map q :=
                DensePoly.mul_comm_poly _ _
          have hdprev : DensePoly.Fraction.map curr ∣
              DensePoly.Fraction.map prev :=
            denseDvd_of_scale hcMap hscaleDvd
          simp only [DensePoly.subresultantAuxExt, delta, hCurr, qr, q, p,
            hpzero, ↓reduceIte]
          rw [hlast]
          exact ⟨hdprev, denseDvd_refl _⟩
      | false =>
          let divisor := DensePoly.negOnePow (delta + 1) *
            prev.leadingCoeff * powNat hPrev delta
          let next := DensePoly.divScalar p divisor
          have hpzeroRaw : (DensePoly.pseudoDivMod prev curr).2.isZero = false := by
            simpa only [p, qr] using hpzero
          simp only [hpzeroRaw, Bool.false_eq_true, ↓reduceIte] at hstep
          have hstep' : divisor ≠ 0 ∧ p = DensePoly.scale divisor next ∧
              next ≠ 0 ∧ DensePoly.BrownLaw curr next hCurr fuel := by
            simpa only [p, qr, divisor, next, delta, hCurr] using hstep
          rcases hstep' with ⟨hdivisor, hpScale, hnext, hnextLaw⟩
          let nextImpl := DensePoly.divScalarImpl p divisor
          have hnextImpl : nextImpl = next := by
            exact (DensePoly.divScalar_eq_divScalarImpl p divisor).symm
          have hnextZero : nextImpl.isZero = false := by
            cases hz : nextImpl.isZero with
            | false => rfl
            | true =>
                exfalso
                apply hnext
                rw [← hnextImpl]
                apply (DensePoly.size_eq_zero_iff nextImpl).mp
                exact (DensePoly.isZero_eq_true_iff nextImpl).mp hz
          let a := powNat curr.leadingCoeff (delta + 1)
          let nextU := DensePoly.divScalarImpl
            (DensePoly.SubresultantExt.numerator a q prevU currU) divisor
          let nextV := DensePoly.divScalarImpl
            (DensePoly.SubresultantExt.numerator a q prevV currV) divisor
          let entry : DensePoly.SubresultantExt.Entry S :=
            (nextU, nextV, next)
          have hlastPush : lastExt (chain.push entry) = next := by
            exact lastExt_push chain entry
          have hrec := ih curr next hCurr currU currV nextU nextV
            (chain.push entry) hnextLaw (by simp) hlastPush
          let out := DensePoly.subresultantAuxExt curr next hCurr
            currU currV nextU nextV (chain.push entry) fuel
          have hrec' : DensePoly.Fraction.map (lastExt out) ∣
                DensePoly.Fraction.map curr ∧
              DensePoly.Fraction.map (lastExt out) ∣
                DensePoly.Fraction.map next := by
            simpa only [out] using hrec
          have hdp : DensePoly.Fraction.map (lastExt out) ∣
              DensePoly.Fraction.map p := by
            rw [hpScale, DensePoly.Fraction.map_scale]
            exact denseDvd_scale _ hrec'.2
          let c := curr.leadingCoeff ^ (prev.size - curr.size + 1)
          have hcurrPos : 0 < curr.size := by
            exact Nat.pos_of_ne_zero fun hz =>
              hcurr ((DensePoly.size_eq_zero_iff curr).mp hz)
          have hlc : curr.leadingCoeff ≠ 0 :=
            DensePoly.leadingCoeff_ne_zero_of_pos_size curr hcurrPos
          have hc : c ≠ 0 := by
            exact Hex.pow_ne_zero Hex.Fraction.NonzeroOne.one_ne_zero hlc _
          have hcMap : Hex.Fraction.ofCoeff c ≠ (0 : Hex.Fraction S) := by
            intro hz
            exact hc ((Hex.Fraction.ofCoeff_eq_zero_iff c).mp hz)
          have hpseudo := DensePoly.pseudoDivMod_reconstruct prev curr hcurr
            (Nat.le_of_lt hsize)
          have hdscale : DensePoly.Fraction.map (lastExt out) ∣
              DensePoly.scale (Hex.Fraction.ofCoeff c)
                (DensePoly.Fraction.map prev) := by
            have hsum : DensePoly.Fraction.map (lastExt out) ∣
                DensePoly.Fraction.map q * DensePoly.Fraction.map curr +
                  DensePoly.Fraction.map p :=
              DensePoly.dvd_add_poly
                (DensePoly.dvd_mul_left_poly _ hrec'.1) hdp
            have hmap := congrArg DensePoly.Fraction.map hpseudo
            rw [DensePoly.Fraction.map_scale, DensePoly.Fraction.map_add,
              DensePoly.Fraction.map_mul] at hmap
            have hdmap : DensePoly.Fraction.map (lastExt out) ∣
                DensePoly.Fraction.map
                  (DensePoly.scale
                    (curr.leadingCoeff ^ (prev.size - curr.size + 1)) prev) := by
              rw [DensePoly.Fraction.map_scale, hmap]
              simpa only [q, p, qr] using hsum
            simpa only [c, DensePoly.Fraction.map_scale] using hdmap
          have hdprev : DensePoly.Fraction.map (lastExt out) ∣
              DensePoly.Fraction.map prev := denseDvd_of_scale hcMap hdscale
          have hout : DensePoly.subresultantAuxExt prev curr hPrev
              prevU prevV currU currV chain (fuel + 1) = out := by
            simp only [DensePoly.subresultantAuxExt, hpzeroRaw,
              Bool.false_eq_true, ↓reduceIte]
            change (if nextImpl.isZero = true then chain else
              DensePoly.subresultantAuxExt curr nextImpl hCurr
                currU currV nextU nextV
                (chain.push (nextU, nextV, nextImpl)) fuel) = out
            rw [hnextZero]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hnextImpl]
          rw [hout]
          exact ⟨hdprev, hrec'.1⟩

private theorem orderedExt_last_dvd_fraction {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    [Hex.Fraction.NonzeroOne S]
    (f g fU fV gU gV : DensePoly S) (hg : g ≠ 0)
    (hgf : g.size ≤ f.size) :
    let out := DensePoly.subresultantOrderedExt f g fU fV gU gV
    DensePoly.Fraction.map (lastExt out) ∣ DensePoly.Fraction.map f ∧
      DensePoly.Fraction.map (lastExt out) ∣ DensePoly.Fraction.map g := by
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let qr := DensePoly.pseudoDivMod f g
  let q := qr.1
  let p := qr.2
  let seed : Array (DensePoly.SubresultantExt.Entry S) :=
    #[(fU, fV, f), (gU, gV, g)]
  have hbrown := DensePoly.subresultantOrdered_brownLaw f g hg hgf
  cases hpzero : p.isZero with
  | true =>
      have hp : p = 0 := by
        apply (DensePoly.size_eq_zero_iff p).mp
        exact (DensePoly.isZero_eq_true_iff p).mp hpzero
      have hdp : DensePoly.Fraction.map g ∣
          DensePoly.Fraction.map (DensePoly.pseudoDivMod f g).2 := by
        rw [show (DensePoly.pseudoDivMod f g).2 = 0 by simpa only [p, qr] using hp,
          DensePoly.Fraction.map_zero]
        exact DensePoly.dvd_zero_poly _
      have hdf := pseudoDvd_left_fraction f g hg hgf
        (denseDvd_refl _) hdp
      have hout : DensePoly.subresultantOrderedExt f g fU fV gU gV = seed := by
        simp only [DensePoly.subresultantOrderedExt, delta, h₂, qr, q, p,
          seed, hpzero, ↓reduceIte]
      have hlastSeed : lastExt seed = g := by
        exact lastExt_push #[(fU, fV, f)] (gU, gV, g)
      rw [hout]
      change DensePoly.Fraction.map (lastExt seed) ∣
          DensePoly.Fraction.map f ∧
        DensePoly.Fraction.map (lastExt seed) ∣ DensePoly.Fraction.map g
      rw [hlastSeed]
      exact ⟨hdf, denseDvd_refl _⟩
  | false =>
      let sign := DensePoly.negOnePow (R := S) (delta + 1)
      let g₃ := DensePoly.scaleImpl sign p
      have hbranch : g₃ ≠ 0 ∧ DensePoly.BrownLaw g g₃ h₂ (g.size + 1) := by
        simpa only [delta, h₂, p, qr, hpzero, Bool.false_eq_true,
          ↓reduceIte, sign, g₃] using hbrown
      rcases hbranch with ⟨hg₃, hg₃law⟩
      have hg₃zero : g₃.isZero = false := by
        rw [DensePoly.isZero_eq_false_iff]
        exact Nat.pos_of_ne_zero fun hz =>
          hg₃ ((DensePoly.size_eq_zero_iff g₃).mp hz)
      let a := powNat g.leadingCoeff (delta + 1)
      let g₃U := DensePoly.scaleImpl sign
        (DensePoly.SubresultantExt.numerator a q fU gU)
      let g₃V := DensePoly.scaleImpl sign
        (DensePoly.SubresultantExt.numerator a q fV gV)
      let entry : DensePoly.SubresultantExt.Entry S := (g₃U, g₃V, g₃)
      let chain := seed.push entry
      have hlast : lastExt chain = g₃ := lastExt_push seed entry
      have hrec := auxExt_last_dvd_fraction g g₃ h₂ gU gV g₃U g₃V
        chain (g.size + 1) hg₃law (by simp [chain, seed]) hlast
      let out := DensePoly.subresultantAuxExt g g₃ h₂ gU gV g₃U g₃V
        chain (g.size + 1)
      have hrec' : DensePoly.Fraction.map (lastExt out) ∣
            DensePoly.Fraction.map g ∧
          DensePoly.Fraction.map (lastExt out) ∣
            DensePoly.Fraction.map g₃ := by
        simpa only [out] using hrec
      have hsign : sign ≠ 0 := by
        exact DensePoly.negOnePow_ne_zero Hex.Fraction.NonzeroOne.one_ne_zero _
      have hsignMap : Hex.Fraction.ofCoeff sign ≠ (0 : Hex.Fraction S) := by
        intro hz
        exact hsign ((Hex.Fraction.ofCoeff_eq_zero_iff sign).mp hz)
      have hdp : DensePoly.Fraction.map (lastExt out) ∣
          DensePoly.Fraction.map (DensePoly.pseudoDivMod f g).2 := by
        have hg₃eq : g₃ = DensePoly.scale sign p := by
          exact (DensePoly.scale_eq_scaleImpl sign p).symm
        have hdscale : DensePoly.Fraction.map (lastExt out) ∣
            DensePoly.scale (Hex.Fraction.ofCoeff sign)
              (DensePoly.Fraction.map p) := by
          rw [← DensePoly.Fraction.map_scale, ← hg₃eq]
          exact hrec'.2
        have := denseDvd_of_scale hsignMap hdscale
        simpa only [p, qr] using this
      have hdf := pseudoDvd_left_fraction f g hg hgf hrec'.1 hdp
      have houtEq : DensePoly.subresultantOrderedExt f g fU fV gU gV = out := by
        simp only [DensePoly.subresultantOrderedExt, delta, h₂, qr, q, p,
          seed, hpzero, Bool.false_eq_true, ↓reduceIte, sign, g₃, hg₃zero,
          a, g₃U, g₃V, entry, chain, out]
      rw [houtEq]
      exact ⟨hdf, hrec'.1⟩

private theorem chainExt_last_dvd_fraction {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    [Hex.Fraction.NonzeroOne S]
    (f g : DensePoly S) (hn : f ≠ 0 ∨ g ≠ 0) :
    let chain := DensePoly.subresultantChainExt f g
    DensePoly.Fraction.map (lastExt chain) ∣ DensePoly.Fraction.map f ∧
      DensePoly.Fraction.map (lastExt chain) ∣ DensePoly.Fraction.map g := by
  cases hf : f.isZero with
  | true =>
      have hf0 : f = 0 := by
        apply (DensePoly.size_eq_zero_iff f).mp
        exact (DensePoly.isZero_eq_true_iff f).mp hf
      have hg0 : g ≠ 0 := hn.resolve_left (fun h => h hf0)
      have hgf : g.isZero = false := by
        rw [DensePoly.isZero_eq_false_iff]
        exact Nat.pos_of_ne_zero fun hz =>
          hg0 ((DensePoly.size_eq_zero_iff g).mp hz)
      simp only [DensePoly.subresultantChainExt, hf, hgf,
        Bool.false_eq_true, ↓reduceIte]
      have hlast : lastExt #[(0, 1, g)] = g :=
        lastExt_push #[] (0, 1, g)
      rw [hlast, hf0, DensePoly.Fraction.map_zero]
      exact ⟨DensePoly.dvd_zero_poly _, denseDvd_refl _⟩
  | false =>
      have hf0 : f ≠ 0 := by
        intro hz
        subst f
        have : (0 : DensePoly S).isZero = true := rfl
        rw [this] at hf
        contradiction
      cases hg : g.isZero with
      | true =>
          have hg0 : g = 0 := by
            apply (DensePoly.size_eq_zero_iff g).mp
            exact (DensePoly.isZero_eq_true_iff g).mp hg
          simp only [DensePoly.subresultantChainExt, hf,
            Bool.false_eq_true, hg, ↓reduceIte]
          have hlast : lastExt #[(1, 0, f)] = f :=
            lastExt_push #[] (1, 0, f)
          rw [hlast, hg0, DensePoly.Fraction.map_zero]
          exact ⟨denseDvd_refl _, DensePoly.dvd_zero_poly _⟩
      | false =>
          have hg0 : g ≠ 0 := by
            intro hz
            subst g
            have : (0 : DensePoly S).isZero = true := rfl
            rw [this] at hg
            contradiction
          by_cases hfg : f.size < g.size
          · have hord := orderedExt_last_dvd_fraction g f 0 1 1 0 hf0
              (Nat.le_of_lt hfg)
            simp only [DensePoly.subresultantChainExt, hf,
              Bool.false_eq_true, hg, hfg, ↓reduceIte]
            exact ⟨hord.2, hord.1⟩
          · have hgf : g.size ≤ f.size := by omega
            have hord := orderedExt_last_dvd_fraction f g 1 0 0 1 hg0 hgf
            simp only [DensePoly.subresultantChainExt, hf,
              Bool.false_eq_true, hg, hfg, ↓reduceIte]
            exact hord

/-- The terminal nonzero Brown remainder divides both inputs after extending
coefficients to the fraction field. -/
theorem terminal_dvd_fraction {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    [Hex.Fraction.NonzeroOne S]
    (f g : DensePoly S) (hn : f ≠ 0 ∨ g ≠ 0) :
    DensePoly.Fraction.map (terminal f g).2.2 ∣ DensePoly.Fraction.map f ∧
      DensePoly.Fraction.map (terminal f g).2.2 ∣ DensePoly.Fraction.map g := by
  simpa only [terminal, lastExt, DensePoly.SubresultantExt.value] using
    chainExt_last_dvd_fraction f g hn

private theorem terminal_ne_zero {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hn : f ≠ 0 ∨ g ≠ 0) :
    (terminal f g).2.2 ≠ 0 := by
  let e := terminal f g
  let t := e.2.2
  have htMem : t ∈ DensePoly.subresultantChain f g := by
    rcases terminal_mem f g hn with ⟨k, hk, heq⟩
    have heMem : e ∈ DensePoly.subresultantChainExt f g := by
      change terminal f g ∈ DensePoly.subresultantChainExt f g
      rw [heq]
      exact Array.getElem_mem hk
    have hmapMem : t ∈
        (DensePoly.subresultantChainExt f g).map
          DensePoly.SubresultantExt.value := by
      apply Array.mem_def.mpr
      simp only [Array.toList_map]
      exact List.mem_map.mpr ⟨e, Array.mem_def.mp heMem, rfl⟩
    rw [DensePoly.subresultantChainExt_values] at hmapMem
    exact hmapMem
  exact DensePoly.subresultantChain_ne_zero f g t htMem

private theorem fraction_dvd_cancel_const {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Dvd S] [Div S]
    [GcdDomainLaws S] [ExactDivLaws S] [Hex.Fraction.NonzeroOne S]
    {q f : DensePoly S} {c : S}
    (hc : c ≠ 0) (hrec : q * DensePoly.C c = f)
    {e : DensePoly (Hex.Fraction S)}
    (hef : e ∣ DensePoly.Fraction.map f) :
    e ∣ DensePoly.Fraction.map q := by
  rcases hef with ⟨x, hx⟩
  let cF := Hex.Fraction.ofCoeff c
  let inv := cF⁻¹
  have hcF : cF ≠ 0 := fun hz =>
    hc ((Hex.Fraction.ofCoeff_eq_zero_iff c).mp hz)
  have hcinv : cF * inv = 1 := Hex.Fraction.mul_inv_cancel hcF
  refine ⟨x * DensePoly.C inv, ?_⟩
  have hmapRec := congrArg DensePoly.Fraction.map hrec
  rw [DensePoly.Fraction.map_mul, DensePoly.Fraction.map_C] at hmapRec
  calc
    DensePoly.Fraction.map q = DensePoly.Fraction.map q * 1 :=
      (DensePoly.mul_one_right_poly _).symm
    _ = DensePoly.Fraction.map q * DensePoly.C (cF * inv) := by
      rw [hcinv]
      rfl
    _ = DensePoly.Fraction.map q *
        (DensePoly.C cF * DensePoly.C inv) := by
      rw [DensePoly.C_mul_C]
    _ = (DensePoly.Fraction.map q * DensePoly.C cF) *
        DensePoly.C inv := (DensePoly.mul_assoc_poly _ _ _).symm
    _ = DensePoly.Fraction.map f * DensePoly.C inv := by rw [hmapRec]
    _ = (e * x) * DensePoly.C inv := by rw [← hx]
    _ = e * (x * DensePoly.C inv) := DensePoly.mul_assoc_poly _ _ _

private theorem ofUnivariate_mul_prs {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (i : Fin (n + 1)) (p q : DensePoly (MvPoly n R cmp')) :
    ofUnivariate (cmp := cmp) i cmp' (p * q) =
      ofUnivariate (cmp := cmp) i cmp' p *
        ofUnivariate (cmp := cmp) i cmp' q := by
  have hinj : Function.Injective
      (toUnivariate (R := R) (cmp := cmp) i cmp') := by
    intro a b hab
    calc
      a = ofUnivariate (cmp := cmp) i cmp' (toUnivariate i cmp' a) :=
        (ofUnivariate_toUnivariate i a).symm
      _ = ofUnivariate (cmp := cmp) i cmp' (toUnivariate i cmp' b) := by
        rw [hab]
      _ = b := ofUnivariate_toUnivariate i b
  apply hinj
  rw [toUnivariate_ofUnivariate, toUnivariate_mul,
    toUnivariate_ofUnivariate, toUnivariate_ofUnivariate]

private theorem ofUnivariate_dvd_prs {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (i : Fin (n + 1)) {p q : DensePoly (MvPoly n R cmp')}
    (h : p ∣ q) :
    ofUnivariate (cmp := cmp) i cmp' p ∣
      ofUnivariate (cmp := cmp) i cmp' q := by
  rcases h with ⟨r, hr⟩
  refine ⟨ofUnivariate (cmp := cmp) i cmp' r, ?_⟩
  calc
    ofUnivariate (cmp := cmp) i cmp' q =
        ofUnivariate (cmp := cmp) i cmp' (p * r) :=
      congrArg (ofUnivariate (cmp := cmp) i cmp') hr
    _ = ofUnivariate (cmp := cmp) i cmp' p *
        ofUnivariate (cmp := cmp) i cmp' r :=
      ofUnivariate_mul_prs i p r
    _ = ofUnivariate (cmp := cmp) i cmp' r *
        ofUnivariate (cmp := cmp) i cmp' p := MvPoly.mul_comm _ _

private theorem toUnivariate_dvd_prs {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    {cmp' : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (i : Fin (n + 1)) {p q : MvPoly (n + 1) R cmp} (h : p ∣ q) :
    toUnivariate i cmp' p ∣ toUnivariate i cmp' q := by
  rcases h with ⟨r, hr⟩
  refine ⟨toUnivariate i cmp' r, ?_⟩
  calc
    toUnivariate i cmp' q = toUnivariate i cmp' (p * r) := by
      rw [hr, MvPoly.mul_comm]
    _ = toUnivariate i cmp' p * toUnivariate i cmp' r :=
      toUnivariate_mul i p r

private theorem fractionMap_dvd_prs {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    [Hex.Fraction.NonzeroOne S]
    {p q : DensePoly S} (h : p ∣ q) :
    DensePoly.Fraction.map p ∣ DensePoly.Fraction.map q := by
  rcases h with ⟨r, hr⟩
  refine ⟨DensePoly.Fraction.map r, ?_⟩
  rw [hr, DensePoly.Fraction.map_mul]

private theorem coprime_nonzero_of_nonunits {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} (hcop : CoprimeCofactors f h)
    (hfUnit : polyIsUnit f = false) (hhUnit : polyIsUnit h = false) :
    f ≠ 0 ∧ h ≠ 0 := by
  constructor
  · intro hf
    subst f
    have hd0 : h ∣ (0 : MvPoly n R cmp) :=
      ⟨0, (MvPoly.zero_mul h).symm⟩
    have hdh : h ∣ h := ⟨1, (MvPoly.one_mul h).symm⟩
    rcases hcop h hd0 hdh with ⟨u, hu⟩
    have : polyIsUnit h = true := (polyIsUnit_iff h).mpr ⟨u, hu⟩
    rw [this] at hhUnit
    contradiction
  · intro hh
    subst h
    have hdf : f ∣ f := ⟨1, (MvPoly.one_mul f).symm⟩
    have hd0 : f ∣ (0 : MvPoly n R cmp) :=
      ⟨0, (MvPoly.zero_mul f).symm⟩
    rcases hcop f hdf hd0 with ⟨u, hu⟩
    have : polyIsUnit f = true := (polyIsUnit_iff f).mpr ⟨u, hu⟩
    rw [this] at hfUnit
    contradiction

private theorem terminal_constant_of_coprime {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp) (hcop : CoprimeCofactors f h)
    (hfUnit : polyIsUnit f = false) (hhUnit : polyIsUnit h = false) :
    let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let fView := toUnivariate i Mono.lex f
    let hView := toUnivariate i Mono.lex h
    let t := (terminal fView hView).2.2
    t = DensePoly.C (t.coeff 0) ∧ t.coeff 0 ≠ 0 := by
  let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let fView := toUnivariate i Mono.lex f
  let hView := toUnivariate i Mono.lex h
  let e := terminal fView hView
  let t := e.2.2
  rcases coprime_nonzero_of_nonunits hcop hfUnit hhUnit with ⟨hf, hh⟩
  have hfView : fView ≠ 0 := by
    intro hz
    apply hf
    rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i f]
    change ofUnivariate (cmp := cmp) i Mono.lex fView = 0
    rw [hz]
    rfl
  have hhView : hView ≠ 0 := by
    intro hz
    apply hh
    rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i h]
    change ofUnivariate (cmp := cmp) i Mono.lex hView = 0
    rw [hz]
    rfl
  letI : Hex.Fraction.NonzeroOne (MvPoly n R Mono.lex) :=
    ⟨GcdDomainLaws.one_ne_zero⟩
  have htDiv := terminal_dvd_fraction fView hView (Or.inl hfView)
  have htMem : t ∈ DensePoly.subresultantChain fView hView := by
    rcases terminal_mem fView hView (Or.inl hfView) with ⟨k, hk, heq⟩
    have heMem : e ∈ DensePoly.subresultantChainExt fView hView := by
      change terminal fView hView ∈ DensePoly.subresultantChainExt fView hView
      rw [heq]
      exact Array.getElem_mem hk
    have hmapMem : t ∈
        (DensePoly.subresultantChainExt fView hView).map
          DensePoly.SubresultantExt.value := by
      apply Array.mem_def.mpr
      simp only [Array.toList_map]
      exact List.mem_map.mpr ⟨e, Array.mem_def.mp heMem, rfl⟩
    rw [DensePoly.subresultantChainExt_values] at hmapMem
    exact hmapMem
  have ht : t ≠ 0 :=
    DensePoly.subresultantChain_ne_zero fView hView t htMem
  let pp := densePrimitivePart t
  have hppF : pp ∣ fView := densePrimPart_descent ht htDiv.1
  have hppH : pp ∣ hView := densePrimPart_descent ht htDiv.2
  let d := ofUnivariate (cmp := cmp) i Mono.lex pp
  have hdf : d ∣ f := by
    have hd := ofUnivariate_dvd_prs (cmp := cmp) i hppF
    simpa only [d, fView, ofUnivariate_toUnivariate] using hd
  have hdh : d ∣ h := by
    have hd := ofUnivariate_dvd_prs (cmp := cmp) i hppH
    simpa only [d, hView, ofUnivariate_toUnivariate] using hd
  rcases hcop d hdf hdh with ⟨w, hw⟩
  have honeView : toUnivariate i Mono.lex (1 : MvPoly (n + 1) R cmp) = 1 := by
    rw [← constIn_one (R := R) (cmp := cmp) (cmp' := Mono.lex) i]
    exact toUnivariate_constIn (cmp := cmp) i 1
  have hppUnit : pp * toUnivariate i Mono.lex w = 1 := by
    calc
      pp * toUnivariate i Mono.lex w =
          toUnivariate i Mono.lex (d * w) := by
        dsimp only [d]
        rw [toUnivariate_mul, toUnivariate_ofUnivariate]
      _ = toUnivariate i Mono.lex 1 := by rw [hw]
      _ = 1 := honeView
  have hmapOne : DensePoly.Fraction.map
      (1 : DensePoly (MvPoly n R Mono.lex)) = 1 := by
    change DensePoly.Fraction.map (DensePoly.C (1 : MvPoly n R Mono.lex)) =
      DensePoly.C (1 : Hex.Fraction (MvPoly n R Mono.lex))
    rw [DensePoly.Fraction.map_C]
    exact congrArg DensePoly.C
      (Hex.Fraction.ofCoeff_one (R := MvPoly n R Mono.lex))
  have hmapUnit : DensePoly.Fraction.map pp *
      DensePoly.Fraction.map (toUnivariate i Mono.lex w) = 1 := by
    rw [← DensePoly.Fraction.map_mul, hppUnit, hmapOne]
  have hppSizeMap := DensePoly.size_eq_one_of_mul_eq_one
    (DensePoly.Fraction.map pp)
    (DensePoly.Fraction.map (toUnivariate i Mono.lex w)) hmapUnit
  have hppSize : pp.size = 1 := by
    simpa only [DensePoly.Fraction.size_map] using hppSizeMap
  have htSizeLe : t.size ≤ pp.size := by
    rw [← denseContent_mul_primitivePart t]
    rw [DensePoly.scale_eq_scaleImpl]
    exact DensePoly.size_scaleImpl_le _ _
  have htPos : 0 < t.size := Nat.pos_of_ne_zero fun hz =>
    ht ((DensePoly.size_eq_zero_iff t).mp hz)
  have htSize : t.size = 1 := by omega
  have htC : t = DensePoly.C (t.coeff 0) := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.coeff_C]
    by_cases hk : k = 0
    · subst k
      rfl
    · rw [ite_eq_right hk]
      exact DensePoly.coeff_eq_zero_of_size_le t (by omega)
  refine ⟨htC, ?_⟩
  intro hc
  apply ht
  rw [htC, hc]
  rfl

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
    let uv := BezoutOps.xgcd a b
    let g := polyNormalize (C (GcdOps.gcd a b))
    let cofL := quotient f g
    let cofR := quotient h g
    .mk g cofL cofR (.base uv.1 uv.2)

private theorem arityZero_eq_C {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    {cmp : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly 0 R cmp) : p = C (coeff Mono.zero p) := by
  apply eq_C_of_vars_eq_nil
  cases h : p.vars with
  | nil => rfl
  | cons i is => exact Fin.elim0 i

private theorem C_mul_C_prs {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (a b : R) : (C a : MvPoly n R cmp) * C b = C (a * b) := by
  unfold C
  rw [monomial_mul_monomial, Mono.zero_mul]

set_option maxHeartbeats 800000 in
private theorem baseGcd_checks {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    (cmp : Mono 0 → Mono 0 → Ordering) [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) :
    checkGcd f h (baseGcd cmp f h) = true := by
  by_cases hzero : f = 0 ∧ h = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp only [baseGcd, beq_self_eq_true, Bool.true_and, ↓reduceIte,
      checkGcd, checkOps, checkGcdUsing, baseCheckCoprime, Cert.baseCheck,
      Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨MvPoly.zero_mul 1, MvPoly.zero_mul 1⟩,
      polyNormalize_zero⟩, ?_⟩
    apply Bool.or_eq_true_iff.mpr
    exact Or.inl ((polyIsUnit_iff (1 : MvPoly 0 R cmp)).mpr
      ⟨(1 : MvPoly 0 R cmp), MvPoly.mul_one 1⟩)
  · have htest : (f == 0 && h == 0) = false := by
      cases ht : (f == 0 && h == 0) with
      | false => rfl
      | true =>
          rcases Bool.and_eq_true_iff.mp ht with ⟨hf, hh⟩
          exact False.elim (hzero ⟨beq_iff_eq.mp hf, beq_iff_eq.mp hh⟩)
    let a := coeff Mono.zero f
    let b := coeff Mono.zero h
    let d := GcdOps.gcd a b
    let s := GcdOps.normUnit d
    let dn := normalize d
    let g : MvPoly 0 R cmp := C dn
    let uv := BezoutOps.xgcd a b
    have hfC : f = C a := arityZero_eq_C f
    have hhC : h = C b := arityZero_eq_C h
    have hd : d ≠ 0 := by
      intro hd0
      have ha0 : a = 0 := by
        rcases (LawfulGcdOps.dvd_iff d a).mp
            (LawfulGcdOps.gcd_dvd_left a b) with ⟨q, hq⟩
        rw [hd0, Lean.Grind.Semiring.zero_mul] at hq
        exact hq
      have hb0 : b = 0 := by
        rcases (LawfulGcdOps.dvd_iff d b).mp
            (LawfulGcdOps.gcd_dvd_right a b) with ⟨q, hq⟩
        rw [hd0, Lean.Grind.Semiring.zero_mul] at hq
        exact hq
      apply hzero
      constructor
      · rw [hfC, ha0, C_zero]
      · rw [hhC, hb0, C_zero]
    rcases LawfulGcdOps.normUnit_unit d with ⟨t, hst⟩
    have hs : s ≠ 0 := by
      intro hs0
      change GcdOps.normUnit d = 0 at hs0
      rw [hs0, Lean.Grind.Semiring.zero_mul] at hst
      exact LawfulGcdOps.one_ne_zero hst.symm
    have hdn : dn = d * s := rfl
    have hdn0 : dn ≠ 0 := by
      rw [hdn]
      intro hz
      rcases LawfulGcdOps.no_zero_div d s hz with hz | hz
      · exact hd hz
      · exact hs hz
    have hg0 : g ≠ 0 := by
      intro hg
      have hc := congrArg (coeff Mono.zero) hg
      rw [show g = C dn by rfl, coeff_C, if_pos rfl, coeff_zero] at hc
      exact hdn0 hc
    have hgf : g ∣ f := by
      rcases (LawfulGcdOps.dvd_iff d a).mp
          (LawfulGcdOps.gcd_dvd_left a b) with ⟨q, hq⟩
      refine ⟨C (t * q), ?_⟩
      rw [hfC]
      calc
        C a = C (d * q) := by rw [hq]
        _ = C (dn * (t * q)) := by
          congr 1
          rw [hdn]
          grind
        _ = C (t * q) * g := by
          rw [show g = C dn by rfl]
          calc
            C (dn * (t * q)) = C ((t * q) * dn) := by
              congr 1
              grind
            _ = C (t * q) * C dn := (C_mul_C_prs (t * q) dn).symm
    have hgh : g ∣ h := by
      rcases (LawfulGcdOps.dvd_iff d b).mp
          (LawfulGcdOps.gcd_dvd_right a b) with ⟨q, hq⟩
      refine ⟨C (t * q), ?_⟩
      rw [hhC]
      calc
        C b = C (d * q) := by rw [hq]
        _ = C (dn * (t * q)) := by
          congr 1
          rw [hdn]
          grind
        _ = C (t * q) * g := by
          rw [show g = C dn by rfl]
          calc
            C (dn * (t * q)) = C ((t * q) * dn) := by
              congr 1
              grind
            _ = C (t * q) * C dn := (C_mul_C_prs (t * q) dn).symm
    let cofL := quotient f g
    let cofR := quotient h g
    have hleft : cofL * g = f := quotient_mul_of_dvd hg0 hgf
    have hright : cofR * g = h := quotient_mul_of_dvd hg0 hgh
    have hca : a = dn * coeff Mono.zero cofL := by
      have hc := congrArg (coeff Mono.zero) hleft
      rw [hfC, coeff_C, if_pos rfl] at hc
      change coeff Mono.zero (cofL * C dn) = a at hc
      rw [MvPoly.mul_comm, coeff_C_mul] at hc
      exact hc.symm
    have hcb : b = dn * coeff Mono.zero cofR := by
      have hc := congrArg (coeff Mono.zero) hright
      rw [hhC, coeff_C, if_pos rfl] at hc
      change coeff Mono.zero (cofR * C dn) = b at hc
      rw [MvPoly.mul_comm, coeff_C_mul] at hc
      exact hc.symm
    have huv : uv.1 * a + uv.2 * b = dn := by
      simpa [uv, d, dn] using LawfulBezoutOps.xgcd_bezout a b
    have hcop : uv.1 * coeff Mono.zero cofL +
        uv.2 * coeff Mono.zero cofR = 1 := by
      have hz : dn * (uv.1 * coeff Mono.zero cofL +
          uv.2 * coeff Mono.zero cofR - 1) = 0 := by
        rw [hca, hcb] at huv
        grind
      rcases LawfulGcdOps.no_zero_div dn
          (uv.1 * coeff Mono.zero cofL +
            uv.2 * coeff Mono.zero cofR - 1) hz with hz | hz
      · exact False.elim (hdn0 hz)
      · grind
    have hgdef : g = polyNormalize (C d : MvPoly 0 R cmp) := by
      change C dn = C d * polyNormUnit (C d)
      rw [polyNormUnit, leadingTerm_C hd, C_mul_C_prs]
      rfl
    have hnorm : polyNormalize g = g := by
      rw [hgdef]
      exact polyNormalize_idem (C d : MvPoly 0 R cmp)
    have hleft' : g * cofL = f := by
      rw [MvPoly.mul_comm]
      exact hleft
    have hright' : g * cofR = h := by
      rw [MvPoly.mul_comm]
      exact hright
    have hbase : baseGcd cmp f h =
        (.mk g cofL cofR (.base uv.1 uv.2) : GcdCert 0 R cmp) := by
      unfold baseGcd
      rw [htest]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hgdef]
    rw [hbase]
    simp only [checkGcd, checkOps, checkGcdUsing, baseCheckCoprime,
      Cert.baseCheck, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨hleft', hright'⟩, hnorm⟩, hcop⟩

private theorem baseCoprime_checks {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    (cmp : Mono 0 → Mono 0 → Ordering) [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) (hcop : CoprimeCofactors f h) :
    checkCoprime f h (baseCoprime cmp f h) = true := by
  let a := coeff Mono.zero f
  let b := coeff Mono.zero h
  let d := GcdOps.gcd a b
  let uv := BezoutOps.xgcd a b
  have hfC : f = C a := arityZero_eq_C f
  have hhC : h = C b := arityZero_eq_C h
  have hdf : (C d : MvPoly 0 R cmp) ∣ f := by
    rcases (LawfulGcdOps.dvd_iff d a).mp
        (LawfulGcdOps.gcd_dvd_left a b) with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [hfC]
    calc
      C a = C (d * q) := by rw [hq]
      _ = C (q * d) := by congr 1; grind
      _ = C q * C d := (C_mul_C_prs q d).symm
  have hdh : (C d : MvPoly 0 R cmp) ∣ h := by
    rcases (LawfulGcdOps.dvd_iff d b).mp
        (LawfulGcdOps.gcd_dvd_right a b) with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [hhC]
    calc
      C b = C (d * q) := by rw [hq]
      _ = C (q * d) := by congr 1; grind
      _ = C q * C d := (C_mul_C_prs q d).symm
  rcases hcop (C d) hdf hdh with ⟨w, hw⟩
  have hdunit : GcdOps.isUnit d = true := by
    apply (LawfulGcdOps.isUnit_iff d).mpr
    refine ⟨coeff Mono.zero w, ?_⟩
    have hc := congrArg (coeff Mono.zero) hw
    rw [coeff_C_mul, coeff_one, ite_eq_left rfl] at hc
    exact hc
  have hdnorm : normalize d = 1 := LawfulGcdOps.normalize_unit d hdunit
  have hbez : uv.1 * a + uv.2 * b = 1 := by
    simpa only [uv, d, hdnorm] using LawfulBezoutOps.xgcd_bezout a b
  simp only [checkCoprime, checkOps, baseCheckCoprime, Cert.baseCheck,
    baseCoprime, beq_iff_eq]
  exact hbez

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

/-- Unnormalized successor-arity gcd candidate from coefficient content and
the primitive part of the terminal extended subresultant. -/
def succRaw {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (lower : PrsOpsAt R n)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp) : MvPoly (n + 1) R cmp :=
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
  constIn i Mono.lex common.gcd * primitiveGcd

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
    let raw := succRaw lower cmp f h
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

private theorem producedContent_dvd {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (hproduce : ∀ f h, checkGcd f h (produce f h) = true)
    (coeffs : List (MvPoly n R cmp)) :
    ∀ q ∈ coeffs, (contentCertWith produce coeffs).value ∣ q := by
  have aux : ∀ (xs : List (MvPoly n R cmp))
      (state : MvPoly n R cmp × List (GcdCert n R cmp)),
      let result := xs.foldl
        (fun state q =>
          let step := produce state.1 q
          (step.gcd, step :: state.2)) state
      result.1 ∣ state.1 ∧ ∀ q ∈ xs, result.1 ∣ q := by
    intro xs
    induction xs with
    | nil =>
        intro state
        exact ⟨⟨1, (MvPoly.one_mul state.1).symm⟩, by simp⟩
    | cons q qs ih =>
        intro state
        let step := produce state.1 q
        have hs := checkGcd_sound (hproduce state.1 q)
        have hstepAcc : step.gcd ∣ state.1 :=
          ⟨step.cofL, hs.1.trans (MvPoly.mul_comm _ _)⟩
        have hstepQ : step.gcd ∣ q :=
          ⟨step.cofR, hs.2.1.trans (MvPoly.mul_comm _ _)⟩
        have htail := ih (step.gcd, step :: state.2)
        simp only [List.foldl_cons]
        refine ⟨Hex.dvdTrans htail.1 hstepAcc, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Hex.dvdTrans htail.1 hstepQ
        · exact htail.2 x hx
  intro q hq
  unfold contentCertWith ContentCert.value ContentCert.ofSteps
  exact (aux coeffs (0, [])).2 q hq

private theorem producedContent_dvd_coeff {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (hproduce : ∀ f h, checkGcd f h (produce f h) = true)
    (p : DensePoly (MvPoly n R cmp)) (k : Nat) :
    (contentCertWith produce p.toArray.toList).value ∣ p.coeff k := by
  by_cases hk : k < p.toList.length
  · have hmem : p.toList[k] ∈ p.toList := List.getElem_mem hk
    have hd := producedContent_dvd produce hproduce p.toArray.toList
      p.toList[k] hmem
    have hcoeff : p.toList[k] = p.coeff k := by
      have hget := DensePoly.toList_getD_eq_coeff p k
      exact (List.getElem_eq_getD (h := hk) 0).trans hget
    exact hcoeff ▸ hd
  · have hsize : p.size ≤ k := by
      rw [DensePoly.length_toList] at hk
      omega
    rw [DensePoly.coeff_eq_zero_of_size_le p hsize]
    exact ⟨0, (MvPoly.zero_mul
      (contentCertWith produce p.toArray.toList).value).symm⟩

private theorem checkedContent_greatest_coeff {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (p : DensePoly (MvPoly n R cmp))
    (cert : ContentCert n R cmp)
    (hc : checkContent p.toArray.toList cert = true) :
    ∀ d, (∀ k, d ∣ p.coeff k) → d ∣ cert.value := by
  intro d hd
  apply (checkContent_sound hc).2 d
  intro q hq
  change q ∈ p.toList at hq
  rw [DensePoly.toList_eq_coeff_range] at hq
  rcases List.mem_map.mp hq with ⟨k, _, rfl⟩
  exact hd k

set_option maxHeartbeats 4000000 in
private theorem producedContent_const_dvd {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (produce : MvPoly n R Mono.lex → MvPoly n R Mono.lex →
      GcdCert n R Mono.lex)
    (hproduce : ∀ f h, checkGcd f h (produce f h) = true)
    (i : Fin (n + 1)) (p : MvPoly (n + 1) R cmp)
    (d : MvPoly n R Mono.lex)
    (hd : d ∣ (contentCertWith produce
      (toUnivariate i Mono.lex p).toArray.toList).value) :
    constIn (cmp := cmp) i Mono.lex d ∣ p := by
  apply constIn_dvd i d p
  intro k
  exact Hex.dvdTrans hd
    (producedContent_dvd_coeff produce hproduce
      (toUnivariate i Mono.lex p) k)

private theorem contentQuotient_primitive {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (produce : MvPoly n R Mono.lex → MvPoly n R Mono.lex →
      GcdCert n R Mono.lex)
    (hproduce : ∀ f h, checkGcd f h (produce f h) = true)
    (i : Fin (n + 1)) (p : MvPoly (n + 1) R cmp) (hp : p ≠ 0) :
    let view := toUnivariate i Mono.lex p
    let cert := contentCertWith produce view.toArray.toList
    let q := quotient p (constIn i Mono.lex cert.value)
    (∀ d, (∀ k, d ∣ (toUnivariate i Mono.lex q).coeff k) →
      ∃ u, d * u = 1) ∧
      q * constIn i Mono.lex cert.value = p := by
  let view := toUnivariate i Mono.lex p
  let cert := contentCertWith produce view.toArray.toList
  let d := cert.value
  let q := quotient p (constIn i Mono.lex d)
  have hcert : checkContent view.toArray.toList cert = true :=
    contentCertWith_checks produce hproduce view.toArray.toList
  have hdP : constIn (cmp := cmp) i Mono.lex d ∣ p :=
    producedContent_const_dvd produce hproduce i p d
      ⟨1, (MvPoly.one_mul d).symm⟩
  have hd0 : d ≠ 0 := by
    intro hd
    rcases hdP with ⟨w, hw⟩
    apply hp
    rw [hd, constIn_zero, MvPoly.mul_zero] at hw
    exact hw
  have hconst0 : constIn (cmp := cmp) i Mono.lex d ≠ 0 := by
    intro hz
    have hview := congrArg (toUnivariate i Mono.lex) hz
    rw [toUnivariate_constIn] at hview
    have hc := congrArg (fun r => r.coeff 0) hview
    rw [DensePoly.coeff_C, toUnivariate_zero,
      DensePoly.coeff_zero] at hc
    exact hd0 hc
  have hq : q * constIn (cmp := cmp) i Mono.lex d = p :=
    quotient_mul_of_dvd hconst0 hdP
  refine ⟨?_, hq⟩
  intro a ha
  have hviewQ : DensePoly.scale d (toUnivariate i Mono.lex q) = view := by
    calc
      DensePoly.scale d (toUnivariate i Mono.lex q) =
          DensePoly.C d * toUnivariate i Mono.lex q :=
        denseScale_eq_C_mul d (toUnivariate i Mono.lex q)
      _ = toUnivariate i Mono.lex q * DensePoly.C d :=
        DensePoly.mul_comm_poly _ _
      _ = toUnivariate i Mono.lex
          (q * constIn (cmp := cmp) i Mono.lex d) := by
        rw [toUnivariate_mul, toUnivariate_constIn]
      _ = view := by rw [hq]
  have hda : d * a ∣ d := by
    apply checkedContent_greatest_coeff view cert hcert
    intro k
    have hcoeff := congrArg (fun r => r.coeff k) hviewQ
    rw [DensePoly.coeff_scale_semiring] at hcoeff
    rcases (GcdDomainLaws.dvd_iff a
        ((toUnivariate i Mono.lex q).coeff k)).mp (ha k) with ⟨x, hx⟩
    apply (GcdDomainLaws.dvd_iff (d * a) (view.coeff k)).mpr
    refine ⟨x, ?_⟩
    rw [← hcoeff, hx]
    grind
  rcases (GcdDomainLaws.dvd_iff (d * a) d).mp hda with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hzero : d * (1 - a * u) = 0 := by
    calc
      d * (1 - a * u) = d - (d * a) * u := by grind
      _ = 0 := by rw [← hu]; grind
  rcases GcdDomainLaws.no_zero_div d (1 - a * u) hzero with hdz | hrest
  · exact False.elim (hd0 hdz)
  · grind

private theorem terminalQuotient_fractionGcd {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Dvd S] [Div S]
    [GcdDomainLaws S] [ExactDivLaws S] [Hex.Fraction.NonzeroOne S]
    (f g fp gp p : DensePoly S) (cf cg tc : S)
    (hfp0 : fp ≠ 0)
    (hfRec : fp * DensePoly.C cf = f)
    (hgRec : gp * DensePoly.C cg = g)
    (hcf0 : cf ≠ 0) (hcg0 : cg ≠ 0) (htc0 : tc ≠ 0)
    (hpRec : p * DensePoly.C tc = (terminal fp gp).2.2) :
    DensePoly.Fraction.map p ∣ DensePoly.Fraction.map f ∧
      DensePoly.Fraction.map p ∣ DensePoly.Fraction.map g ∧
      ∀ z, z ∣ DensePoly.Fraction.map f →
        z ∣ DensePoly.Fraction.map g → z ∣ DensePoly.Fraction.map p := by
  let t := (terminal fp gp).2.2
  have htDiv := terminal_dvd_fraction fp gp (Or.inl hfp0)
  have hpTDense : p ∣ t := by
    refine ⟨DensePoly.C tc, ?_⟩
    exact hpRec.symm
  have hpT : DensePoly.Fraction.map p ∣ DensePoly.Fraction.map t :=
    fractionMap_dvd_prs hpTDense
  have hfpDense : fp ∣ f := by
    refine ⟨DensePoly.C cf, ?_⟩
    exact hfRec.symm
  have hgpDense : gp ∣ g := by
    refine ⟨DensePoly.C cg, ?_⟩
    exact hgRec.symm
  have hpF : DensePoly.Fraction.map p ∣ DensePoly.Fraction.map f :=
    denseDvd_trans (denseDvd_trans hpT htDiv.1)
      (fractionMap_dvd_prs hfpDense)
  have hpG : DensePoly.Fraction.map p ∣ DensePoly.Fraction.map g :=
    denseDvd_trans (denseDvd_trans hpT htDiv.2)
      (fractionMap_dvd_prs hgpDense)
  refine ⟨hpF, hpG, ?_⟩
  intro z hzF hzG
  have hzFP : z ∣ DensePoly.Fraction.map fp :=
    fraction_dvd_cancel_const hcf0 hfRec hzF
  have hzGP : z ∣ DensePoly.Fraction.map gp :=
    fraction_dvd_cancel_const hcg0 hgRec hzG
  have hzT : z ∣ DensePoly.Fraction.map t := by
    rcases hzFP with ⟨a, ha⟩
    rcases hzGP with ⟨b, hb⟩
    let e := terminal fp gp
    let bez := e.1 * fp + e.2.1 * gp
    have hbez : bez = t := by
      simpa only [e, t, bez] using terminal_bezout fp gp (Or.inl hfp0)
    refine ⟨DensePoly.Fraction.map e.1 * a +
      DensePoly.Fraction.map e.2.1 * b, ?_⟩
    calc
      DensePoly.Fraction.map t = DensePoly.Fraction.map bez := by rw [hbez]
      _ = DensePoly.Fraction.map e.1 * DensePoly.Fraction.map fp +
          DensePoly.Fraction.map e.2.1 * DensePoly.Fraction.map gp := by
        simp only [bez, DensePoly.Fraction.map_add,
          DensePoly.Fraction.map_mul]
      _ = DensePoly.Fraction.map e.1 * (z * a) +
          DensePoly.Fraction.map e.2.1 * (z * b) := by rw [← ha, ← hb]
      _ = z * (DensePoly.Fraction.map e.1 * a +
          DensePoly.Fraction.map e.2.1 * b) := by grind
  exact fraction_dvd_cancel_const htc0 hpRec hzT

set_option maxHeartbeats 4000000 in
private theorem succRaw_gcd {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (lower : PrsOpsAt R n)
    (hlower : ∀ (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a b : MvPoly n R cmp'),
      checkGcd a b (lower.gcdCert cmp' a b) = true)
    (f h : MvPoly (n + 1) R cmp) (hf : f ≠ 0) (hh : h ≠ 0) :
    succRaw lower cmp f h ∣ f ∧ succRaw lower cmp f h ∣ h ∧
      ∀ d, d ∣ f → d ∣ h → d ∣ succRaw lower cmp f h := by
  let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let fView := toUnivariate i Mono.lex f
  let hView := toUnivariate i Mono.lex h
  let fContent := contentCertWith (lower.gcdCert Mono.lex)
    fView.toArray.toList
  let hContent := contentCertWith (lower.gcdCert Mono.lex)
    hView.toArray.toList
  let common := lower.gcdCert Mono.lex fContent.value hContent.value
  let fPrimitive := quotient f (constIn i Mono.lex fContent.value)
  let hPrimitive := quotient h (constIn i Mono.lex hContent.value)
  let fPrimitiveView := toUnivariate i Mono.lex fPrimitive
  let hPrimitiveView := toUnivariate i Mono.lex hPrimitive
  let e := terminal fPrimitiveView hPrimitiveView
  let t := e.2.2
  let terminalPoly := ofUnivariate (cmp := cmp) i Mono.lex t
  let terminalContent := contentCertWith (lower.gcdCert Mono.lex)
    t.toArray.toList
  let primitiveGcd := quotient terminalPoly
    (constIn i Mono.lex terminalContent.value)
  let p := toUnivariate i Mono.lex primitiveGcd
  let raw := succRaw lower cmp f h
  letI : Hex.Fraction.NonzeroOne (MvPoly n R Mono.lex) :=
    ⟨GcdDomainLaws.one_ne_zero⟩
  have hfView : fView ≠ 0 := by
    intro hz
    apply hf
    rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i f]
    change ofUnivariate (cmp := cmp) i Mono.lex fView = 0
    rw [hz]
    rfl
  have hhView : hView ≠ 0 := by
    intro hz
    apply hh
    rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i h]
    change ofUnivariate (cmp := cmp) i Mono.lex hView = 0
    rw [hz]
    rfl
  have hfData := contentQuotient_primitive
    (lower.gcdCert Mono.lex) (hlower Mono.lex) i f hf
  have hhData := contentQuotient_primitive
    (lower.gcdCert Mono.lex) (hlower Mono.lex) i h hh
  have hfRec : fPrimitive * constIn i Mono.lex fContent.value = f := by
    simpa only [fView, fContent, fPrimitive] using hfData.2
  have hhRec : hPrimitive * constIn i Mono.lex hContent.value = h := by
    simpa only [hView, hContent, hPrimitive] using hhData.2
  have hfPrimitive0 : fPrimitive ≠ 0 := by
    intro hz
    apply hf
    rw [← hfRec, hz, MvPoly.zero_mul]
  have hhPrimitive0 : hPrimitive ≠ 0 := by
    intro hz
    apply hh
    rw [← hhRec, hz, MvPoly.zero_mul]
  have hfPrimitiveView0 : fPrimitiveView ≠ 0 := by
    intro hz
    apply hfPrimitive0
    rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i fPrimitive]
    change ofUnivariate (cmp := cmp) i Mono.lex fPrimitiveView = 0
    rw [hz]
    rfl
  have hhPrimitiveView0 : hPrimitiveView ≠ 0 := by
    intro hz
    apply hhPrimitive0
    rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i hPrimitive]
    change ofUnivariate (cmp := cmp) i Mono.lex hPrimitiveView = 0
    rw [hz]
    rfl
  have ht0 : t ≠ 0 := by
    simpa only [e, t] using
      terminal_ne_zero fPrimitiveView hPrimitiveView
        (Or.inl hfPrimitiveView0)
  have hterminalPoly0 : terminalPoly ≠ 0 := by
    intro hz
    apply ht0
    have hv := congrArg (toUnivariate i Mono.lex) hz
    simpa only [terminalPoly, toUnivariate_ofUnivariate,
      toUnivariate_zero] using hv
  have hpData := contentQuotient_primitive
    (lower.gcdCert Mono.lex) (hlower Mono.lex) i terminalPoly hterminalPoly0
  have hpPrim : ∀ d, (∀ k, d ∣ p.coeff k) → ∃ u, d * u = 1 := by
    simpa only [terminalPoly, terminalContent, primitiveGcd, p,
      toUnivariate_ofUnivariate] using hpData.1
  have hpRecMv : primitiveGcd *
      constIn i Mono.lex terminalContent.value = terminalPoly := by
    simpa only [terminalPoly, terminalContent, primitiveGcd,
      toUnivariate_ofUnivariate] using hpData.2
  have hpRec : p * DensePoly.C terminalContent.value = t := by
    have hv := congrArg (toUnivariate i Mono.lex) hpRecMv
    simpa only [p, terminalPoly, toUnivariate_mul,
      toUnivariate_constIn, toUnivariate_ofUnivariate] using hv
  have htc0 : terminalContent.value ≠ 0 := by
    intro hz
    apply ht0
    have hCzero : DensePoly.C
        (0 : MvPoly n R Mono.lex) = 0 := rfl
    rw [← hpRec, hz, hCzero, DensePoly.mul_comm_poly,
      DensePoly.zero_mul]
  have hp0 : p ≠ 0 := by
    intro hz
    apply ht0
    rw [← hpRec, hz, DensePoly.zero_mul]
  have hfcCheck : checkContent fView.toArray.toList fContent = true :=
    contentCertWith_checks (lower.gcdCert Mono.lex) (hlower Mono.lex)
      fView.toArray.toList
  have hhcCheck : checkContent hView.toArray.toList hContent = true :=
    contentCertWith_checks (lower.gcdCert Mono.lex) (hlower Mono.lex)
      hView.toArray.toList
  have hcf : ∀ k, fContent.value ∣ fView.coeff k :=
    producedContent_dvd_coeff (lower.gcdCert Mono.lex) (hlower Mono.lex) fView
  have hcg : ∀ k, hContent.value ∣ hView.coeff k :=
    producedContent_dvd_coeff (lower.gcdCert Mono.lex) (hlower Mono.lex) hView
  have hcfGreat : ∀ d, (∀ k, d ∣ fView.coeff k) →
      d ∣ fContent.value :=
    checkedContent_greatest_coeff fView fContent hfcCheck
  have hcgGreat : ∀ d, (∀ k, d ∣ hView.coeff k) →
      d ∣ hContent.value :=
    checkedContent_greatest_coeff hView hContent hhcCheck
  have hcommon := checkGcd_greatest
    (hlower Mono.lex fContent.value hContent.value)
  have hcF : common.gcd ∣ fContent.value := by
    refine ⟨common.cofL, ?_⟩
    rw [hcommon.1.1, MvPoly.mul_comm]
  have hcG : common.gcd ∣ hContent.value := by
    refine ⟨common.cofR, ?_⟩
    rw [hcommon.1.2.1, MvPoly.mul_comm]
  have hcGreat : ∀ d, d ∣ fContent.value → d ∣ hContent.value →
      d ∣ common.gcd := hcommon.2
  have hfRecView : fPrimitiveView * DensePoly.C fContent.value = fView := by
    have hv := congrArg (toUnivariate i Mono.lex) hfRec
    simpa only [fPrimitiveView, fView, toUnivariate_mul,
      toUnivariate_constIn] using hv
  have hhRecView : hPrimitiveView * DensePoly.C hContent.value = hView := by
    have hv := congrArg (toUnivariate i Mono.lex) hhRec
    simpa only [hPrimitiveView, hView, toUnivariate_mul,
      toUnivariate_constIn] using hv
  have hfc0 : fContent.value ≠ 0 := by
    intro hz
    apply hfView
    have hCzero : DensePoly.C
        (0 : MvPoly n R Mono.lex) = 0 := rfl
    rw [← hfRecView, hz, hCzero, DensePoly.mul_comm_poly,
      DensePoly.zero_mul]
  have hhc0 : hContent.value ≠ 0 := by
    intro hz
    apply hhView
    have hCzero : DensePoly.C
        (0 : MvPoly n R Mono.lex) = 0 := rfl
    rw [← hhRecView, hz, hCzero, DensePoly.mul_comm_poly,
      DensePoly.zero_mul]
  have hpFraction := terminalQuotient_fractionGcd
    fView hView fPrimitiveView hPrimitiveView p
    fContent.value hContent.value terminalContent.value
    hfPrimitiveView0 hfRecView hhRecView hfc0 hhc0 htc0
    (by simpa only [e, t] using hpRec)
  have hpF := hpFraction.1
  have hpH := hpFraction.2.1
  have hpGreat := hpFraction.2.2
  have hdense := denseGcd_of_fraction hcf hcfGreat hcg hcgGreat
    hcF hcG hcGreat hfView hhView hpPrim hpF hpH hpGreat
  let candidate := DensePoly.scale common.gcd p
  have hrawView : toUnivariate i Mono.lex raw = candidate := by
    dsimp only [raw, candidate]
    unfold succRaw
    dsimp only
    rw [toUnivariate_mul, toUnivariate_constIn]
    change DensePoly.C common.gcd * p = DensePoly.scale common.gcd p
    exact (denseScale_eq_C_mul common.gcd p).symm
  have hcand : ofUnivariate (cmp := cmp) i Mono.lex candidate = raw := by
    calc
      ofUnivariate (cmp := cmp) i Mono.lex candidate =
          ofUnivariate (cmp := cmp) i Mono.lex
            (toUnivariate i Mono.lex raw) := by rw [hrawView]
      _ = raw := ofUnivariate_toUnivariate i raw
  have hrawF : raw ∣ f := by
    have hd := ofUnivariate_dvd_prs (cmp := cmp) i hdense.1
    rw [hcand, show ofUnivariate (cmp := cmp) i Mono.lex fView = f by
      exact ofUnivariate_toUnivariate i f] at hd
    exact hd
  have hrawH : raw ∣ h := by
    have hd := ofUnivariate_dvd_prs (cmp := cmp) i hdense.2.1
    rw [hcand, show ofUnivariate (cmp := cmp) i Mono.lex hView = h by
      exact ofUnivariate_toUnivariate i h] at hd
    exact hd
  refine ⟨hrawF, hrawH, ?_⟩
  intro d hdF hdH
  have hdViewF := toUnivariate_dvd_prs (cmp' := Mono.lex) i hdF
  have hdViewH := toUnivariate_dvd_prs (cmp' := Mono.lex) i hdH
  have hdCandidate := hdense.2.2 (toUnivariate i Mono.lex d)
    (by simpa only [fView] using hdViewF)
    (by simpa only [hView] using hdViewH)
  have hd := ofUnivariate_dvd_prs (cmp := cmp) i hdCandidate
  rw [hcand, ofUnivariate_toUnivariate] at hd
  exact hd

private theorem normalizedGcd_checks {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (coprime : MvPoly n R cmp → MvPoly n R cmp → CoprimeCert n R cmp)
    (hcoprime : ∀ a b, CoprimeCofactors a b →
      checkCoprime a b (coprime a b) = true)
    (f h raw : MvPoly n R cmp) (hraw0 : raw ≠ 0)
    (hrawF : raw ∣ f) (hrawH : raw ∣ h)
    (hgreat : ∀ d, d ∣ f → d ∣ h → d ∣ raw) :
    let g := polyNormalize raw
    let cofL := quotient f g
    let cofR := quotient h g
    checkGcd f h (.mk g cofL cofR (coprime cofL cofR)) = true := by
  let g := polyNormalize raw
  let cofL := quotient f g
  let cofR := quotient h g
  have hg0 : g ≠ 0 := by
    intro hg
    apply hraw0
    rcases polyNormalize_dvd_prs raw with ⟨q, hq⟩
    change polyNormalize raw = 0 at hg
    rw [hg, MvPoly.mul_zero] at hq
    exact hq
  have hgF : g ∣ f := Hex.dvdTrans (polyNormalize_dvd_prs raw) hrawF
  have hgH : g ∣ h := Hex.dvdTrans (polyNormalize_dvd_prs raw) hrawH
  have hleft : cofL * g = f := quotient_mul_of_dvd hg0 hgF
  have hright : cofR * g = h := quotient_mul_of_dvd hg0 hgH
  have hcop : CoprimeCofactors cofL cofR := by
    intro d hdL hdR
    have hgdF : g * d ∣ f := by
      rcases hdL with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      calc
        f = cofL * g := hleft.symm
        _ = (a * d) * g := by rw [ha]
        _ = a * (g * d) := by grind
    have hgdH : g * d ∣ h := by
      rcases hdR with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      calc
        h = cofR * g := hright.symm
        _ = (a * d) * g := by rw [ha]
        _ = a * (g * d) := by grind
    have hgdRaw : g * d ∣ raw := hgreat (g * d) hgdF hgdH
    have hgdG : g * d ∣ g :=
      Hex.dvdTrans hgdRaw (dvd_polyNormalize_prs raw)
    rcases hgdG with ⟨q, hq⟩
    have hzero : g * (1 - q * d) = 0 := by
      rw [hq]
      grind
    rcases GcdDomainLaws.no_zero_div g (1 - q * d) hzero with hg | hrest
    · exact False.elim (hg0 hg)
    · refine ⟨q, ?_⟩
      grind
  change checkGcd f h (.mk g cofL cofR (coprime cofL cofR)) = true
  rw [checkGcd_mk]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, polyNormalize_idem raw⟩,
    hcoprime cofL cofR hcop⟩
  · rw [MvPoly.mul_comm]
    exact hleft
  · rw [MvPoly.mul_comm]
    exact hright

private theorem quotient_normalize_unit {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hp : p ≠ 0) :
    polyIsUnit (quotient p (polyNormalize p)) = true := by
  let g := polyNormalize p
  let q := quotient p g
  have hg0 : g ≠ 0 := by
    intro hg
    rcases polyNormalize_dvd_prs p with ⟨a, ha⟩
    apply hp
    change polyNormalize p = 0 at hg
    rw [hg, MvPoly.mul_zero] at ha
    exact ha
  have hq : q * g = p :=
    quotient_mul_of_dvd hg0 (polyNormalize_dvd_prs p)
  rcases dvd_polyNormalize_prs p with ⟨v, hv⟩
  have hzero : g * (1 - v * q) = 0 := by
    change g = v * p at hv
    rw [← hq] at hv
    grind
  rcases GcdDomainLaws.no_zero_div g (1 - v * q) hzero with hg | hrest
  · exact False.elim (hg0 hg)
  · apply (polyIsUnit_iff q).mpr
    refine ⟨v, ?_⟩
    grind

private theorem unit_of_constIn_unit {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (i : Fin (n + 1)) (d : MvPoly n R Mono.lex)
    (w : MvPoly (n + 1) R cmp)
    (hw : constIn (cmp := cmp) i Mono.lex d * w = 1) :
    ∃ u, d * u = 1 := by
  have honeView : toUnivariate i Mono.lex (1 : MvPoly (n + 1) R cmp) = 1 := by
    rw [← constIn_one (R := R) (cmp := cmp) (cmp' := Mono.lex) i]
    exact toUnivariate_constIn (cmp := cmp) i 1
  have hview : DensePoly.C d * toUnivariate i Mono.lex w = 1 := by
    calc
      DensePoly.C d * toUnivariate i Mono.lex w =
          toUnivariate i Mono.lex (constIn (cmp := cmp) i Mono.lex d * w) := by
        rw [toUnivariate_mul, toUnivariate_constIn]
      _ = toUnivariate i Mono.lex 1 := by rw [hw]
      _ = 1 := honeView
  refine ⟨(toUnivariate i Mono.lex w).coeff 0, ?_⟩
  have hc := congrArg (fun p => p.coeff 0) hview
  rw [← denseScale_eq_C_mul, DensePoly.coeff_scale_semiring] at hc
  have honeCoeff :
      (1 : DensePoly (MvPoly n R Mono.lex)).coeff 0 = 1 := by
    rw [show (1 : DensePoly (MvPoly n R Mono.lex)) =
      DensePoly.C (1 : MvPoly n R Mono.lex) by rfl,
      DensePoly.coeff_C]
    rfl
  rw [honeCoeff] at hc
  exact hc

set_option maxHeartbeats 800000 in
private theorem contentValues_coprime {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (lower : PrsOpsAt R n)
    (hlower : ∀ (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a b : MvPoly n R cmp'),
      checkGcd a b (lower.gcdCert cmp' a b) = true)
    (f h : MvPoly (n + 1) R cmp) (hcop : CoprimeCofactors f h) :
    let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let fView := toUnivariate i Mono.lex f
    let hView := toUnivariate i Mono.lex h
    let left := contentCertWith (lower.gcdCert Mono.lex) fView.toArray.toList
    let right := contentCertWith (lower.gcdCert Mono.lex) hView.toArray.toList
    CoprimeCofactors left.value right.value := by
  let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let fView := toUnivariate i Mono.lex f
  let hView := toUnivariate i Mono.lex h
  let left := contentCertWith (lower.gcdCert Mono.lex) fView.toArray.toList
  let right := contentCertWith (lower.gcdCert Mono.lex) hView.toArray.toList
  change CoprimeCofactors left.value right.value
  intro d hdLeft hdRight
  have hdf : constIn (cmp := cmp) i Mono.lex d ∣ f :=
    producedContent_const_dvd (lower.gcdCert Mono.lex) (hlower Mono.lex)
      i f d hdLeft
  have hdh : constIn (cmp := cmp) i Mono.lex d ∣ h :=
    producedContent_const_dvd (lower.gcdCert Mono.lex) (hlower Mono.lex)
      i h d hdRight
  rcases hcop (constIn (cmp := cmp) i Mono.lex d) hdf hdh with ⟨w, hw⟩
  exact unit_of_constIn_unit i d w hw

private theorem succCoprime_checks {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (lower : PrsOpsAt R n)
    (hlowerGcd : ∀ (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a b : MvPoly n R cmp'),
      checkGcd a b (lower.gcdCert cmp' a b) = true)
    (hlowerCoprime : ∀ (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a b : MvPoly n R cmp'),
      CoprimeCofactors a b →
        checkCoprime a b (lower.coprimeCert cmp' a b) = true)
    (f h : MvPoly (n + 1) R cmp) (hcop : CoprimeCofactors f h) :
    checkCoprime f h (succCoprime lower cmp f h) = true := by
  cases hunit : polyIsUnit f || polyIsUnit h with
  | true =>
      have hcert : succCoprime lower cmp f h =
          (.unit : CoprimeCert (n + 1) R cmp) := by
        unfold succCoprime
        simp only [hunit, ↓reduceIte]
      rw [hcert]
      rw [checkCoprime_unit]
      exact hunit
  | false =>
      rcases Bool.or_eq_false_iff.mp hunit with ⟨hfUnit, hhUnit⟩
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
      have hconstant := terminal_constant_of_coprime f h hcop hfUnit hhUnit
      have htC : e.2.2 = DensePoly.C r := by
        simpa only [i, fView, hView, e, r] using hconstant.1
      have hr : r ≠ 0 := by
        simpa only [i, fView, hView, e, r] using hconstant.2
      rcases coprime_nonzero_of_nonunits hcop hfUnit hhUnit with ⟨hf, _⟩
      have hfView : fView ≠ 0 := by
        intro hz
        apply hf
        rw [← ofUnivariate_toUnivariate (cmp' := Mono.lex) i f]
        change ofUnivariate (cmp := cmp) i Mono.lex fView = 0
        rw [hz]
        rfl
      have hdense := terminal_bezout fView hView (Or.inl hfView)
      have hbez : u * f + v * h = constIn (cmp := cmp) i Mono.lex r := by
        have hinj : Function.Injective
            (toUnivariate (R := R) (cmp := cmp) i Mono.lex) := by
          intro a b hab
          calc
            a = ofUnivariate (cmp := cmp) i Mono.lex
                (toUnivariate i Mono.lex a) :=
              (ofUnivariate_toUnivariate i a).symm
            _ = ofUnivariate (cmp := cmp) i Mono.lex
                (toUnivariate i Mono.lex b) := by rw [hab]
            _ = b := ofUnivariate_toUnivariate i b
        apply hinj
        simp only [toUnivariate_add, toUnivariate_mul,
          toUnivariate_ofUnivariate, toUnivariate_constIn, u, v]
        rw [hdense, htC]
      have hleft : checkContent fView.toArray.toList left = true :=
        contentCertWith_checks (lower.gcdCert Mono.lex)
          (hlowerGcd Mono.lex) fView.toArray.toList
      have hright : checkContent hView.toArray.toList right = true :=
        contentCertWith_checks (lower.gcdCert Mono.lex)
          (hlowerGcd Mono.lex) hView.toArray.toList
      have hrestCop : CoprimeCofactors left.value right.value := by
        simpa only [i, fView, hView, left, right] using
          contentValues_coprime lower hlowerGcd f h hcop
      have hrest : checkCoprime left.value right.value rest = true :=
        hlowerCoprime Mono.lex left.value right.value hrestCop
      have hcert : succCoprime lower cmp f h =
          (.splitBezout i Mono.lex u v r left right rest :
            CoprimeCert (n + 1) R cmp) := by
        unfold succCoprime
        simp only [hunit, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [hcert]
      rw [checkCoprime_splitBezout]
      simp only [decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨hr, hbez⟩, hleft⟩, hright⟩, hrest⟩

set_option maxHeartbeats 1000000 in
private theorem succGcd_checks {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [LawfulGcdOps R] [IsMonomialOrder cmp]
    (lower : PrsOpsAt R n)
    (hlowerGcd : ∀ (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a b : MvPoly n R cmp'),
      checkGcd a b (lower.gcdCert cmp' a b) = true)
    (hlowerCoprime : ∀ (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a b : MvPoly n R cmp'),
      CoprimeCofactors a b →
        checkCoprime a b (lower.coprimeCert cmp' a b) = true)
    (f h : MvPoly (n + 1) R cmp) :
    checkGcd f h (succGcd lower cmp f h) = true := by
  by_cases hf : f = 0
  · subst f
    by_cases hh : h = 0
    · subst h
      simp only [succGcd, beq_self_eq_true, Bool.true_and, ↓reduceIte]
      rw [checkGcd_mk, checkCoprime_unit]
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨MvPoly.zero_mul 1, MvPoly.zero_mul 1⟩,
        polyNormalize_zero⟩, ?_⟩
      apply Bool.or_eq_true_iff.mpr
      exact Or.inl ((polyIsUnit_iff (1 : MvPoly (n + 1) R cmp)).mpr
        ⟨1, MvPoly.mul_one 1⟩)
    · have hhTest : (h == (0 : MvPoly (n + 1) R cmp)) = false := by
        cases ht : (h == (0 : MvPoly (n + 1) R cmp)) with
        | false => rfl
        | true => exact False.elim (hh (beq_iff_eq.mp ht))
      simp only [succGcd, beq_self_eq_true, Bool.true_and, hhTest,
        Bool.false_eq_true, ↓reduceIte]
      let g := polyNormalize h
      let cofR := quotient h g
      have hg0 : g ≠ 0 := by
        intro hg
        rcases polyNormalize_dvd_prs h with ⟨a, ha⟩
        apply hh
        change polyNormalize h = 0 at hg
        rw [hg, MvPoly.mul_zero] at ha
        exact ha
      have hright : cofR * g = h :=
        quotient_mul_of_dvd hg0 (polyNormalize_dvd_prs h)
      rw [checkGcd_mk, checkCoprime_unit]
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨MvPoly.mul_zero g, ?_⟩, polyNormalize_idem h⟩, ?_⟩
      · rw [MvPoly.mul_comm]
        exact hright
      · apply Bool.or_eq_true_iff.mpr
        exact Or.inr (quotient_normalize_unit h hh)
  · by_cases hh : h = 0
    · subst h
      have hfTest : (f == (0 : MvPoly (n + 1) R cmp)) = false := by
        cases ht : (f == (0 : MvPoly (n + 1) R cmp)) with
        | false => rfl
        | true => exact False.elim (hf (beq_iff_eq.mp ht))
      simp only [succGcd, hfTest, Bool.false_and, Bool.false_eq_true,
        beq_self_eq_true, ↓reduceIte]
      let g := polyNormalize f
      let cofL := quotient f g
      have hg0 : g ≠ 0 := by
        intro hg
        rcases polyNormalize_dvd_prs f with ⟨a, ha⟩
        apply hf
        change polyNormalize f = 0 at hg
        rw [hg, MvPoly.mul_zero] at ha
        exact ha
      have hleft : cofL * g = f :=
        quotient_mul_of_dvd hg0 (polyNormalize_dvd_prs f)
      rw [checkGcd_mk, checkCoprime_unit]
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨?_, MvPoly.mul_zero g⟩, polyNormalize_idem f⟩, ?_⟩
      · rw [MvPoly.mul_comm]
        exact hleft
      · apply Bool.or_eq_true_iff.mpr
        exact Or.inl (quotient_normalize_unit f hf)
    · have hfTest : (f == (0 : MvPoly (n + 1) R cmp)) = false := by
        cases ht : (f == (0 : MvPoly (n + 1) R cmp)) with
        | false => rfl
        | true => exact False.elim (hf (beq_iff_eq.mp ht))
      have hhTest : (h == (0 : MvPoly (n + 1) R cmp)) = false := by
        cases ht : (h == (0 : MvPoly (n + 1) R cmp)) with
        | false => rfl
        | true => exact False.elim (hh (beq_iff_eq.mp ht))
      simp only [succGcd, hfTest, Bool.false_and, Bool.false_eq_true, hhTest,
        ↓reduceIte]
      let raw := succRaw lower cmp f h
      change checkGcd f h (.mk (polyNormalize raw)
        (quotient f (polyNormalize raw)) (quotient h (polyNormalize raw))
        (succCoprime lower cmp (quotient f (polyNormalize raw))
          (quotient h (polyNormalize raw)))) = true
      have hraw := succRaw_gcd lower hlowerGcd f h hf hh
      have hraw0 : raw ≠ 0 := by
        intro hz
        rcases hraw.1 with ⟨a, ha⟩
        apply hf
        change succRaw lower cmp f h = 0 at hz
        rw [hz, MvPoly.mul_zero] at ha
        exact ha
      exact normalizedGcd_checks (succCoprime lower cmp)
        (succCoprime_checks lower hlowerGcd hlowerCoprime)
        f h raw hraw0 hraw.1 hraw.2.1 hraw.2.2

private theorem prsOps_checks {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R] :
    ∀ n,
      (∀ (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
        (f h : MvPoly n R cmp),
        checkGcd f h ((prsOps (R := R) n).gcdCert cmp f h) = true) ∧
      (∀ (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
        (f h : MvPoly n R cmp), CoprimeCofactors f h →
        checkCoprime f h ((prsOps (R := R) n).coprimeCert cmp f h) = true) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro cmp _ f h
        simpa only [prsOps] using baseGcd_checks cmp f h
      · intro cmp _ f h hcop
        simpa only [prsOps] using baseCoprime_checks cmp f h hcop
  | succ n ih =>
      rcases ih with ⟨ihGcd, ihCoprime⟩
      constructor
      · intro cmp _ f h
        simpa only [prsOps] using
          succGcd_checks (prsOps (R := R) n) ihGcd ihCoprime f h
      · intro cmp _ f h hcop
        simpa only [prsOps] using
          succCoprime_checks (prsOps (R := R) n) ihGcd ihCoprime f h hcop

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
  exact (prsOps_checks (R := R) n).1 cmp f h

end Hex.MvPoly
