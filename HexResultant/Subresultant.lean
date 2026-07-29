/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultant.BrownTraub
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

omit [Zero R] [DecidableEq R] in
/-- The executable Brown sign is the local determinant's alternating sign. -/
theorem negOnePow_eq_sign {S : Type u} [Zero S] [One S] [Sub S] (n : Nat) :
    negOnePow (R := S) n = SubresultantMinor.sign (R := S) n := by
  rfl

omit [Zero R] [DecidableEq R] in
/-- Brown signs are nonzero in every nontrivial commutative ring. -/
theorem negOnePow_ne_zero {S : Type u} [Lean.Grind.CommRing S]
    (h1 : (1 : S) ≠ 0) (n : Nat) : negOnePow (R := S) n ≠ 0 := by
  rw [negOnePow_eq_sign]
  exact SubresultantMinor.sign_ne_zero h1 n

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

/-- Integral subresultant-family invariant for one recursive Brown state. It
keeps all accumulated factors cross-multiplied in the coefficient ring. -/
private def BrownInv [Lean.Grind.CommRing R] [DecidableEq R]
    (f g prev curr : DensePoly R) (hPrev : R) : Prop :=
  prev ≠ 0 ∧ curr ≠ 0 ∧ curr.size < prev.size ∧ hPrev ≠ 0 ∧
    ∀ J, J < curr.size →
      Subresultant.poly J prev curr =
        scale
          (prev.leadingCoeff ^ (curr.size - 1 - J) *
            hPrev ^ (prev.size - 2 - J))
          (Subresultant.poly J f g)

/-- The block-swap sign cancels the repeated signed-pseudo-remainder factor
at every index below the divisor degree. -/
private theorem sign_prem_cancel {S : Type u} [Lean.Grind.CommRing S]
    (m n J : Nat) (hnm : n ≤ m) (hJ : J < n) :
    SubresultantMinor.sign (R := S) ((m - 1 - J) * (n - 1 - J)) *
        SubresultantMinor.sign (R := S) (m - n + 1) ^ (n - 1 - J) = 1 := by
  let t := n - 1 - J
  let delta := m - n
  have hmJ : m - 1 - J = t + delta := by
    dsimp only [t, delta]
    omega
  rw [hmJ]
  rw [← SubresultantMinor.sign_mul (R := S) (delta + 1) t,
    ← SubresultantMinor.sign_add]
  have hexp :
      (t + delta) * t + (delta + 1) * t =
        (t + delta + (delta + 1)) * t := by
    simp only [Nat.add_mul]
  rw [hexp]
  have hmod : ((t + delta + (delta + 1)) * t) % 2 = 0 := by
    by_cases ht : t % 2 = 0
    · rw [Nat.mul_mod, ht]
      omega
    · have ht1 : t % 2 = 1 := by
        have := Nat.mod_lt t (by decide : 0 < 2)
        omega
      have hu : (t + delta + (delta + 1)) % 2 = 0 := by
        omega
      rw [Nat.mul_mod, hu]
      omega
  unfold SubresultantMinor.sign
  rw [if_pos hmod]

/-- The invariant identifies the next Brown scale with the leading principal
coefficient of the original-pair subresultant and proves its exact quotient
law inside the base ring. -/
private theorem BrownInv.nextScale {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g prev curr : DensePoly S) (hPrev : S)
    (hinv : BrownInv f g prev curr hPrev) :
    let delta := prev.size - curr.size
    let hCurr := divExp curr.leadingCoeff hPrev delta
    hCurr = (Subresultant.poly (curr.size - 1) f g).coeff (curr.size - 1) ∧
      hCurr ≠ 0 ∧
      powNat curr.leadingCoeff delta =
        powNat hPrev (delta - 1) * hCurr := by
  rcases hinv with ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
  let delta := prev.size - curr.size
  let J := curr.size - 1
  let root := Subresultant.poly J f g
  let w := root.coeff J
  have hprevPos : 0 < prev.size := Nat.pos_of_ne_zero fun hzero =>
    hprev ((size_eq_zero_iff prev).mp hzero)
  have hcurrPos : 0 < curr.size := Nat.pos_of_ne_zero fun hzero =>
    hcurr ((size_eq_zero_iff curr).mp hzero)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    omega
  have hJ : J < curr.size := by
    dsimp only [J]
    omega
  have hInvJ : Subresultant.poly J prev curr =
      scale (hPrev ^ (delta - 1)) root := by
    have h := hfamily J hJ
    have hexp₁ : curr.size - 1 - J = 0 := by
      dsimp only [J]
      omega
    have hexp₂ : prev.size - 2 - J = delta - 1 := by
      dsimp only [J, delta]
      omega
    rw [hexp₁, hexp₂, Lean.Grind.Semiring.pow_zero,
      Lean.Grind.Semiring.one_mul] at h
    exact h
  have hEdge : Subresultant.poly J prev curr =
      scale (curr.leadingCoeff ^ (delta - 1)) curr := by
    have h := Subresultant.poly_rightDegree (prev.size - 1)
      (curr.size - 1) prev curr (by omega) (by omega) (by omega)
    have hexp : (prev.size - 1) - (curr.size - 1) - 1 = delta - 1 := by
      dsimp only [delta]
      omega
    simpa only [J, hexp] using h
  have hcoeff := congrArg (fun p : DensePoly S => p.coeff J)
    (hEdge.symm.trans hInvJ)
  rw [coeff_scale_semiring, coeff_scale_semiring] at hcoeff
  have hcurrCoeff : curr.coeff J = curr.leadingCoeff := by
    exact (leadingCoeff_eq_coeff_last curr hcurrPos).symm
  have hnum : curr.leadingCoeff ^ delta = hPrev ^ (delta - 1) * w := by
    rw [hcurrCoeff] at hcoeff
    change curr.leadingCoeff ^ (delta - 1) * curr.leadingCoeff =
      hPrev ^ (delta - 1) * w at hcoeff
    rw [← Lean.Grind.Semiring.pow_succ] at hcoeff
    simpa only [show delta - 1 + 1 = delta by omega] using hcoeff
  have hcurrLc : curr.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size curr hcurrPos
  have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hcurrLc
  have hden : hPrev ^ (delta - 1) ≠ 0 :=
    pow_ne_zero h1 hhPrev (delta - 1)
  have hnumNe : curr.leadingCoeff ^ delta ≠ 0 :=
    pow_ne_zero h1 hcurrLc delta
  have hw : w ≠ 0 := by
    intro hwzero
    apply hnumNe
    rw [hnum, hwzero, Lean.Grind.Semiring.mul_zero]
  have hdiv : divExp curr.leadingCoeff hPrev delta = w := by
    unfold divExp
    rw [powNat_eq_pow, powNat_eq_pow, hnum]
    rw [show hPrev ^ (delta - 1) * w = w * hPrev ^ (delta - 1) by grind]
    exact exactDiv_mul_right w hden
  dsimp only
  refine ⟨?_, hdiv ▸ hw, ?_⟩
  · simpa only [J, root, w] using hdiv
  · rw [hdiv, powNat_eq_pow, powNat_eq_pow]
    exact hnum

/-- The signed first pseudo-remainder establishes the integral invariant for
the first recursive Brown state. -/
private theorem brownInv_init {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hg : g ≠ 0) (hgf : g.size ≤ f.size)
    (hp : (pseudoDivMod f g).2 ≠ 0) :
    let delta := f.size - g.size
    let h₂ := powNat g.leadingCoeff delta
    let g₃ := scale (negOnePow (R := S) (delta + 1)) (pseudoDivMod f g).2
    BrownInv f g g g₃ h₂ := by
  let delta := f.size - g.size
  let p := (pseudoDivMod f g).2
  let s := negOnePow (R := S) (delta + 1)
  let h₂ := powNat g.leadingCoeff delta
  let g₃ := scale s p
  have hgpos : 0 < g.size := Nat.pos_of_ne_zero fun hzero =>
    hg ((size_eq_zero_iff g).mp hzero)
  have hglc : g.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size g hgpos
  have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hglc
  have hs : s ≠ 0 := negOnePow_ne_zero h1 (delta + 1)
  have hg₃ : g₃ ≠ 0 := scale_ne_zero hs hp
  have hg₃size : g₃.size = p.size := size_scale hs p
  have hg₃lt : g₃.size < g.size := by
    rw [hg₃size]
    simpa only [p] using pseudoDivMod_remainder_lt f g hg
  have hh₂ : h₂ ≠ 0 := powNat_ne_zero h1 hglc delta
  have hsquare : s * s = 1 := by
    simpa only [s, negOnePow_eq_sign] using
      (SubresultantMinor.sign_mul_self (R := S) (delta + 1))
  have hpback : p = scale s g₃ := by
    apply ext_coeff
    intro i
    simp only [g₃, coeff_scale_semiring]
    change p.coeff i = s * (s * p.coeff i)
    grind
  refine ⟨hg, hg₃, hg₃lt, hh₂, ?_⟩
  intro J hJ
  have hdes := Subresultant.poly_descent f g g₃ hs hg hg₃ hgf
    (by simpa only [p] using hpback) J hJ
  have hJg : J < g.size := Nat.lt_trans hJ hg₃lt
  have hsign := sign_prem_cancel (S := S) f.size g.size J hgf hJg
  have hscalar :
      SubresultantMinor.sign (R := S)
          ((f.size - 1 - J) * (g.size - 1 - J)) *
        g.leadingCoeff ^ (f.size - g₃.size) *
        s ^ (g.size - 1 - J) =
      g.leadingCoeff ^ (f.size - g₃.size) := by
    rw [show s = SubresultantMinor.sign (R := S) (f.size - g.size + 1) by
      simp only [s, delta, negOnePow_eq_sign]]
    grind
  rw [hscalar] at hdes
  let common := f.size - g₃.size
  let targetExp := (g₃.size - 1 - J) + delta * (g.size - 2 - J)
  let leftExp := (delta + 1) * (g.size - 1 - J)
  have hexp : leftExp = common + targetExp := by
    have hJle₃ : J + 1 ≤ g₃.size := Nat.succ_le_of_lt hJ
    have hJstrong : J + 1 < g.size :=
      Nat.lt_of_le_of_lt hJle₃ hg₃lt
    have hJleg : J + 1 ≤ g.size := Nat.le_of_lt hJstrong
    have hg₃f : g₃.size ≤ f.size :=
      Nat.le_trans (Nat.le_of_lt hg₃lt) hgf
    have hn : g.size - 1 - J = (g.size - 2 - J) + 1 := by omega
    have hleft :
        (f.size - g₃.size) + (g₃.size - 1 - J) =
          f.size - (J + 1) := by
      rw [show g₃.size - 1 - J = g₃.size - (J + 1) by omega]
      exact Nat.sub_add_sub_cancel hg₃f hJle₃
    have hright :
        (f.size - g.size) + (g.size - 1 - J) =
          f.size - (J + 1) := by
      rw [show g.size - 1 - J = g.size - (J + 1) by omega]
      exact Nat.sub_add_sub_cancel hgf hJleg
    have hlin :
        (f.size - g₃.size) + (g₃.size - 1 - J) =
          (f.size - g.size) + (g.size - 1 - J) := by
      exact hleft.trans hright.symm
    dsimp only [leftExp, common, targetExp, delta]
    calc
      (f.size - g.size + 1) * (g.size - 1 - J) =
          (f.size - g.size) * (g.size - 1 - J) +
            (g.size - 1 - J) := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = (f.size - g.size) * ((g.size - 2 - J) + 1) +
            (g.size - 1 - J) := by rw [hn]
      _ = (f.size - g.size) * (g.size - 2 - J) +
            (f.size - g.size) + (g.size - 1 - J) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = ((f.size - g₃.size) + (g₃.size - 1 - J)) +
            (f.size - g.size) * (g.size - 2 - J) := by
        rw [hlin]
        omega
      _ = (f.size - g₃.size) +
            ((g₃.size - 1 - J) +
              (f.size - g.size) * (g.size - 2 - J)) := by omega
  have htarget :
      g.leadingCoeff ^ (g₃.size - 1 - J) * h₂ ^ (g.size - 2 - J) =
        g.leadingCoeff ^ targetExp := by
    rw [show h₂ = g.leadingCoeff ^ delta by
      simp only [h₂, powNat_eq_pow], ← pow_mul,
      ← Lean.Grind.Semiring.pow_add]
  apply scale_cancel (pow_ne_zero h1 hglc common)
  rw [scale_scale]
  rw [htarget]
  rw [← Lean.Grind.Semiring.pow_add, ← hexp]
  simpa only [common, leftExp, delta, s, g₃, p] using hdes.symm

/-- At a nonterminal invariant state, the pseudo-remainder has the exact Brown
factor and its quotient is the adjacent original-pair subresultant. -/
private theorem BrownInv.factor {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g prev curr : DensePoly S) (hPrev : S)
    (hinv : BrownInv f g prev curr hPrev)
    (hp : (pseudoDivMod prev curr).2 ≠ 0) :
    let delta := prev.size - curr.size
    let p := (pseudoDivMod prev curr).2
    let divisor :=
      negOnePow (R := S) (delta + 1) * prev.leadingCoeff * powNat hPrev delta
    let next := divScalar p divisor
    divisor ≠ 0 ∧ p = scale divisor next ∧ next ≠ 0 ∧
      next = Subresultant.poly (curr.size - 2) f g := by
  rcases hinv with ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
  let delta := prev.size - curr.size
  let p := (pseudoDivMod prev curr).2
  let s := negOnePow (R := S) (delta + 1)
  let divisor := s * prev.leadingCoeff * powNat hPrev delta
  let next := divScalar p divisor
  let J := curr.size - 2
  let root := Subresultant.poly J f g
  have hprevPos : 0 < prev.size := Nat.pos_of_ne_zero fun hzero =>
    hprev ((size_eq_zero_iff prev).mp hzero)
  have hcurrPos : 0 < curr.size := Nat.pos_of_ne_zero fun hzero =>
    hcurr ((size_eq_zero_iff curr).mp hzero)
  have hprevLc : prev.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size prev hprevPos
  have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hprevLc
  have hs : s ≠ 0 := negOnePow_ne_zero h1 (delta + 1)
  have hpow : powNat hPrev delta ≠ 0 :=
    powNat_ne_zero h1 hhPrev delta
  have hdivisor : divisor ≠ 0 :=
    ExactDivLaws.mul_ne_zero
      (ExactDivLaws.mul_ne_zero hs hprevLc) hpow
  have hcurrBig : 2 ≤ curr.size := by
    by_cases hbig : 2 ≤ curr.size
    · exact hbig
    · have hpsize : p.size < curr.size := by
        simpa only [p] using pseudoDivMod_remainder_lt prev curr hcurr
      have hpzero : p = 0 := (size_eq_zero_iff p).mp (by omega)
      exact (hp hpzero).elim
  have hJ : J < curr.size := by
    dsimp only [J]
    omega
  have hInvJ : Subresultant.poly J prev curr =
      scale (prev.leadingCoeff * hPrev ^ delta) root := by
    have h := hfamily J hJ
    have hexp₁ : curr.size - 1 - J = 1 := by
      dsimp only [J]
      omega
    have hexp₂ : prev.size - 2 - J = delta := by
      dsimp only [J, delta]
      omega
    rw [hexp₁, hexp₂, Lean.Grind.Semiring.pow_one] at h
    exact h
  have hPrem : Subresultant.poly J prev curr = scale s p := by
    have h := Subresultant.poly_prem prev curr hcurrBig (Nat.le_of_lt hlt)
    simpa only [J, s, delta, p, negOnePow_eq_sign] using h
  have hsquare : s * s = 1 := by
    simpa only [s, negOnePow_eq_sign] using
      (SubresultantMinor.sign_mul_self (R := S) (delta + 1))
  have hfactor : p = scale divisor root := by
    apply scale_cancel hs
    rw [scale_scale]
    have heq : scale s p = scale (prev.leadingCoeff * hPrev ^ delta) root :=
      hPrem.symm.trans hInvJ
    have hscalar :
        s * divisor = prev.leadingCoeff * hPrev ^ delta := by
      dsimp only [divisor]
      rw [powNat_eq_pow]
      grind
    rw [hscalar]
    exact heq
  have hnext : next = root := by
    dsimp only [next]
    rw [hfactor]
    exact divScalar_scale root hdivisor
  have hroot : root ≠ 0 := by
    intro hzero
    apply hp
    change p = 0
    rw [hfactor, hzero]
    apply ext_coeff
    intro i
    rw [coeff_scale_semiring, coeff_zero]
    grind
  have hscaled : p = scale divisor next := by
    rw [hnext]
    exact hfactor
  have hnextNonzero : next ≠ 0 := by
    rw [hnext]
    exact hroot
  exact ⟨hdivisor, hscaled, hnextNonzero, hnext⟩

/-- One nonterminal Brown step preserves the integral original-pair
subresultant invariant. -/
private theorem BrownInv.step {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g prev curr : DensePoly S) (hPrev : S)
    (hinv : BrownInv f g prev curr hPrev)
    (hp : (pseudoDivMod prev curr).2 ≠ 0) :
    let delta := prev.size - curr.size
    let hCurr := divExp curr.leadingCoeff hPrev delta
    let p := (pseudoDivMod prev curr).2
    let divisor :=
      negOnePow (R := S) (delta + 1) * prev.leadingCoeff * powNat hPrev delta
    let next := divScalar p divisor
    BrownInv f g curr next hCurr := by
  rcases hinv with ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
  let delta := prev.size - curr.size
  let hCurr := divExp curr.leadingCoeff hPrev delta
  let p := (pseudoDivMod prev curr).2
  let s := negOnePow (R := S) (delta + 1)
  let divisor := s * prev.leadingCoeff * powNat hPrev delta
  let next := divScalar p divisor
  have hinv : BrownInv f g prev curr hPrev :=
    ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
  have hscale := BrownInv.nextScale f g prev curr hPrev hinv
  rcases hscale with ⟨_, hhCurrRaw, hscaleExactRaw⟩
  have hhCurr : hCurr ≠ 0 := by
    simpa only [hCurr, delta] using hhCurrRaw
  have hscaleExact :
      powNat curr.leadingCoeff delta =
        powNat hPrev (delta - 1) * hCurr := by
    simpa only [hCurr, delta] using hscaleExactRaw
  have hfactor := BrownInv.factor f g prev curr hPrev hinv hp
  rcases hfactor with
    ⟨hdivisorRaw, hscaledRaw, hnextRaw, hnextEqRaw⟩
  have hdivisor : divisor ≠ 0 := by
    simpa only [divisor, s, delta] using hdivisorRaw
  have hscaled : p = scale divisor next := by
    simpa only [p, divisor, next, s, delta] using hscaledRaw
  have hnext : next ≠ 0 := by
    simpa only [p, divisor, next, s, delta] using hnextRaw
  have hnextEq :
      next = Subresultant.poly (curr.size - 2) f g := by
    simpa only [p, divisor, next, s, delta] using hnextEqRaw
  have hprevPos : 0 < prev.size := Nat.pos_of_ne_zero fun hzero =>
    hprev ((size_eq_zero_iff prev).mp hzero)
  have hcurrPos : 0 < curr.size := Nat.pos_of_ne_zero fun hzero =>
    hcurr ((size_eq_zero_iff curr).mp hzero)
  have hprevLc : prev.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size prev hprevPos
  have hcurrLc : curr.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size curr hcurrPos
  have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hcurrLc
  have hcurrBig : 2 ≤ curr.size := by
    by_cases hbig : 2 ≤ curr.size
    · exact hbig
    · have hpsize : p.size < curr.size := by
        simpa only [p] using pseudoDivMod_remainder_lt prev curr hcurr
      have hpzero : p = 0 := (size_eq_zero_iff p).mp (by omega)
      exact (hp hpzero).elim
  have hnextSize : next.size ≤ curr.size - 1 := by
    rw [hnextEq]
    exact Nat.le_trans
      (Subresultant.poly_size_le (curr.size - 2) f g) (by omega)
  have hnextLt : next.size < curr.size := by omega
  refine ⟨hcurr, hnext, hnextLt, hhCurr, ?_⟩
  intro J hJ
  have hJnext : J < next.size := by
    simpa only [next, p, divisor, s, delta] using hJ
  have hJcurr : J < curr.size := Nat.lt_trans hJnext hnextLt
  have hdes := Subresultant.poly_descent prev curr next hdivisor
    hcurr hnext (Nat.le_of_lt hlt) hscaled J hJnext
  have hfamilyJ := hfamily J hJcurr
  let t := curr.size - 1 - J
  let b := curr.size - 2 - J
  let a := next.size - 1 - J
  let common :=
    curr.leadingCoeff ^ (prev.size - next.size) *
      prev.leadingCoeff ^ t * hPrev ^ (delta * t)
  let target := curr.leadingCoeff ^ a * hCurr ^ b
  have ht : t = b + 1 := by
    dsimp only [t, b]
    omega
  have hdelta : 0 < delta := by
    dsimp only [delta]
    omega
  have hrecPow :
      curr.leadingCoeff ^ delta = hPrev ^ (delta - 1) * hCurr := by
    simpa only [powNat_eq_pow] using hscaleExact
  have hrecPowB :
      curr.leadingCoeff ^ (delta * b) =
        hPrev ^ ((delta - 1) * b) * hCurr ^ b := by
    rw [pow_mul, hrecPow, mul_pow, ← pow_mul]
  have hlcExp :
      (delta + 1) * t =
        ((prev.size - next.size) + a) + delta * b := by
    have hgap : (prev.size - next.size) + a = delta + t := by
      dsimp only [delta, t, a]
      omega
    rw [hgap, ht, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hprevExp :
      prev.size - 2 - J = delta + b := by
    dsimp only [delta, b]
    omega
  have hhExp :
      (delta - 1) * b + (prev.size - 2 - J) = delta * t := by
    rw [hprevExp, ht]
    have hd : delta = (delta - 1) + 1 := by omega
    calc
      (delta - 1) * b + (delta + b) =
          ((delta - 1) * b + b) + delta := by omega
      _ = ((delta - 1) + 1) * b + delta := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = delta * b + delta := by rw [← hd]
      _ = delta * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have hhCombine :
      hPrev ^ ((delta - 1) * b) * hPrev ^ (prev.size - 2 - J) =
        hPrev ^ (delta * t) := by
    rw [← Lean.Grind.Semiring.pow_add, hhExp]
  have hleftScalar :
      curr.leadingCoeff ^ ((delta + 1) * t) *
          (prev.leadingCoeff ^ t * hPrev ^ (prev.size - 2 - J)) =
        common * target := by
    rw [hlcExp, Lean.Grind.Semiring.pow_add,
      Lean.Grind.Semiring.pow_add, hrecPowB]
    dsimp only [common, target]
    calc
      curr.leadingCoeff ^ (prev.size - next.size) *
            curr.leadingCoeff ^ a *
            (hPrev ^ ((delta - 1) * b) * hCurr ^ b) *
            (prev.leadingCoeff ^ t * hPrev ^ (prev.size - 2 - J)) =
          curr.leadingCoeff ^ (prev.size - next.size) *
            prev.leadingCoeff ^ t *
            (hPrev ^ ((delta - 1) * b) *
              hPrev ^ (prev.size - 2 - J)) *
            (curr.leadingCoeff ^ a * hCurr ^ b) := by grind
      _ = curr.leadingCoeff ^ (prev.size - next.size) *
            prev.leadingCoeff ^ t * hPrev ^ (delta * t) *
            (curr.leadingCoeff ^ a * hCurr ^ b) := by rw [hhCombine]
  have hsign := sign_prem_cancel (S := S) prev.size curr.size J
    (Nat.le_of_lt hlt) hJcurr
  have hrightScalar :
      SubresultantMinor.sign (R := S)
          ((prev.size - 1 - J) * (curr.size - 1 - J)) *
          curr.leadingCoeff ^ (prev.size - next.size) *
          divisor ^ (curr.size - 1 - J) = common := by
    have hsEq : s =
        SubresultantMinor.sign (R := S) (prev.size - curr.size + 1) := by
      simp only [s, delta, negOnePow_eq_sign]
    dsimp only [divisor]
    rw [mul_pow, mul_pow, powNat_eq_pow, ← pow_mul, hsEq]
    dsimp only [common, t, delta]
    grind
  rw [hfamilyJ, scale_scale] at hdes
  change
    scale
        (curr.leadingCoeff ^ ((delta + 1) * t) *
          (prev.leadingCoeff ^ t * hPrev ^ (prev.size - 2 - J)))
        (Subresultant.poly J f g) = _ at hdes
  rw [hleftScalar] at hdes
  change
    scale (common * target) (Subresultant.poly J f g) =
      scale
        (SubresultantMinor.sign (R := S)
            ((prev.size - 1 - J) * (curr.size - 1 - J)) *
          curr.leadingCoeff ^ (prev.size - next.size) *
          divisor ^ (curr.size - 1 - J))
        (Subresultant.poly J curr next) at hdes
  rw [hrightScalar] at hdes
  have hcommon : common ≠ 0 := by
    dsimp only [common]
    exact ExactDivLaws.mul_ne_zero
      (ExactDivLaws.mul_ne_zero
        (pow_ne_zero h1 hcurrLc (prev.size - next.size))
        (pow_ne_zero h1 hprevLc t))
      (pow_ne_zero h1 hhPrev (delta * t))
  have heq :
      scale common (scale target (Subresultant.poly J f g)) =
        scale common (Subresultant.poly J curr next) := by
    rw [scale_scale]
    exact hdes
  have hcancel := scale_cancel hcommon heq
  simpa only [target, a, b] using hcancel.symm

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

/-- The integral subresultant invariant supplies every obligation in the
fuel-bounded executable Brown law. -/
private theorem brownLaw_of_inv {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (fuel : Nat) (prev curr : DensePoly S) (hPrev : S)
    (hinv : BrownInv f g prev curr hPrev) (hfuel : curr.size ≤ fuel) :
    BrownLaw prev curr hPrev fuel := by
  induction fuel generalizing prev curr hPrev with
  | zero =>
      rcases hinv with ⟨_, hcurr, _, _, _⟩
      have hpos := size_pos_of_ne_zero curr hcurr
      omega
  | succ fuel ih =>
      rcases hinv with ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      have hinv : BrownInv f g prev curr hPrev :=
        ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
      have hscale := BrownInv.nextScale f g prev curr hPrev hinv
      rcases hscale with ⟨_, hhCurrRaw, hscaleExactRaw⟩
      have hhCurr : hCurr ≠ 0 := by
        simpa only [hCurr, delta] using hhCurrRaw
      have hscaleExact :
          powNat curr.leadingCoeff delta =
            powNat hPrev (delta - 1) * hCurr := by
        simpa only [hCurr, delta] using hscaleExactRaw
      have hresult :
          prev ≠ 0 ∧ curr ≠ 0 ∧ curr.size < prev.size ∧
            hPrev ≠ 0 ∧ hCurr ≠ 0 ∧
            powNat curr.leadingCoeff delta =
              powNat hPrev (delta - 1) * hCurr ∧
            if p.isZero then
              True
            else
              let divisor :=
                negOnePow (R := S) (delta + 1) * prev.leadingCoeff *
                  powNat hPrev delta
              let next := divScalar p divisor
              divisor ≠ 0 ∧ p = scale divisor next ∧ next ≠ 0 ∧
                BrownLaw curr next hCurr fuel := by
        refine ⟨hprev, hcurr, hlt, hhPrev, hhCurr, hscaleExact, ?_⟩
        cases hpzero : p.isZero with
        | true => simp only [↓reduceIte]
        | false =>
            have hp : p ≠ 0 := ne_zero_of_isZero_false p hpzero
            let divisor :=
              negOnePow (R := S) (delta + 1) * prev.leadingCoeff *
                powNat hPrev delta
            let next := divScalar p divisor
            have hpRaw : (pseudoDivMod prev curr).2 ≠ 0 := by
              simpa only [p] using hp
            have hfactor := BrownInv.factor f g prev curr hPrev hinv hpRaw
            rcases hfactor with
              ⟨hdivisorRaw, hscaledRaw, hnextRaw, _⟩
            have hdivisor : divisor ≠ 0 := by
              simpa only [divisor, delta] using hdivisorRaw
            have hscaled : p = scale divisor next := by
              simpa only [p, divisor, next, delta] using hscaledRaw
            have hnext : next ≠ 0 := by
              simpa only [p, divisor, next, delta] using hnextRaw
            have hstepRaw := BrownInv.step f g prev curr hPrev hinv hpRaw
            have hstep : BrownInv f g curr next hCurr := by
              simpa only [p, divisor, next, hCurr, delta] using hstepRaw
            have hnextLt : next.size < curr.size := hstep.2.2.1
            have hrec := ih curr next hCurr hstep (by omega)
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨hdivisor, hscaled, hnext, hrec⟩
      simpa only [BrownLaw, delta, hCurr, p] using hresult

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

/-- Extract the corrected terminal scalar when the final stored polynomial is
a constant. -/
private def terminalValue {S : Type u} [Zero S] [DecidableEq S]
    (run : PRSResult S) : S :=
  let last := run.chain.getD (run.chain.size - 1) 0
  if last.size = 1 then run.scale else 0

/-- A worker launched from an integral Brown invariant returns the zeroth
subresultant coefficient of the original pair. -/
private theorem subresultantAux_terminal {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g prev curr : DensePoly S) (hPrev : S)
    (chain : Array (DensePoly S)) (fuel : Nat)
    (hinv : BrownInv f g prev curr hPrev) (hfuel : curr.size ≤ fuel)
    (hlast : chain.getD (chain.size - 1) 0 = curr) :
    terminalValue (subresultantAux prev curr hPrev chain fuel) =
      Subresultant.coeffMinor 0 0 f g := by
  induction fuel generalizing prev curr hPrev chain with
  | zero =>
      have hcurr : curr ≠ 0 := hinv.2.1
      have hpos := size_pos_of_ne_zero curr hcurr
      omega
  | succ fuel ih =>
      rcases hinv with ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
      let delta := prev.size - curr.size
      let hCurr := divExp curr.leadingCoeff hPrev delta
      let p := (pseudoDivMod prev curr).2
      have hinv : BrownInv f g prev curr hPrev :=
        ⟨hprev, hcurr, hlt, hhPrev, hfamily⟩
      have hscaleRaw := BrownInv.nextScale f g prev curr hPrev hinv
      have hscale :
          hCurr =
            (Subresultant.poly (curr.size - 1) f g).coeff (curr.size - 1) := by
        simpa only [hCurr, delta] using hscaleRaw.1
      cases hpzero : p.isZero with
      | true =>
          have hp : (pseudoDivMod prev curr).2 = 0 := by
            have : p = 0 := eq_zero_of_isZero_true p hpzero
            simpa only [p] using this
          unfold terminalValue
          simp only [subresultantAux, p, hpzero, ↓reduceIte]
          rw [hlast]
          by_cases hconst : curr.size = 1
          · rw [if_pos hconst]
            have hscale0 :
                hCurr = Subresultant.coeffMinor 0 0 f g := by
              simpa [hconst, Subresultant.coeff_poly] using hscale
            simpa only [hCurr, delta, hconst] using hscale0
          · rw [if_neg hconst]
            have hcurrPos := size_pos_of_ne_zero curr hcurr
            have hcurrBig : 2 ≤ curr.size := by omega
            have hlocal := Subresultant.coeffMinor_zero_of_prem_zero
              prev curr hcurr (Nat.le_of_lt hlt) hcurrBig hp
            have hinv0 := hfamily 0 hcurrPos
            have hcoeff := congrArg (fun q : DensePoly S => q.coeff 0) hinv0
            simp only [Subresultant.coeff_poly, coeff_scale_semiring] at hcoeff
            rw [hlocal] at hcoeff
            have hprevPos := size_pos_of_ne_zero prev hprev
            have hprevLc := leadingCoeff_ne_zero_of_pos_size prev hprevPos
            have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hprevLc
            have hscalar :
                prev.leadingCoeff ^ (curr.size - 1) *
                    hPrev ^ (prev.size - 2) ≠ 0 :=
              ExactDivLaws.mul_ne_zero
                (pow_ne_zero h1 hprevLc (curr.size - 1))
                (pow_ne_zero h1 hhPrev (prev.size - 2))
            have horig : Subresultant.coeffMinor 0 0 f g = 0 := by
              apply ExactDivLaws.mul_right_cancel hscalar
              grind
            exact horig.symm
      | false =>
          have hp : p ≠ 0 := ne_zero_of_isZero_false p hpzero
          let divisor :=
            negOnePow (R := S) (delta + 1) * prev.leadingCoeff *
              powNat hPrev delta
          let next := divScalar p divisor
          let nextImpl := divScalarImpl p divisor
          have hnextEq : next = nextImpl := divScalar_eq_divScalarImpl p divisor
          have hpRaw : (pseudoDivMod prev curr).2 ≠ 0 := by
            simpa only [p] using hp
          have hstepRaw := BrownInv.step f g prev curr hPrev hinv hpRaw
          have hstep : BrownInv f g curr next hCurr := by
            simpa only [p, divisor, next, hCurr, delta] using hstepRaw
          have hnext : next ≠ 0 := hstep.2.1
          have hnextImpl : nextImpl ≠ 0 := by
            rw [← hnextEq]
            exact hnext
          have hnextZero : nextImpl.isZero = false :=
            isZero_false_of_ne_zero nextImpl hnextImpl
          have hlast' :
              (chain.push next).getD ((chain.push next).size - 1) 0 = next := by
            rw [Array.size_push, show chain.size + 1 - 1 = chain.size by omega,
              getD_push_last]
          have hrec := ih curr next hCurr (chain.push next) hstep
            (by have := hstep.2.2.1; omega) hlast'
          simpa only [subresultantAux, delta, hCurr, p, hpzero,
            Bool.false_eq_true, ↓reduceIte, divisor, nextImpl, hnextZero,
            hnextEq] using hrec

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
    (f g : DensePoly S) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let delta := f.size - g.size
    let h₂ := powNat g.leadingCoeff delta
    let p := (pseudoDivMod f g).2
    if p.isZero then
      h₂ ≠ 0
    else
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      g₃ ≠ 0 ∧ BrownLaw g g₃ h₂ (g.size + 1) := by
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  have hgpos := size_pos_of_ne_zero g hg
  have hglc : g.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size g hgpos
  have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hglc
  have hh₂ : h₂ ≠ 0 := powNat_ne_zero h1 hglc delta
  change
    if p.isZero then
      h₂ ≠ 0
    else
      let g₃ := scaleImpl (negOnePow (R := S) (delta + 1)) p
      g₃ ≠ 0 ∧ BrownLaw g g₃ h₂ (g.size + 1)
  cases hpzero : p.isZero with
  | true =>
      simp only [↓reduceIte]
      exact hh₂
  | false =>
      let s := negOnePow (R := S) (delta + 1)
      let g₃ := scaleImpl s p
      have hp : p ≠ 0 := ne_zero_of_isZero_false p hpzero
      have hs : s ≠ 0 := negOnePow_ne_zero h1 (delta + 1)
      have hg₃Eq : g₃ = scale s p := by
        dsimp only [g₃]
        exact (scale_eq_scaleImpl s p).symm
      have hg₃ : g₃ ≠ 0 := by
        rw [hg₃Eq]
        exact scale_ne_zero hs hp
      have hpRaw : (pseudoDivMod f g).2 ≠ 0 := by
        simpa only [p] using hp
      have hinvRaw := brownInv_init f g hg hgf hpRaw
      have hinvScale : BrownInv f g g (scale s p) h₂ := by
        simpa only [delta, h₂, p, s] using hinvRaw
      have hinv : BrownInv f g g g₃ h₂ := by
        rw [hg₃Eq]
        exact hinvScale
      have hg₃lt : g₃.size < g.size := hinv.2.2.1
      have hlaw := brownLaw_of_inv f g (g.size + 1) g g₃ h₂ hinv
        (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte]
      simpa only [g₃, s] using ⟨hg₃, hlaw⟩

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

/-- For ordered nonzero inputs, Brown's corrected terminal value is the
zeroth generalized subresultant coefficient. -/
theorem resultantOrdered_eq_coeffMinor {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [ExactDivLaws S]
    (f g : DensePoly S) (hf : f ≠ 0) (hg : g ≠ 0)
    (hgf : g.size ≤ f.size) :
    resultantOrdered f g = Subresultant.coeffMinor 0 0 f g := by
  let delta := f.size - g.size
  let h₂ := powNat g.leadingCoeff delta
  let p := (pseudoDivMod f g).2
  have hfpos := size_pos_of_ne_zero f hf
  have hgpos := size_pos_of_ne_zero g hg
  have hglc := leadingCoeff_ne_zero_of_pos_size g hgpos
  have h1 : (1 : S) ≠ 0 := one_ne_zero_of_nonzero hglc
  cases hpzero : p.isZero with
  | true =>
      have hp : (pseudoDivMod f g).2 = 0 := by
        have : p = 0 := eq_zero_of_isZero_true p hpzero
        simpa only [p] using this
      have hlast :
          (#[f, g] : Array (DensePoly S)).getD
              ((#[f, g] : Array (DensePoly S)).size - 1) 0 = g := by
        rfl
      unfold resultantOrdered subresultantOrdered
        subresultantOrderedFuel
      simp only [p, hpzero, ↓reduceIte]
      rw [hlast]
      by_cases hconst : g.size = 1
      · rw [if_pos hconst]
        by_cases hfconst : f.size = 1
        · rw [show powNat g.leadingCoeff (f.size - g.size) = 1 by
            simp [hfconst, hconst, powNat]]
          unfold Subresultant.coeffMinor
          rw [show Subresultant.formalDegree f = 0 by
            simp [Subresultant.formalDegree, hfconst]]
          rw [show Subresultant.formalDegree g = 0 by
            simp [Subresultant.formalDegree, hconst]]
          rfl
        · have hminor := Subresultant.coeffMinorAt_rightDegree
            (f.size - 1) 0 0 f g (by omega) hconst
          have hff : Subresultant.formalDegree f = f.size - 1 := by
            simp [Subresultant.formalDegree]
          have hgg : Subresultant.formalDegree g = 0 := by
            simp [Subresultant.formalDegree, hconst]
          have hgc : g.coeff 0 = g.leadingCoeff := by
            simpa [hconst] using (leadingCoeff_eq_coeff_last g hgpos).symm
          unfold Subresultant.coeffMinor
          rw [hff, hgg, hminor, hgc]
          rw [powNat_eq_pow]
          rw [← Lean.Grind.Semiring.pow_succ]
          congr 1
          omega
      · rw [if_neg hconst]
        have hgBig : 2 ≤ g.size := by omega
        have hzero := Subresultant.coeffMinor_zero_of_prem_zero
          f g hg hgf hgBig hp
        exact hzero.symm
  | false =>
      have hp : p ≠ 0 := ne_zero_of_isZero_false p hpzero
      let s := negOnePow (R := S) (delta + 1)
      let g₃ := scaleImpl s p
      have hs : s ≠ 0 := negOnePow_ne_zero h1 (delta + 1)
      have hg₃Eq : g₃ = scale s p := by
        rw [scale_eq_scaleImpl]
      have hg₃ : g₃ ≠ 0 := by
        rw [hg₃Eq]
        exact scale_ne_zero hs hp
      have hg₃Zero : g₃.isZero = false := isZero_false_of_ne_zero g₃ hg₃
      have hpRaw : (pseudoDivMod f g).2 ≠ 0 := by
        simpa only [p] using hp
      have hinvRaw := brownInv_init f g hg hgf hpRaw
      have hinv : BrownInv f g g g₃ h₂ := by
        rw [hg₃Eq]
        simpa only [delta, h₂, p, s] using hinvRaw
      have hlast :
          (#[f, g, g₃] : Array (DensePoly S)).getD
              ((#[f, g, g₃] : Array (DensePoly S)).size - 1) 0 = g₃ := by
        rfl
      have hterminal := subresultantAux_terminal f g g g₃ h₂
        #[f, g, g₃] (g.size + 1) hinv (by
          have := hinv.2.2.1
          omega) hlast
      unfold terminalValue at hterminal
      unfold resultantOrdered subresultantOrdered subresultantOrderedFuel
      simp only [delta, p, hpzero, Bool.false_eq_true, ↓reduceIte,
        s, g₃, hg₃Zero]
      exact hterminal

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
