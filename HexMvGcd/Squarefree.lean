/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Squarefree.Core

@[expose] public section
set_option backward.proofsInPublic true

/-!
Characteristic-zero squarefree decomposition.

This module proves the Yun loop invariants, combines them with recursive
coefficient content, and exposes the executable decomposition and its public
correctness theorems. Foundational squarefree criteria and merge invariants live
in `HexMvGcd.Squarefree.Core`.
-/

namespace Hex.MvPoly

universe u

attribute [local instance] Lean.Grind.Semiring.natCast
attribute [local instance] Lean.Grind.Ring.intCast

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
  [GcdProducer R]

/-- One decreasing Yun layer in the selected main variable.  The fuel is the
total degree of the primitive input plus one; in characteristic zero every
nonterminal layer removes at least one degree from `b`. -/
def yunLoop [NatNoZero R] [IsMonomialOrder cmp] (i : Fin n) (fuel k : Nat)
    (b d : MvPoly n R cmp) (acc : List (SqfFactor n R cmp)) :
    List (SqfFactor n R cmp) :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
      if polyIsUnit b then acc.reverse
      else
        let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        let acc := if polyIsUnit factor then acc else ⟨factor, k⟩ :: acc
        yunLoop i fuel (k + 1) nextB nextD acc

private def yunContribution [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) : Nat → Nat → MvPoly n R cmp → MvPoly n R cmp →
      MvPoly n R cmp
  | 0, _, _, _ => 1
  | fuel + 1, k, b, d =>
      if polyIsUnit b then 1
      else
        let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        let tail := yunContribution i fuel (k + 1) nextB nextD
        if polyIsUnit factor then tail else factor ^ k * tail

private structure YunState [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    (b d target residual : MvPoly (m + 1) R order) : Prop where
  b_ne : b ≠ 0
  residual_ne : residual ≠ 0
  reconstruct : b ^ k * residual = target
  differential : d * residual = b * derivative i residual
  primitive : Primitive target
  normalized : polyNormalize target = target
  content_one : contentIn i Mono.lex residual = 1
  coprime : ∀ e, e ∣ b →
    e ∣ ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d →
      polyIsUnit e = true

private theorem yunState_step [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    {b d target residual : MvPoly (m + 1) R order}
    (state : YunState i k b d target residual) :
    let factor := gcd b d
    let nextB := quotient b factor
    let nextC := quotient d factor
    let nextD := nextC - derivative i nextB
    ∃ nextTarget nextResidual,
      YunState i (k + 1) nextB nextD nextTarget nextResidual ∧
        factor ^ k * nextTarget = target := by
  let factor := gcd b d
  let nextB := quotient b factor
  let nextC := quotient d factor
  let nextD := nextC - derivative i nextB
  rcases gcd_quotients state.b_ne with
    ⟨hfactor0, hnextB, hnextC, hcoprime⟩
  have hcancelFactor :
      nextC * residual = nextB * derivative i residual := by
    have hzero : factor *
        (nextC * residual - nextB * derivative i residual) = 0 := by
      calc
        factor * (nextC * residual - nextB * derivative i residual) =
            (nextC * factor) * residual -
              (nextB * factor) * derivative i residual := by grind
        _ = d * residual - b * derivative i residual := by
          rw [hnextC, hnextB]
        _ = 0 := by rw [state.differential]; grind
    rcases GcdDomainLaws.no_zero_div factor _ hzero with hzero | hrest
    · exact False.elim (hfactor0 hzero)
    · grind
  have hnextB0 : nextB ≠ 0 := by
    intro hzero
    apply state.b_ne
    calc
      b = nextB * factor := hnextB.symm
      _ = 0 := by rw [hzero, MvPoly.zero_mul]
  have hnextBResidual : nextB ∣ residual := by
    have hcoprime' : ∀ e, e ∣ nextC → e ∣ nextB → ∃ u, e * u = 1 :=
      fun e heC heB => (polyIsUnit_iff e).mp (hcoprime e heB heC)
    have hleft : nextB ∣ residual * nextC := by
      refine ⟨derivative i residual, ?_⟩
      calc
        residual * nextC = nextC * residual := MvPoly.mul_comm ..
        _ = nextB * derivative i residual := hcancelFactor
        _ = derivative i residual * nextB := MvPoly.mul_comm ..
    have hright : nextB ∣ residual * nextB :=
      ⟨residual, rfl⟩
    exact CoprimeCancelLaws.cancel_coprime residual nextC nextB nextB
      hcoprime' hleft hright
  let nextResidual := quotient residual nextB
  have hnextResidual : nextResidual * nextB = residual :=
    quotient_mul_of_dvd hnextB0 hnextBResidual
  have hnextResidual0 : nextResidual ≠ 0 := by
    intro hzero
    apply state.residual_ne
    change residual = 0
    calc
      residual = nextResidual * nextB := hnextResidual.symm
      _ = 0 := by rw [hzero, MvPoly.zero_mul]
  have hcancelNextB :
      nextC * nextResidual =
        derivative i nextB * nextResidual +
          nextB * derivative i nextResidual := by
    have hzero : nextB *
        (nextC * nextResidual -
          (derivative i nextB * nextResidual +
            nextB * derivative i nextResidual)) = 0 := by
      calc
        nextB * (nextC * nextResidual -
            (derivative i nextB * nextResidual +
              nextB * derivative i nextResidual)) =
            nextC * (nextResidual * nextB) -
              nextB * derivative i (nextResidual * nextB) := by
          rw [derivative_mul]
          grind
        _ = nextC * residual - nextB * derivative i residual := by
          rw [hnextResidual]
        _ = 0 := by rw [hcancelFactor]; grind
    rcases GcdDomainLaws.no_zero_div nextB _ hzero with hzero | hrest
    · exact False.elim (hnextB0 hzero)
    · grind
  have hnextDifferential :
      nextD * nextResidual =
        nextB * derivative i nextResidual := by
    change (nextC - derivative i nextB) * nextResidual = _
    grind
  let nextTarget := nextB ^ (k + 1) * nextResidual
  have htarget : factor ^ k * nextTarget = target := by
    change factor ^ k * (nextB ^ (k + 1) * nextResidual) = target
    calc
      factor ^ k * (nextB ^ (k + 1) * nextResidual) =
          (nextB * factor) ^ k * (nextResidual * nextB) := by
        rw [Lean.Grind.CommSemiring.mul_pow]
        rw [MvPoly.pow_succ]
        grind
      _ = b ^ k * residual := by rw [hnextB, hnextResidual]
      _ = target := state.reconstruct
  have htarget0 : nextTarget ≠ 0 := by
    intro hzero
    have hzeroTarget : target = 0 := by
      calc
        target = factor ^ k * nextTarget := htarget.symm
        _ = 0 := by rw [hzero, MvPoly.mul_zero]
    have hstateTarget0 : target ≠ 0 := by
      intro ht
      have hz := state.reconstruct.trans ht
      rcases GcdDomainLaws.no_zero_div (b ^ k) residual hz with _ | he
      · exact (mv_pow_ne_zero state.b_ne k) ‹_›
      · exact state.residual_ne he
    exact False.elim (hstateTarget0 hzeroTarget)
  have hnextPrimitive : Primitive nextTarget := by
    apply primitive_of_dvd_primitive state.primitive
    exact ⟨factor ^ k, htarget.symm⟩
  have hfactorNormalized : polyNormalize factor = factor :=
    gcd_normalized b d
  have hfactorPowerNormalized : polyNormalize (factor ^ k) = factor ^ k :=
    polyNormalize_pow hfactorNormalized k
  have hnextNormalized : polyNormalize nextTarget = nextTarget := by
    apply normalized_left_factor state.normalized hfactorPowerNormalized
      (mv_pow_ne_zero hfactor0 k)
    rw [MvPoly.mul_comm]
    exact htarget
  have hnextContent : contentIn i Mono.lex nextResidual = 1 := by
    apply contentIn_one_of_dvd (R := R) (m := m) (order := order)
      i state.content_one
    refine ⟨nextB, ?_⟩
    calc
      residual = nextResidual * nextB := hnextResidual.symm
      _ = nextB * nextResidual := MvPoly.mul_comm ..
  have hnextCoprime : ∀ e, e ∣ nextB →
      e ∣ (((k + 1 : Nat) : MvPoly (m + 1) R order) *
          derivative i nextB + nextD) → polyIsUnit e = true := by
    intro e heB heNext
    have hnextExpression :
        (((k + 1 : Nat) : MvPoly (m + 1) R order) *
            derivative i nextB + nextD) =
          ((k : Nat) : MvPoly (m + 1) R order) *
            derivative i nextB + nextC := by
      change ((k + 1 : Nat) : MvPoly (m + 1) R order) *
          derivative i nextB + (nextC - derivative i nextB) = _
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_one]
      grind
    rw [hnextExpression] at heNext
    have heOldB : e ∣ b := by
      rcases heB with ⟨a, ha⟩
      refine ⟨a * factor, ?_⟩
      calc
        b = nextB * factor := hnextB.symm
        _ = (a * e) * factor := by rw [ha]
        _ = (a * factor) * e := by grind
    have heFirst : e ∣ factor *
        (((k : Nat) : MvPoly (m + 1) R order) *
          derivative i nextB + nextC) :=
      dvd_mul_left_poly factor heNext
    have heSecond : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * nextB *
          derivative i factor := by
      rcases heB with ⟨a, ha⟩
      refine ⟨((k : Nat) : MvPoly (m + 1) R order) * a *
          derivative i factor, ?_⟩
      rw [ha]
      grind
    have heOld : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d := by
      have hsum := dvd_add_poly heFirst heSecond
      have heq :
          factor * (((k : Nat) : MvPoly (m + 1) R order) *
              derivative i nextB + nextC) +
            ((k : Nat) : MvPoly (m + 1) R order) * nextB *
              derivative i factor =
            ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d := by
        rw [← hnextB, derivative_mul, ← hnextC]
        grind
      rw [heq] at hsum
      exact hsum
    exact state.coprime e heOldB heOld
  refine ⟨nextTarget, nextResidual, ?_, htarget⟩
  exact
    { b_ne := hnextB0
      residual_ne := hnextResidual0
      reconstruct := rfl
      differential := hnextDifferential
      primitive := hnextPrimitive
      normalized := hnextNormalized
      content_one := hnextContent
      coprime := hnextCoprime }

private theorem unit_of_derivative_zero_contentIn_one [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hderivative : derivative i p = 0)
    (hcontent : contentIn i Mono.lex p = 1) : polyIsUnit p = true := by
  let view := toUnivariate i Mono.lex p
  let constant := view.coeff 0
  have hviewDerivative : DensePoly.derivative view = 0 := by
    rw [← toUnivariate_derivative, hderivative, toUnivariate_zero]
  have hview : view = DensePoly.C constant := by
    apply DensePoly.ext_coeff
    intro k
    cases k with
    | zero => rw [DensePoly.coeff_C, ite_eq_left rfl]
    | succ k =>
        have hcoeff := congrArg
          (fun q : DensePoly (MvPoly m R Mono.lex) => q.coeff k)
          hviewDerivative
        rw [DensePoly.coeff_derivative_semiring, DensePoly.coeff_zero] at hcoeff
        have hcast :
            ((k + 1 : Nat) : MvPoly m R Mono.lex) ≠ 0 := by
          intro hzero
          have hzeroCoeff := congrArg (coeff Mono.zero) hzero
          rw [coeff_natCast, coeff_zero, ite_eq_left rfl] at hzeroCoeff
          exact NatNoZero.natCast_ne_zero (k + 1) (by omega) hzeroCoeff
        have hcoefficient : view.coeff (k + 1) = 0 := by
          rcases GcdDomainLaws.no_zero_div
              ((k + 1 : Nat) : MvPoly m R Mono.lex)
              (view.coeff (k + 1)) hcoeff with hzero | hzero
          · exact False.elim (hcast hzero)
          · exact hzero
        rw [DensePoly.coeff_C, ite_eq_right (by omega)]
        exact hcoefficient
  have hpConst : p = constIn (cmp := order) i Mono.lex constant := by
    calc
      p = ofUnivariate i Mono.lex view :=
        (ofUnivariate_toUnivariate i p).symm
      _ = ofUnivariate i Mono.lex (DensePoly.C constant) := by rw [hview]
      _ = constIn (cmp := order) i Mono.lex constant := rfl
  have hconstantDiv : constant ∣ contentIn i Mono.lex p := by
    apply dvd_contentIn i Mono.lex p constant
    intro k
    change constant ∣ view.coeff k
    rw [hview, DensePoly.coeff_C]
    split
    · exact ⟨1, (MvPoly.one_mul constant).symm⟩
    · exact ⟨0, (MvPoly.zero_mul constant).symm⟩
  rw [hcontent] at hconstantDiv
  rcases hconstantDiv with ⟨inverse, hinverse⟩
  apply (polyIsUnit_iff p).mpr
  refine ⟨constIn (cmp := order) i Mono.lex inverse, ?_⟩
  have hone : constant * inverse = 1 := by
    calc
      constant * inverse = inverse * constant := MvPoly.mul_comm ..
      _ = 1 := hinverse.symm
  rw [hpConst, ← constIn_mul, hone, constIn_one]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem totalDegree_monomial_le
    (p : MvPoly n R cmp) {m : Mono n} (hm : m ∈ p.monomials) :
    Mono.degree m ≤ p.totalDegree := by
  unfold monomials at hm
  rcases List.mem_map.mp hm with ⟨term, hterm, hfirst⟩
  rcases term with ⟨k, c⟩
  simp only at hfirst
  subst k
  rw [totalDegree_eq]
  unfold foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have le_start (terms : List (Mono n × R)) (init : Nat) :
      init ≤ terms.foldl
        (fun d term => max d (Mono.degree term.1)) init := by
    induction terms generalizing init with
    | nil => exact Nat.le_refl _
    | cons term terms ih =>
        exact Nat.le_trans (Nat.le_max_left ..) (ih _)
  have member_bound :
      ∀ (terms : List (Mono n × R)) (init : Nat) {term},
        term ∈ terms →
          Mono.degree term.1 ≤ terms.foldl
            (fun d term => max d (Mono.degree term.1)) init := by
    intro terms init term hterm
    induction terms generalizing init with
    | nil => simp at hterm
    | cons head terms ih =>
        simp only [List.foldl_cons]
        cases List.mem_cons.mp hterm with
        | inl h =>
            subst head
            exact Nat.le_trans (Nat.le_max_right ..) (le_start terms _)
        | inr h => exact ih _ h
  exact member_bound p.termsList 0 hterm

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem view_size_le_totalDegree_succ
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (p : MvPoly (m + 1) R order) :
    (toUnivariate i Mono.lex p).size ≤ p.totalDegree + 1 := by
  let view := toUnivariate i Mono.lex p
  by_cases hsize : view.size = 0
  · change view.size ≤ p.totalDegree + 1
    omega
  have hpos : 0 < view.size := Nat.pos_of_ne_zero hsize
  have hleading0 : view.leadingCoeff ≠ (0 : MvPoly m R Mono.lex) :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size view hpos
  cases hterm : view.leadingCoeff.leadingTerm with
  | none =>
      exact False.elim
        (hleading0 ((leadingTerm_eq_none_iff view.leadingCoeff).mp hterm))
  | some term =>
      rcases term with ⟨monomial, coefficient⟩
      have hcoefficient0 : coefficient ≠ 0 := by
        intro hzero
        have hstored :=
          (leadingTerm_eq_some_iff view.leadingCoeff monomial coefficient).mp
            hterm |>.1
        subst coefficient
        exact (view.leadingCoeff.coeff?_ne_zero monomial) hstored
      have hsourceCoeff :
          coeff (insertVar i (view.size - 1) monomial) p = coefficient := by
        rw [← toUnivariate_coeff (cmp' := Mono.lex) i p]
        change coeff monomial (view.coeff (view.size - 1)) = coefficient
        rw [← DensePoly.leadingCoeff_eq_coeff_last view hpos]
        exact coeff_eq_of_leadingTerm hterm
      have hsourceMem :
          insertVar i (view.size - 1) monomial ∈ p.monomials :=
        (mem_monomials_iff _ p).mpr (hsourceCoeff ▸ hcoefficient0)
      have htotal := totalDegree_monomial_le p hsourceMem
      have hcoordinate :=
        Mono.degreeOf_le_degree i (insertVar i (view.size - 1) monomial)
      rw [degreeOf_insertVar] at hcoordinate
      change view.size ≤ p.totalDegree + 1
      omega

omit [LawfulBezoutOps R] [GcdProducer R] in
private theorem exponent_le_totalDegree_of_pow_dvd [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    {source b : MvPoly (m + 1) R order} {k : Nat}
    (hsource : source ≠ 0) (hconst : ¬ IsConst b) (hk : 0 < k)
    (hdiv : b ^ k ∣ source) : k ≤ source.totalDegree := by
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hconst
    subst b
    simp [IsConst]
  have hvars : b.vars ≠ [] := hconst
  cases hvarsEq : b.vars with
  | nil => exact False.elim (hvars hvarsEq)
  | cons i tail =>
      have hi : i ∈ b.vars := by rw [hvarsEq]; simp
      have hpowerLower := view_pow_size_lower i b hi (k - 1)
      have hkPower : k - 1 + 1 = k := by omega
      rw [hkPower] at hpowerLower
      rcases hdiv with ⟨q, hq⟩
      have hq0 : q ≠ 0 := by
        intro hzero
        apply hsource
        rw [hq, hzero, MvPoly.zero_mul]
      have hqView : toUnivariate i Mono.lex q ≠ 0 := by
        intro hzero
        apply hq0
        calc
          q = ofUnivariate i Mono.lex (toUnivariate i Mono.lex q) :=
            (ofUnivariate_toUnivariate i q).symm
          _ = 0 := by rw [hzero]; rfl
      have hpower0 : b ^ k ≠ 0 := mv_pow_ne_zero hb0 k
      have hpowerView : toUnivariate i Mono.lex (b ^ k) ≠ 0 := by
        intro hzero
        apply hpower0
        calc
          b ^ k = ofUnivariate i Mono.lex
              (toUnivariate i Mono.lex (b ^ k)) :=
            (ofUnivariate_toUnivariate i (b ^ k)).symm
          _ = 0 := by rw [hzero]; rfl
      have hqPos : 0 < (toUnivariate i Mono.lex q).size :=
        Nat.pos_of_ne_zero
          (fun h => hqView ((DensePoly.size_eq_zero_iff _).mp h))
      have hpowerPos : 0 < (toUnivariate i Mono.lex (b ^ k)).size :=
        Nat.pos_of_ne_zero
          (fun h => hpowerView ((DensePoly.size_eq_zero_iff _).mp h))
      have htop :
          (toUnivariate i Mono.lex q).leadingCoeff *
              (toUnivariate i Mono.lex (b ^ k)).leadingCoeff ≠
            (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases GcdDomainLaws.no_zero_div _ _ hzero with hl | hr
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size _ hqPos) hl
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size _ hpowerPos) hr
      have hproduct := DensePoly.size_mul_of_top_ne
        (toUnivariate i Mono.lex q) (toUnivariate i Mono.lex (b ^ k))
        hqPos hpowerPos htop
      have hviewEq := congrArg
        (fun f => (toUnivariate i Mono.lex f).size) hq
      rw [toUnivariate_mul, hproduct] at hviewEq
      have hsourceUpper := view_size_le_totalDegree_succ i source
      omega

private theorem yunState_terminal [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    {b d target residual : MvPoly (m + 1) R order}
    (state : YunState i k b d target residual)
    (hunit : polyIsUnit b = true) : target = 1 := by
  rcases (polyIsUnit_iff b).mp hunit with ⟨u, hu⟩
  have hresidualDvd : residual ∣ derivative i residual := by
    refine ⟨u * d, ?_⟩
    calc
      derivative i residual = 1 * derivative i residual :=
        (MvPoly.one_mul _).symm
      _ = (b * u) * derivative i residual := by rw [hu]
      _ = u * (b * derivative i residual) := by grind
      _ = u * (d * residual) := by rw [state.differential]
      _ = (u * d) * residual := by grind
  have hderivative : derivative i residual = 0 :=
    derivative_eq_zero_of_dvd i residual state.residual_ne hresidualDvd
  have hresidualUnit : polyIsUnit residual = true :=
    unit_of_derivative_zero_contentIn_one i hderivative state.content_one
  rcases (polyIsUnit_iff residual).mp hresidualUnit with ⟨v, hv⟩
  have honePow : ∀ j : Nat, (1 : MvPoly (m + 1) R order) ^ j = 1 := by
    intro j
    induction j with
    | zero => exact MvPoly.pow_zero 1
    | succ j ih => rw [MvPoly.pow_succ, ih, MvPoly.one_mul]
  have hpower : b ^ k * u ^ k = 1 := by
    calc
      b ^ k * u ^ k = (b * u) ^ k :=
        (Lean.Grind.CommSemiring.mul_pow b u k).symm
      _ = 1 := by
        rw [hu]
        exact honePow k
  have htargetUnit : polyIsUnit target = true := by
    apply (polyIsUnit_iff target).mpr
    refine ⟨v * u ^ k, ?_⟩
    calc
      target * (v * u ^ k) =
          (b ^ k * residual) * (v * u ^ k) := by
        rw [state.reconstruct]
      _ = (b ^ k * u ^ k) * (residual * v) := by grind
      _ = 1 := by rw [hpower, hv, MvPoly.one_mul]
  calc
    target = polyNormalize target := state.normalized.symm
    _ = 1 := polyNormalize_unit target htargetUnit

private theorem yunContribution_correct [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (source : MvPoly (m + 1) R order)
    (hsource : source ≠ 0) :
    ∀ fuel k b d target residual,
      0 < k → target ∣ source → source.totalDegree < k + fuel →
      YunState i k b d target residual →
        yunContribution i fuel k b d = target := by
  intro fuel
  induction fuel with
  | zero =>
      intro k b d target residual hk htargetSource hbound state
      rw [yunContribution]
      by_cases hunit : polyIsUnit b = true
      · exact (yunState_terminal i k state hunit).symm
      · exfalso
        have hconst : ¬ IsConst b := by
          intro hconst
          have hbDvdTarget : b ∣ target := by
            refine ⟨b ^ (k - 1) * residual, ?_⟩
            calc
              target = b ^ k * residual := state.reconstruct.symm
              _ = (b ^ (k - 1) * residual) * b := by
                rw [show k = k - 1 + 1 by omega, MvPoly.pow_succ]
                grind
          exact hunit (unit_of_const_dvd_primitive state.primitive hconst
            hbDvdTarget)
        have hpowerTarget : b ^ k ∣ target := by
          refine ⟨residual, ?_⟩
          calc
            target = b ^ k * residual := state.reconstruct.symm
            _ = residual * b ^ k := MvPoly.mul_comm ..
        rcases htargetSource with ⟨a, ha⟩
        rcases hpowerTarget with ⟨r, hr⟩
        have hpowerSource : b ^ k ∣ source := by
          refine ⟨a * r, ?_⟩
          calc
            source = a * target := ha
            _ = a * (r * b ^ k) := by rw [hr]
            _ = (a * r) * b ^ k := by grind
        have hdegree := exponent_le_totalDegree_of_pow_dvd
          hsource hconst hk hpowerSource
        omega
  | succ fuel ih =>
      intro k b d target residual hk htargetSource hbound state
      simp only [yunContribution]
      by_cases hunitB : polyIsUnit b = true
      · rw [if_pos hunitB]
        exact (yunState_terminal i k state hunitB).symm
      · rw [if_neg hunitB]
        let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        rcases yunState_step i k state with
          ⟨nextTarget, nextResidual, nextState, hfactorTarget⟩
        change factor ^ k * nextTarget = target at hfactorTarget
        have hnextTargetSource : nextTarget ∣ source := by
          rcases htargetSource with ⟨a, ha⟩
          refine ⟨a * factor ^ k, ?_⟩
          calc
            source = a * target := ha
            _ = a * (factor ^ k * nextTarget) := by rw [hfactorTarget]
            _ = (a * factor ^ k) * nextTarget := by grind
        have hnextBound : source.totalDegree < (k + 1) + fuel := by
          omega
        have htail :
            yunContribution i fuel (k + 1) nextB nextD = nextTarget :=
          ih (k + 1) nextB nextD nextTarget nextResidual (by omega)
            hnextTargetSource hnextBound nextState
        change
          (if polyIsUnit factor then
            yunContribution i fuel (k + 1) nextB nextD
          else factor ^ k * yunContribution i fuel (k + 1) nextB nextD) =
            target
        by_cases hunitFactor : polyIsUnit factor = true
        · rw [if_pos hunitFactor, htail]
          have hfactorOne : factor = 1 := by
            calc
              factor = polyNormalize factor := (gcd_normalized b d).symm
              _ = 1 := polyNormalize_unit factor hunitFactor
          rw [hfactorOne] at hfactorTarget
          rw [mv_one_pow, MvPoly.one_mul] at hfactorTarget
          exact hfactorTarget
        · rw [if_neg hunitFactor, htail, hfactorTarget]

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem yunLoop_product [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp)) :
    sqfProduct (yunLoop i fuel k b d acc) =
      sqfProduct acc.reverse * yunContribution i fuel k b d := by
  induction fuel generalizing k b d acc with
  | zero =>
      rw [yunLoop, yunContribution, MvPoly.mul_one]
  | succ fuel ih =>
      simp only [yunLoop, yunContribution]
      split
      · rw [MvPoly.mul_one]
      · split
        · rw [ih]
        · rename_i hfactor
          rw [ih]
          rw [List.reverse_cons, sqfProduct_append, sqfProduct_cons,
            sqfProduct_nil, MvPoly.mul_one]
          grind

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem yunLoop_acc [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp)) :
    yunLoop i fuel k b d acc = acc.reverse ++ yunLoop i fuel k b d [] := by
  induction fuel generalizing k b d acc with
  | zero => simp [yunLoop]
  | succ fuel ih =>
      simp only [yunLoop]
      split
      · simp
      · split
        · rw [ih]
        · rw [ih]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
            List.append_assoc]
          symm
          rw [ih]
          simp

private structure YunEntryProps
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (factor nextB b : MvPoly (m + 1) R order) : Prop where
  squarefree : Squarefree factor
  primitive : Primitive factor
  nonconstant : ¬ IsConst factor
  divides : factor ∣ b
  coprime_next : ∀ e, e ∣ factor → e ∣ nextB → polyIsUnit e = true

private theorem yunEntryProps [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) (k : Nat)
    {b d target residual : MvPoly (m + 1) R order}
    (state : YunState i k b d target residual) (hk : 0 < k)
    (hnonunit : polyIsUnit (gcd b d) ≠ true) :
    YunEntryProps (gcd b d) (quotient b (gcd b d)) b := by
  let factor := gcd b d
  let nextB := quotient b factor
  let nextC := quotient d factor
  rcases gcd_quotients state.b_ne with
    ⟨hfactor0, hnextB, hnextC, _⟩
  change factor ≠ 0 at hfactor0
  change nextB * factor = b at hnextB
  change nextC * factor = d at hnextC
  have hfactorB : factor ∣ b := gcd_dvd_left b d
  have hbTarget : b ∣ target := by
    refine ⟨b ^ (k - 1) * residual, ?_⟩
    calc
      target = b ^ k * residual := state.reconstruct.symm
      _ = (b ^ (k - 1) * residual) * b := by
        rw [show k = k - 1 + 1 by omega, MvPoly.pow_succ]
        grind
  have hfactorTarget : factor ∣ target := Hex.dvdTrans hfactorB hbTarget
  have hfactorPrimitive : Primitive factor :=
    primitive_of_dvd_primitive state.primitive hfactorTarget
  have hfactorNonconstant : ¬ IsConst factor := by
    intro hconst
    exact hnonunit
      (unit_of_const_dvd_primitive state.primitive hconst hfactorTarget)
  have hfactorSquarefree : Squarefree factor := by
    refine ⟨hfactor0, ?_⟩
    intro e heSquare
    have heFactor : e ∣ factor := by
      rcases heSquare with ⟨a, ha⟩
      refine ⟨a * e, ?_⟩
      calc
        factor = a * (e * e) := ha
        _ = (a * e) * e := by grind
    have heDerivative : e ∣ derivative i factor :=
      derivative_dvd_of_square_dvd i heSquare
    have heB : e ∣ b := Hex.dvdTrans heFactor hfactorB
    have heDerivativeB : e ∣ derivative i b := by
      rw [← hnextB, derivative_mul]
      apply dvd_add_poly
      · exact dvd_mul_left_poly (derivative i nextB) heFactor
      · exact dvd_mul_left_poly nextB heDerivative
    have heD : e ∣ d := by
      exact Hex.dvdTrans heFactor (gcd_dvd_right b d)
    have heExpression : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d :=
      dvd_add_poly
        (dvd_mul_left_poly
          ((k : Nat) : MvPoly (m + 1) R order) heDerivativeB)
        heD
    exact isConst_of_unit e (state.coprime e heB heExpression)
  have hfactorNext : ∀ e, e ∣ factor → e ∣ nextB →
      polyIsUnit e = true := by
    intro e heFactor heNextB
    have heB : e ∣ b := Hex.dvdTrans heFactor hfactorB
    have heDerivativeB : e ∣ derivative i b := by
      rw [← hnextB, derivative_mul]
      apply dvd_add_poly
      · exact dvd_mul_left_poly (derivative i nextB) heFactor
      · exact dvd_mul_right_poly (derivative i factor) heNextB
    have heD : e ∣ d :=
      Hex.dvdTrans heFactor (gcd_dvd_right b d)
    have heExpression : e ∣
        ((k : Nat) : MvPoly (m + 1) R order) * derivative i b + d :=
      dvd_add_poly
        (dvd_mul_left_poly
          ((k : Nat) : MvPoly (m + 1) R order) heDerivativeB)
        heD
    exact state.coprime e heB heExpression
  exact
    { squarefree := hfactorSquarefree
      primitive := hfactorPrimitive
      nonconstant := hfactorNonconstant
      divides := hfactorB
      coprime_next := hfactorNext }

private structure YunFactors
    {n : Nat} {order : Mono n → Mono n → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    (root : MvPoly n R order) (factors : List (SqfFactor n R order)) : Prop where
  squarefree : ∀ factor ∈ factors, Squarefree factor.factor
  primitive : ∀ factor ∈ factors, Primitive factor.factor
  nonconstant : ∀ factor ∈ factors, ¬ IsConst factor.factor
  divides : ∀ factor ∈ factors, factor.factor ∣ root
  pairwise : factors.Pairwise fun left right =>
    ∀ d, d ∣ left.factor → d ∣ right.factor → polyIsUnit d = true

private theorem yunLoop_properties [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) :
    ∀ (fuel k : Nat)
      (b d target residual : MvPoly (m + 1) R order),
      0 < k → YunState i k b d target residual →
        YunFactors b (yunLoop i fuel k b d []) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k b d target residual hk state
      simp only [yunLoop]
      exact
        { squarefree := by simp
          primitive := by simp
          nonconstant := by simp
          divides := by simp
          pairwise := by simp }
  | succ fuel ih =>
      intro k b d target residual hk state
      by_cases hunitB : polyIsUnit b = true
      · rw [yunLoop, if_pos hunitB]
        exact
          { squarefree := by simp
            primitive := by simp
            nonconstant := by simp
            divides := by simp
            pairwise := by simp }
      · let factor := gcd b d
        let nextB := quotient b factor
        let nextC := quotient d factor
        let nextD := nextC - derivative i nextB
        rcases yunState_step i k state with
          ⟨nextTarget, nextResidual, nextState, _⟩
        have htail := ih (k + 1) nextB nextD nextTarget nextResidual
          (by omega) nextState
        have hnextBdiv : nextB ∣ b := by
          have hnextBEq : nextB * factor = b :=
            (gcd_quotients state.b_ne).2.1
          refine ⟨factor, ?_⟩
          calc
            b = nextB * factor := hnextBEq.symm
            _ = factor * nextB := MvPoly.mul_comm ..
        by_cases hunitFactor : polyIsUnit factor = true
        · rw [yunLoop, if_neg hunitB]
          change YunFactors b (yunLoop i fuel (k + 1) nextB nextD
            (if polyIsUnit factor then [] else
              [{ factor := factor, multiplicity := k }]))
          rw [if_pos hunitFactor]
          exact
            { squarefree := htail.squarefree
              primitive := htail.primitive
              nonconstant := htail.nonconstant
              divides := by
                intro entry hentry
                exact Hex.dvdTrans (htail.divides entry hentry) hnextBdiv
              pairwise := htail.pairwise }
        · have hentry := yunEntryProps i k state hk hunitFactor
          let entry : SqfFactor (m + 1) R order :=
            { factor := factor, multiplicity := k }
          have hloop :
              yunLoop i (fuel + 1) k b d [] =
                entry :: yunLoop i fuel (k + 1) nextB nextD [] := by
            rw [yunLoop, if_neg hunitB]
            change yunLoop i fuel (k + 1) nextB nextD
              (if polyIsUnit factor then [] else
                [{ factor := factor, multiplicity := k }]) = _
            rw [if_neg hunitFactor, yunLoop_acc]
            simp [entry]
          rw [hloop]
          exact
            { squarefree := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.squarefree
                · exact htail.squarefree candidate hcandidate
              primitive := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.primitive
                · exact htail.primitive candidate hcandidate
              nonconstant := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.nonconstant
                · exact htail.nonconstant candidate hcandidate
              divides := by
                intro candidate hcandidate
                simp only [List.mem_cons] at hcandidate
                rcases hcandidate with rfl | hcandidate
                · exact hentry.divides
                · exact Hex.dvdTrans (htail.divides candidate hcandidate)
                    hnextBdiv
              pairwise := by
                apply List.Pairwise.cons
                · intro candidate hcandidate common hcommonEntry
                    hcommonCandidate
                  exact hentry.coprime_next common hcommonEntry
                    (Hex.dvdTrans hcommonCandidate
                      (htail.divides candidate hcandidate))
                · exact htail.pairwise }

private theorem yunInitialState [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hp0 : p ≠ 0) (hprimitive : Primitive p)
    (hnormalized : polyNormalize p = p)
    (hcontent : contentIn i Mono.lex p = 1) :
    let deriv := derivative i p
    let repeated := gcd p deriv
    let b := quotient p repeated
    let c := quotient deriv repeated
    let d := c - derivative i b
    YunState i 1 b d p repeated := by
  let deriv := derivative i p
  let repeated := gcd p deriv
  let b := quotient p repeated
  let c := quotient deriv repeated
  let d := c - derivative i b
  rcases gcd_quotients hp0 with ⟨hrepeated0, hb, hc, hcoprime⟩
  change repeated ≠ 0 at hrepeated0
  change b * repeated = p at hb
  change c * repeated = deriv at hc
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hp0
    rw [← hb, hzero, MvPoly.zero_mul]
  refine
    { b_ne := hb0
      residual_ne := hrepeated0
      reconstruct := ?_
      differential := ?_
      primitive := hprimitive
      normalized := hnormalized
      content_one := ?_
      coprime := ?_ }
  · rw [MvPoly.pow_succ, MvPoly.pow_zero, MvPoly.one_mul, hb]
  · change (c - derivative i b) * repeated =
      b * derivative i repeated
    calc
      (c - derivative i b) * repeated =
          c * repeated - derivative i b * repeated := by grind
      _ = deriv - derivative i b * repeated := by rw [hc]
      _ = derivative i (b * repeated) -
          derivative i b * repeated := by rw [hb]
      _ = b * derivative i repeated := by rw [derivative_mul]; grind
  · exact contentIn_one_of_dvd i hcontent (gcd_dvd_left p deriv)
  · intro e heB heExpression
    apply hcoprime e heB
    have hexpressionEq :
        (((1 : Nat) : MvPoly (m + 1) R order) * derivative i b + d) =
          c := by
      change (((1 : Nat) : MvPoly (m + 1) R order) *
        derivative i b + (c - derivative i b)) = c
      rw [Lean.Grind.Semiring.natCast_one, MvPoly.one_mul]
      grind
    rw [hexpressionEq] at heExpression
    exact heExpression

private theorem yunInitialProperties [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hp0 : p ≠ 0) (hprimitive : Primitive p)
    (hnormalized : polyNormalize p = p)
    (hcontent : contentIn i Mono.lex p = 1) :
    let deriv := derivative i p
    let repeated := gcd p deriv
    let b := quotient p repeated
    let c := quotient deriv repeated
    let d := c - derivative i b
    let factors := yunLoop i (p.totalDegree + 1) 1 b d []
    FactorProperties factors ∧
      ∀ factor ∈ factors, contentIn i Mono.lex factor.factor = 1 := by
  let deriv := derivative i p
  let repeated := gcd p deriv
  let b := quotient p repeated
  let c := quotient deriv repeated
  let d := c - derivative i b
  let factors := yunLoop i (p.totalDegree + 1) 1 b d []
  have hstate : YunState i 1 b d p repeated :=
    yunInitialState i hp0 hprimitive hnormalized hcontent
  have hyun : YunFactors b factors :=
    yunLoop_properties i (p.totalDegree + 1) 1 b d p repeated
      (by omega) hstate
  have hbP : b ∣ p := by
    have hb := (gcd_quotients (b := p) (d := deriv) hp0).2.1
    change b * repeated = p at hb
    exact ⟨repeated, by rw [MvPoly.mul_comm]; exact hb.symm⟩
  refine ⟨?_, ?_⟩
  · exact
      { squarefree := hyun.squarefree
        primitive := hyun.primitive
        nonconstant := hyun.nonconstant
        pairwise := hyun.pairwise }
  · intro factor hfactor
    apply contentIn_one_of_dvd i hcontent
    exact Hex.dvdTrans (hyun.divides factor hfactor) hbP

private theorem liftProperties
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {factors : List (SqfFactor m R lowerOrder)}
    (hprops : FactorProperties factors) :
    FactorProperties (factors.map fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }) := by
  let lift : SqfFactor m R lowerOrder → SqfFactor (m + 1) R order :=
    fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }
  have hpairwise : (factors.map lift).Pairwise fun left right =>
      CoprimePoly left.factor right.factor := by
    induction factors with
    | nil => simp
    | cons head tail ih =>
        have hsource := List.pairwise_cons.mp hprops.pairwise
        rw [List.map_cons]
        apply List.Pairwise.cons
        · intro lifted hlifted
          rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
          apply coprime_constIn i
          · exact (hprops.squarefree head (by simp)).1
          · exact hsource.1 factor hfactor
        · apply ih
          exact
            { squarefree := by
                intro factor hfactor
                exact hprops.squarefree factor (by simp [hfactor])
              primitive := by
                intro factor hfactor
                exact hprops.primitive factor (by simp [hfactor])
              nonconstant := by
                intro factor hfactor
                exact hprops.nonconstant factor (by simp [hfactor])
              pairwise := hsource.2 }
  change FactorProperties (factors.map lift)
  exact
    { squarefree := by
        intro lifted hlifted
        rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
        exact squarefree_constIn i (hprops.squarefree factor hfactor)
      primitive := by
        intro lifted hlifted
        rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
        exact primitive_constIn i (hprops.primitive factor hfactor)
      nonconstant := by
        intro lifted hlifted hconst
        rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
        exact hprops.nonconstant factor hfactor (isConst_of_constIn i hconst)
      pairwise := hpairwise }

private theorem cross_lift_main
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {lower : List (SqfFactor m R lowerOrder)}
    {main : List (SqfFactor (m + 1) R order)}
    (hlower : FactorProperties lower)
    (hmain : ∀ factor ∈ main,
      contentIn i lowerOrder factor.factor = 1) :
    CrossFactors (lower.map fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }) main := by
  intro lifted hlifted mainFactor hmainFactor
  rcases List.mem_map.mp hlifted with ⟨factor, hfactor, rfl⟩
  exact coprime_constIn_of_content_one i
    (hlower.squarefree factor hfactor).1 (hmain mainFactor hmainFactor)

private theorem yunLoop_product_initial [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] [IsMonomialOrder order]
    (i : Fin (m + 1)) {p : MvPoly (m + 1) R order}
    (hp0 : p ≠ 0) (hprimitive : Primitive p)
    (hnormalized : polyNormalize p = p)
    (hcontent : contentIn i Mono.lex p = 1) :
    let deriv := derivative i p
    let repeated := gcd p deriv
    let b := quotient p repeated
    let c := quotient deriv repeated
    let d := c - derivative i b
    sqfProduct (yunLoop i (p.totalDegree + 1) 1 b d []) = p := by
  let deriv := derivative i p
  let repeated := gcd p deriv
  let b := quotient p repeated
  let c := quotient deriv repeated
  let d := c - derivative i b
  have hstate : YunState i 1 b d p repeated :=
    yunInitialState i hp0 hprimitive hnormalized hcontent
  have hcontribution :
      yunContribution i (p.totalDegree + 1) 1 b d = p := by
    apply yunContribution_correct i p hp0
    · omega
    · exact ⟨1, (MvPoly.one_mul p).symm⟩
    · omega
    · exact hstate
  have hloop := yunLoop_product i (p.totalDegree + 1) 1 b d []
  rw [List.reverse_nil, sqfProduct_nil, MvPoly.one_mul, hcontribution] at hloop
  exact hloop

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem positive_yunLoop [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp)) (hk : 0 < k)
    (hacc : PositiveMultiplicities acc) :
    PositiveMultiplicities (yunLoop i fuel k b d acc) := by
  induction fuel generalizing k b d acc with
  | zero => simpa [yunLoop, PositiveMultiplicities] using hacc
  | succ fuel ih =>
      simp only [yunLoop]
      split
      · simpa [PositiveMultiplicities] using hacc
      · apply ih
        · omega
        · split
          · exact hacc
          · simpa [PositiveMultiplicities] using And.intro hk hacc

private def MultiplicitiesBelow (bound : Nat)
    (factors : List (SqfFactor n R cmp)) : Prop :=
  ∀ factor ∈ factors, factor.multiplicity < bound

private def ReverseSortedMultiplicities
    (factors : List (SqfFactor n R cmp)) : Prop :=
  factors.Pairwise fun left right => right.multiplicity < left.multiplicity

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem sorted_yunLoop [NatNoZero R] [IsMonomialOrder cmp]
    (i : Fin n) (fuel k : Nat) (b d : MvPoly n R cmp)
    (acc : List (SqfFactor n R cmp))
    (hbelow : MultiplicitiesBelow k acc)
    (hsorted : ReverseSortedMultiplicities acc) :
    SortedMultiplicities (yunLoop i fuel k b d acc) := by
  induction fuel generalizing k b d acc with
  | zero =>
      unfold SortedMultiplicities
      rw [yunLoop, List.pairwise_reverse]
      exact hsorted
  | succ fuel ih =>
      simp only [yunLoop]
      split
      · unfold SortedMultiplicities
        rw [List.pairwise_reverse]
        exact hsorted
      · split
        · apply ih
          · intro factor hfactor
            exact Nat.lt_trans (hbelow factor hfactor) (Nat.lt_succ_self k)
          · exact hsorted
        · apply ih
          · intro factor hfactor
            simp only [List.mem_cons] at hfactor
            rcases hfactor with rfl | hfactor
            · change k < k + 1
              omega
            · exact Nat.lt_trans (hbelow factor hfactor) (Nat.lt_succ_self k)
          · apply List.Pairwise.cons
            · exact hbelow
            · exact hsorted

/-- Move the normalization unit of the primitive part into the scalar output,
so the polynomial sent to recursive decomposition is canonically normalized
without losing the sign (or general coefficient-ring unit) in the product. -/
def sqfPrimitiveSplit [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : R × MvPoly n R cmp :=
  let scalar := content p
  let primitive := primPart p
  let unitInv := GcdOps.exactDiv 1 (GcdOps.normUnit primitive.leadingCoeff)
  (scalar * unitInv, polyNormalize primitive)

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- The scalar and normalized primitive part reconstruct the input exactly. -/
theorem sqfPrimitiveSplit_product [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    C (sqfPrimitiveSplit p).1 * (sqfPrimitiveSplit p).2 = p := by
  let scalar := content p
  let primitive := primPart p
  let unit := GcdOps.normUnit primitive.leadingCoeff
  let unitInv := GcdOps.exactDiv 1 unit
  change C (scalar * unitInv) * polyNormalize primitive = p
  by_cases hprimitive : primitive = 0
  · have hreconstruct := content_mul_primPart p
    change C scalar * primitive = p at hreconstruct
    rw [hprimitive, MvPoly.mul_zero] at hreconstruct
    rw [hprimitive, polyNormalize_zero, MvPoly.mul_zero]
    exact hreconstruct
  · cases hlead : primitive.leadingTerm with
    | none =>
        exact False.elim
          (hprimitive ((leadingTerm_eq_none_iff primitive).mp hlead))
    | some term =>
        rcases term with ⟨m, c⟩
        have hleadCoeff : primitive.leadingCoeff = c := by
          rw [leadingCoeff_eq, hlead]
          rfl
        have hunit : unit = GcdOps.normUnit c := by
          simp only [unit, hleadCoeff]
        rcases LawfulGcdOps.normUnit_unit c with ⟨inverse, hinverse⟩
        have hunitNe : GcdOps.normUnit c ≠ 0 := by
          intro hzero
          rw [hzero, Lean.Grind.Semiring.zero_mul] at hinverse
          exact LawfulGcdOps.one_ne_zero hinverse.symm
        have hinverse' : inverse * GcdOps.normUnit c = 1 := by
          rw [Lean.Grind.CommSemiring.mul_comm]
          exact hinverse
        have hexact : GcdOps.exactDiv 1 (GcdOps.normUnit c) = inverse := by
          have hcancel := LawfulGcdOps.exactDiv_cancel
            inverse (GcdOps.normUnit c) hunitNe
          rw [hinverse'] at hcancel
          exact hcancel
        have hunitInv : unitInv = inverse := by
          simp only [unitInv, hunit, hexact]
        have hpolyUnit : polyNormUnit primitive = C unit := by
          unfold polyNormUnit
          rw [hlead, hunit]
        have hconstant :
            (C unitInv : MvPoly n R cmp) * C unit = 1 := by
          change monomial Mono.zero unitInv * monomial Mono.zero unit = 1
          rw [monomial_mul_monomial, Mono.zero_mul, hunitInv, hunit,
            hinverse']
          rfl
        have hcancelPoly :
            (C unitInv : MvPoly n R cmp) * polyNormalize primitive =
              primitive := by
          rw [polyNormalize, hpolyUnit]
          calc
            C unitInv * (primitive * C unit) =
                (C unitInv * primitive) * C unit :=
              (MvPoly.mul_assoc ..).symm
            _ = (primitive * C unitInv) * C unit := by
              rw [MvPoly.mul_comm (C unitInv) primitive]
            _ = primitive * (C unitInv * C unit) :=
              MvPoly.mul_assoc ..
            _ = primitive * 1 := by rw [hconstant]
            _ = primitive := MvPoly.mul_one _
        have hscalar :
            (C (scalar * unitInv) : MvPoly n R cmp) =
              C scalar * C unitInv := by
          change monomial Mono.zero (scalar * unitInv) =
            monomial Mono.zero scalar * monomial Mono.zero unitInv
          rw [monomial_mul_monomial, Mono.zero_mul]
        calc
          C (scalar * unitInv) * polyNormalize primitive =
              (C scalar * C unitInv) * polyNormalize primitive := by
            rw [hscalar]
          _ = C scalar * (C unitInv * polyNormalize primitive) :=
            MvPoly.mul_assoc ..
          _ = C scalar * primitive := by rw [hcancelPoly]
          _ = p := content_mul_primPart p

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- The polynomial component of the primitive split is canonical. -/
theorem sqfPrimitiveSplit_normalized [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) :
    polyNormalize (sqfPrimitiveSplit p).2 = (sqfPrimitiveSplit p).2 := by
  simp only [sqfPrimitiveSplit]
  exact polyNormalize_idem _

omit [LawfulBezoutOps R] [GcdProducer R] in
/-- A nonzero polynomial component of the split remains primitive after its
normalization unit is applied. -/
theorem sqfPrimitiveSplit_primitive [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hsecond : (sqfPrimitiveSplit p).2 ≠ 0) :
    content (sqfPrimitiveSplit p).2 = 1 := by
  let primitive := primPart p
  change polyNormalize primitive ≠ 0 at hsecond
  have hprimitive : primitive ≠ 0 := by
    intro hzero
    apply hsecond
    rw [hzero, polyNormalize_zero]
  have hcontentOne : content (1 : MvPoly n R cmp) = 1 := by
    have honeUnit : GcdOps.isUnit (1 : R) = true :=
      (LawfulGcdOps.isUnit_iff 1).mpr
        ⟨1, Lean.Grind.Semiring.one_mul 1⟩
    have hnormalizeOne : normalize (1 : R) = 1 :=
      LawfulGcdOps.normalize_unit 1 honeUnit
    unfold content scalarContent
    change ((match (1 : MvPoly n R cmp).termsList with
      | [] => (0 : R)
      | (_, c) :: terms =>
          normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)) :
        R) = (1 : R)
    change ((match
      (monomial Mono.zero (1 : R) : MvPoly n R cmp).termsList with
      | [] => (0 : R)
      | (_, c) :: terms =>
          normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)) :
        R) = (1 : R)
    rw [termsList_monomial, ite_eq_right LawfulGcdOps.one_ne_zero]
    exact hnormalizeOne
  have hunitContent : content (polyNormUnit primitive) = 1 := by
    rcases (polyIsUnit_iff (polyNormUnit primitive)).mp
        (polyNormUnit_isUnit primitive) with ⟨inverse, hinverse⟩
    have hproduct := congrArg content hinverse
    rw [content_mul, hcontentOne] at hproduct
    have hbaseUnit : GcdOps.isUnit (content (polyNormUnit primitive)) = true :=
      (LawfulGcdOps.isUnit_iff _).mpr ⟨content inverse, hproduct⟩
    calc
      content (polyNormUnit primitive) =
          normalize (content (polyNormUnit primitive)) :=
        (normalize_scalarContent _).symm
      _ = 1 := LawfulGcdOps.normalize_unit _ hbaseUnit
  have hp : p ≠ 0 := by
    intro hzero
    subst p
    exact hprimitive (by simp [primitive])
  have hprimitiveContent : content primitive = 1 := by
    simpa only [primitive] using content_primPart hp
  change content (polyNormalize primitive) = 1
  rw [polyNormalize, content_mul, hprimitiveContent,
    hunitContent, Lean.Grind.Semiring.one_mul]

/-- Arity-indexed decomposition operation.  Packaging the recursive call
makes the coefficient-content descent structurally decreasing in the arity. -/
structure SqfOpsAt (R : Type u) [Zero R] (n : Nat) : Type (u + 1) where
  decomp : (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → MvPoly n R cmp → SqfDecomp n R cmp

/-- The arity-zero polynomial is a scalar, including its normalization unit. -/
def sqfBase : SqfOpsAt R 0 where
  decomp := fun _ _ p =>
    let split := sqfPrimitiveSplit p
    ⟨split.1, []⟩

/-- One recursive content split followed by Yun in a variable which occurs in
the normalized primitive part. -/
def sqfStep [NatNoZero R] {m : Nat} (lower : SqfOpsAt R m) :
    SqfOpsAt R (m + 1) where
  decomp := fun cmp _ p =>
    let split := sqfPrimitiveSplit p
    let scalar := split.1
    let q := split.2
    if q == 0 || polyIsUnit q then
      ⟨scalar, []⟩
    else
      match q.vars with
      | [] => ⟨scalar, []⟩
      | i :: _ =>
          let coefficientPart := contentIn i Mono.lex q
          let coefficientDecomp := lower.decomp Mono.lex coefficientPart
          let rawMainPart := primPartIn i Mono.lex q
          let mainSplit := sqfPrimitiveSplit rawMainPart
          let mainScalar := mainSplit.1
          let mainPart := mainSplit.2
          let deriv := derivative i mainPart
          let repeated := gcd mainPart deriv
          let b := quotient mainPart repeated
          let c := quotient deriv repeated
          let d := c - derivative i b
          let mainFactors :=
            yunLoop i (mainPart.totalDegree + 1) 1 b d []
          let liftedFactors := coefficientDecomp.factors.map fun factor =>
            { factor := constIn (cmp := cmp) i Mono.lex factor.factor
              multiplicity := factor.multiplicity }
          let factors := liftedFactors.foldl
            (fun acc factor => mergeSqfFactor factor acc) mainFactors
          ⟨scalar * coefficientDecomp.content * mainScalar, factors⟩

/-- Construct squarefree decomposition recursively in the arity. -/
def sqfOps [NatNoZero R] : (m : Nat) → SqfOpsAt R m
  | 0 => sqfBase
  | m + 1 => sqfStep (sqfOps m)

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem positive_sqfOps [NatNoZero R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    PositiveMultiplicities ((sqfOps (R := R) m).decomp order p).factors := by
  induction m with
  | zero => simp [sqfOps, sqfBase, sqfPrimitiveSplit, PositiveMultiplicities]
  | succ m ih =>
      simp only [sqfOps, sqfStep]
      split
      · simp [PositiveMultiplicities]
      · cases hvars : p.sqfPrimitiveSplit.2.vars with
        | nil => simp [PositiveMultiplicities]
        | cons i tail =>
            apply positive_merge_fold
            · have hlower := ih Mono.lex
                (contentIn i Mono.lex p.sqfPrimitiveSplit.2)
              simpa [PositiveMultiplicities] using hlower
            · apply positive_yunLoop
              · omega
              · simp [PositiveMultiplicities]

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
private theorem sorted_sqfOps [NatNoZero R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    SortedMultiplicities ((sqfOps (R := R) m).decomp order p).factors := by
  cases m with
  | zero => simp [sqfOps, sqfBase, sqfPrimitiveSplit, SortedMultiplicities]
  | succ m =>
      simp only [sqfOps, sqfStep]
      split
      · simp [SortedMultiplicities]
      · cases hvars : p.sqfPrimitiveSplit.2.vars with
        | nil => simp [SortedMultiplicities]
        | cons i tail =>
            apply sorted_merge_fold
            apply sorted_yunLoop
            · simp [MultiplicitiesBelow]
            · simp [ReverseSortedMultiplicities]

private theorem properties_sqfOps [NatNoZero R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    FactorProperties ((sqfOps (R := R) m).decomp order p).factors := by
  induction m with
  | zero =>
      simpa [sqfOps, sqfBase, sqfPrimitiveSplit] using
        (properties_nil (R := R) (cmp := order))
  | succ m ih =>
      simp only [sqfOps, sqfStep]
      split
      · exact properties_nil
      · have hq0 : (sqfPrimitiveSplit p).2 ≠ 0 := by
          intro hzero
          rename_i hterminal
          rw [hzero] at hterminal
          simp at hterminal
        cases hvars : (sqfPrimitiveSplit p).2.vars with
        | nil => exact properties_nil
        | cons i tail =>
            let q := (sqfPrimitiveSplit p).2
            let coefficientPart := contentIn i Mono.lex q
            let coefficientDecomp :=
              (sqfOps (R := R) m).decomp Mono.lex coefficientPart
            let rawMainPart := primPartIn i Mono.lex q
            let mainSplit := sqfPrimitiveSplit rawMainPart
            let mainPart := mainSplit.2
            let deriv := derivative i mainPart
            let repeated := gcd mainPart deriv
            let b := quotient mainPart repeated
            let c := quotient deriv repeated
            let d := c - derivative i b
            let mainFactors :=
              yunLoop i (mainPart.totalDegree + 1) 1 b d []
            let liftedFactors : List (SqfFactor (m + 1) R order) :=
              coefficientDecomp.factors.map fun factor =>
              { factor := constIn (cmp := order) i Mono.lex factor.factor
                multiplicity := factor.multiplicity }
            have hlower : FactorProperties coefficientDecomp.factors := by
              exact ih Mono.lex coefficientPart
            have hlifted : FactorProperties liftedFactors := by
              exact liftProperties i hlower
            have hqRestore :
                constIn i Mono.lex coefficientPart * rawMainPart = q :=
              contentIn_mul_primPartIn i Mono.lex q
            have hraw0 : rawMainPart ≠ 0 := by
              intro hzero
              apply hq0
              change q = 0
              rw [← hqRestore, hzero, MvPoly.mul_zero]
            have hmainRestore :
                (C mainSplit.1 : MvPoly (m + 1) R order) * mainPart =
                  rawMainPart := sqfPrimitiveSplit_product rawMainPart
            have hmain0 : mainPart ≠ 0 := by
              intro hzero
              apply hraw0
              rw [← hmainRestore, hzero, MvPoly.mul_zero]
            have hmainPrimitive : Primitive mainPart := by
              apply primitive_of_scalarContent_one
              exact sqfPrimitiveSplit_primitive rawMainPart hmain0
            have hmainContent : contentIn i Mono.lex mainPart = 1 := by
              have hrawContent : contentIn i Mono.lex rawMainPart = 1 :=
                primPartIn_content i Mono.lex hq0
              apply contentIn_one_of_dvd i hrawContent
              exact ⟨C mainSplit.1, hmainRestore.symm⟩
            have hmain := yunInitialProperties i hmain0 hmainPrimitive
              (sqfPrimitiveSplit_normalized rawMainPart) hmainContent
            change FactorProperties
              (liftedFactors.foldl
                (fun acc factor => mergeSqfFactor factor acc) mainFactors)
            apply properties_merge_fold liftedFactors mainFactors
            · exact hlifted
            · exact hmain.1
            · exact cross_lift_main i hlower hmain.2

private theorem split_content_of_zero [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hzero : (sqfPrimitiveSplit p).2 = 0) :
    C (sqfPrimitiveSplit p).1 = p := by
  have hrestore := sqfPrimitiveSplit_product p
  rw [hzero, MvPoly.mul_zero] at hrestore
  subst p
  simp [sqfPrimitiveSplit]
  rw [Lean.Grind.Semiring.zero_mul]
  exact C_zero

private theorem split_content_of_unit [IsMonomialOrder cmp]
    (p : MvPoly n R cmp)
    (hunit : polyIsUnit (sqfPrimitiveSplit p).2 = true) :
    C (sqfPrimitiveSplit p).1 = p := by
  have hnormalized := sqfPrimitiveSplit_normalized p
  have hone : (sqfPrimitiveSplit p).2 = 1 := by
    calc
      (sqfPrimitiveSplit p).2 =
          polyNormalize (sqfPrimitiveSplit p).2 := hnormalized.symm
      _ = 1 := polyNormalize_unit _ hunit
  have hrestore := sqfPrimitiveSplit_product p
  rw [hone, MvPoly.mul_one] at hrestore
  exact hrestore

private theorem split_content_of_const [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) (hzero : (sqfPrimitiveSplit p).2 ≠ 0)
    (hconst : IsConst (sqfPrimitiveSplit p).2) :
    C (sqfPrimitiveSplit p).1 = p := by
  have hprimitive : Primitive (sqfPrimitiveSplit p).2 := by
    apply primitive_of_scalarContent_one
    exact sqfPrimitiveSplit_primitive p hzero
  have hone := primitive_const_normalized_eq_one hprimitive hconst
    (sqfPrimitiveSplit_normalized p)
  have hrestore := sqfPrimitiveSplit_product p
  rw [hone, MvPoly.mul_one] at hrestore
  exact hrestore

private theorem product_sqfOps [NatNoZero R] (m : Nat)
    (order : Mono m → Mono m → Ordering) [IsMonomialOrder order]
    (p : MvPoly m R order) :
    C ((sqfOps (R := R) m).decomp order p).content *
        sqfProduct ((sqfOps (R := R) m).decomp order p).factors = p := by
  induction m with
  | zero =>
      simp only [sqfOps, sqfBase]
      rw [sqfProduct_nil, MvPoly.mul_one]
      by_cases hzero : (sqfPrimitiveSplit p).2 = 0
      · exact split_content_of_zero p hzero
      · apply split_content_of_const p hzero
        unfold IsConst
        apply List.eq_nil_iff_forall_not_mem.mpr
        exact fun i _ => Fin.elim0 i
  | succ m ih =>
      simp only [sqfOps, sqfStep]
      split <;> rename_i hterminal
      · rw [sqfProduct_nil, MvPoly.mul_one]
        simp only [Bool.or_eq_true, beq_iff_eq] at hterminal
        rcases hterminal with hzero | hunit
        · exact split_content_of_zero p hzero
        · exact split_content_of_unit p hunit
      · have hq0 : (sqfPrimitiveSplit p).2 ≠ 0 := by
          intro hzero
          rw [hzero] at hterminal
          simp at hterminal
        have hqunit : polyIsUnit (sqfPrimitiveSplit p).2 ≠ true := by
          intro hunit
          rw [hunit] at hterminal
          simp at hterminal
        cases hvars : (sqfPrimitiveSplit p).2.vars with
        | nil =>
            rw [sqfProduct_nil, MvPoly.mul_one]
            exact split_content_of_const p hq0 hvars
        | cons i tail =>
            let q := (sqfPrimitiveSplit p).2
            let coefficientPart := contentIn i Mono.lex q
            let coefficientDecomp :=
              (sqfOps (R := R) m).decomp Mono.lex coefficientPart
            let rawMainPart := primPartIn i Mono.lex q
            let mainSplit := sqfPrimitiveSplit rawMainPart
            let mainPart := mainSplit.2
            let deriv := derivative i mainPart
            let repeated := gcd mainPart deriv
            let b := quotient mainPart repeated
            let c := quotient deriv repeated
            let d := c - derivative i b
            let mainFactors :=
              yunLoop i (mainPart.totalDegree + 1) 1 b d []
            let liftedFactors : List (SqfFactor (m + 1) R order) :=
              coefficientDecomp.factors.map fun factor =>
              { factor := constIn (cmp := order) i Mono.lex factor.factor
                multiplicity := factor.multiplicity }
            have hlower :
                C coefficientDecomp.content *
                    sqfProduct coefficientDecomp.factors = coefficientPart := by
              exact ih Mono.lex coefficientPart
            have hembedded :
                (C coefficientDecomp.content : MvPoly (m + 1) R order) *
                    sqfProduct liftedFactors =
                  constIn i Mono.lex coefficientPart := by
              have h := congrArg
                (constIn (cmp := order) i Mono.lex) hlower
              rw [constIn_mul, constIn_C, ← sqfProduct_map_constIn] at h
              exact h
            have hqRestore :
                constIn i Mono.lex coefficientPart * rawMainPart = q :=
              contentIn_mul_primPartIn i Mono.lex q
            have hraw0 : rawMainPart ≠ 0 := by
              intro hzero
              apply hq0
              change q = 0
              rw [← hqRestore, hzero, MvPoly.mul_zero]
            have hmainRestore :
                (C mainSplit.1 : MvPoly (m + 1) R order) * mainPart =
                  rawMainPart := sqfPrimitiveSplit_product rawMainPart
            have hmain0 : mainPart ≠ 0 := by
              intro hzero
              apply hraw0
              rw [← hmainRestore, hzero, MvPoly.mul_zero]
            have hmainPrimitive : Primitive mainPart := by
              apply primitive_of_scalarContent_one
              exact sqfPrimitiveSplit_primitive rawMainPart hmain0
            have hmainContent : contentIn i Mono.lex mainPart = 1 := by
              have hrawContent : contentIn i Mono.lex rawMainPart = 1 :=
                primPartIn_content i Mono.lex hq0
              apply contentIn_one_of_dvd i hrawContent
              exact ⟨C mainSplit.1, hmainRestore.symm⟩
            have hmainProduct : sqfProduct mainFactors = mainPart := by
              exact yunLoop_product_initial i hmain0 hmainPrimitive
                (sqfPrimitiveSplit_normalized rawMainPart) hmainContent
            have hfactors :
                sqfProduct (liftedFactors.foldl
                  (fun acc factor => mergeSqfFactor factor acc) mainFactors) =
                    sqfProduct liftedFactors * sqfProduct mainFactors :=
              sqfProduct_merge_fold liftedFactors mainFactors
            have hscalar :
                (C ((sqfPrimitiveSplit p).1 *
                    coefficientDecomp.content * mainSplit.1) :
                    MvPoly (m + 1) R order) =
                  C (sqfPrimitiveSplit p).1 *
                    C coefficientDecomp.content * C mainSplit.1 := by
              rw [C_mul_C, C_mul_C]
            have hpRestore := sqfPrimitiveSplit_product p
            change C (sqfPrimitiveSplit p).1 * q = p at hpRestore
            change
              C ((sqfPrimitiveSplit p).1 * coefficientDecomp.content *
                  mainSplit.1) *
                sqfProduct (liftedFactors.foldl
                  (fun acc factor => mergeSqfFactor factor acc) mainFactors) =
                p
            rw [hfactors, hscalar]
            calc
              (C (sqfPrimitiveSplit p).1 * C coefficientDecomp.content *
                    C mainSplit.1) *
                  (sqfProduct liftedFactors * sqfProduct mainFactors) =
                  C (sqfPrimitiveSplit p).1 *
                    (C coefficientDecomp.content * sqfProduct liftedFactors) *
                    (C mainSplit.1 * sqfProduct mainFactors) := by grind
              _ = C (sqfPrimitiveSplit p).1 *
                    constIn i Mono.lex coefficientPart * rawMainPart := by
                rw [hembedded, hmainProduct, hmainRestore]
              _ = C (sqfPrimitiveSplit p).1 * q := by
                rw [MvPoly.mul_assoc, hqRestore]
              _ = p := hpRestore

/-- Characteristic-zero squarefree decomposition with recursive content and
scalar content split off. -/
def sqfDecomp [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) : SqfDecomp n R cmp :=
  (sqfOps (R := R) n).decomp cmp p

/-- Product of the distinct polynomial factors; scalar content is omitted. -/
def radical [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  let q := polyNormalize (primPart p)
  if q == 0 then 0
  else quotient q (gcdList (q :: derivatives q))

/-- Exact Boolean squarefree decision under the relative CAS convention. -/
def isSquarefree [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : Bool :=
  let q := primPart p
  polyIsUnit (gcdList (q :: derivatives q))

theorem isSquarefree_iff [IsMonomialOrder cmp]
    [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R] [PerfectFrac R]
    (p : MvPoly n R cmp) :
    isSquarefree p = true ↔ Squarefree p := by
  rcases PerfectFrac.charZeroOrPerfect (R := R) with hchar | hperfect
  · let q := primPart p
    by_cases hp : p = 0
    · subst p
      simp only [isSquarefree, primPart_zero, gcdList_derivatives_zero]
      constructor
      · intro hunit
        rcases (polyIsUnit_iff (0 : MvPoly n R cmp)).mp hunit with ⟨u, hu⟩
        rw [MvPoly.zero_mul] at hu
        exact False.elim (LawfulGcdOps.one_ne_zero hu.symm)
      · intro hsq
        exact False.elim (hsq.1 rfl)
    · have hq0 : q ≠ 0 := by
        intro hzero
        apply hp
        rw [← content_mul_primPart p]
        change C (content p) * q = 0
        rw [hzero, MvPoly.mul_zero]
      letI charZero : NatNoZero R := ⟨by
        intro m hm hzero
        apply hchar m hm
        change Hex.Fraction.ofCoeff (m : R) = 0
        rw [Hex.Fraction.ofCoeff_eq_zero_iff]
        exact hzero⟩
      have hprimitive : Primitive q := by
        apply primitive_of_scalarContent_one
        change content q = 1
        exact content_primPart hp
      change polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree p
      rw [gcdList_unit_iff_squarefree_charZero q hprimitive,
        squarefree_primPart p]
  · rcases hperfect with ⟨prime, hprime, hchar, hroot⟩
    let q := primPart p
    by_cases hp : p = 0
    · subst p
      simp only [isSquarefree, primPart_zero, gcdList_derivatives_zero]
      constructor
      · intro hunit
        rcases (polyIsUnit_iff (0 : MvPoly n R cmp)).mp hunit with ⟨u, hu⟩
        rw [MvPoly.zero_mul] at hu
        exact False.elim (LawfulGcdOps.one_ne_zero hu.symm)
      · intro hsq
        exact False.elim (hsq.1 rfl)
    · have hprimitive : Primitive q := by
        apply primitive_of_scalarContent_one
        change content q = 1
        exact content_primPart hp
      change polyIsUnit (gcdList (q :: derivatives q)) = true ↔ Squarefree p
      rw [gcdList_unit_iff_squarefree_of_kernel q hprimitive
        (fun hsq g hgq hg0 hderiv =>
          isConst_of_derivatives_zero_perfect hprime hchar hroot
            hsq hgq hg0 hderiv), squarefree_primPart p]

theorem radical_squarefree [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) (hp : p ≠ 0) : Squarefree (radical p) := by
  let q := polyNormalize (primPart p)
  have hrestore : C (sqfPrimitiveSplit p).1 * q = p :=
    sqfPrimitiveSplit_product p
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hp
    rw [← hrestore, hzero, MvPoly.mul_zero]
  let g := gcdList (q :: derivatives q)
  have hgq : g ∣ q := gcdList_dvd (List.mem_cons_self ..)
  have hg0 : g ≠ 0 := by
    intro hzero
    rcases hgq with ⟨a, ha⟩
    rw [hzero, MvPoly.mul_zero] at ha
    exact hq0 ha
  let r := quotient q g
  have hreconstruct : r * g = q := quotient_mul_of_dvd hg0 hgq
  have hr0 : r ≠ 0 := by
    intro hzero
    apply hq0
    rw [← hreconstruct, hzero, MvPoly.zero_mul]
  unfold radical
  simp only [beq_iff_eq]
  change Squarefree
    (if q = 0 then 0 else quotient q (gcdList (q :: derivatives q)))
  rw [ite_eq_right hq0]
  change Squarefree r
  refine ⟨hr0, ?_⟩
  intro d hdd
  have hdr : d ∣ r := by
    rcases hdd with ⟨a, ha⟩
    refine ⟨a * d, ?_⟩
    rw [ha]
    grind
  have hdderiv : ∀ i, d ∣ derivative i r :=
    fun i => derivative_dvd_of_square_dvd i hdd
  apply isConst_of_all_powers_dvd hg0
  exact powers_dvd_derivative_gcd rfl hreconstruct hdr hdderiv

/-- The radical divides the original input, including its scalar content
and normalization unit. -/
theorem radical_dvd [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) : radical p ∣ p := by
  let q := polyNormalize (primPart p)
  have hrestore : C (sqfPrimitiveSplit p).1 * q = p :=
    sqfPrimitiveSplit_product p
  unfold radical
  change (if q == 0 then 0 else quotient q (gcdList (q :: derivatives q))) ∣ p
  by_cases hq : q = 0
  · simp only [hq, beq_self_eq_true, ite_true, mul_zero] at hrestore ⊢
    rw [← hrestore]
    exact ⟨0, (mul_zero 0).symm⟩
  · simp only [beq_iff_eq, hq, ite_false]
    have hd : gcdList (q :: derivatives q) ∣ q :=
      gcdList_dvd (List.mem_cons_self ..)
    have hd0 : gcdList (q :: derivatives q) ≠ 0 := by
      intro hzero
      rcases hd with ⟨r, hr⟩
      rw [hzero, mul_zero] at hr
      exact hq hr
    have hquot := quotient_mul_of_dvd hd0 hd
    refine ⟨C (sqfPrimitiveSplit p).1 * gcdList (q :: derivatives q), ?_⟩
    calc
      p = C (sqfPrimitiveSplit p).1 * q := hrestore.symm
      _ = (C (sqfPrimitiveSplit p).1 * gcdList (q :: derivatives q)) *
          quotient q (gcdList (q :: derivatives q)) := by
        rw [mul_assoc (C (sqfPrimitiveSplit p).1),
          mul_comm (gcdList _) (quotient ..), hquot]

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
@[simp] theorem radical_zero [IsMonomialOrder cmp] [NatNoZero R] :
    radical (0 : MvPoly n R cmp) = 0 := by
  simp [radical]

/-- Multiplying the scalar and factor powers reconstructs the input. -/
theorem sqfDecomp_prod [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    (sqfDecomp p).factors.foldl
      (fun acc f => acc * f.factor ^ f.multiplicity)
      (C (sqfDecomp p).content) = p := by
  rw [sqfProduct_from]
  exact product_sqfOps n cmp p

/-- Every polynomial returned by square-free decomposition is square-free. -/
theorem sqfDecomp_squarefree [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, Squarefree f.factor := by
  simpa [sqfDecomp] using
    (properties_sqfOps (R := R) n cmp p).squarefree

theorem sqfDecomp_primitive [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, content f.factor = 1 := by
  intro factor hfactor
  apply content_eq_one_of_primitive
  exact (properties_sqfOps (R := R) n cmp p).primitive factor hfactor

theorem sqfDecomp_coprime [IsMonomialOrder cmp] [NatNoZero R]
    (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ∀ g ∈ (sqfDecomp p).factors,
      f.multiplicity ≠ g.multiplicity →
        ∀ d, d ∣ f.factor → d ∣ g.factor → GcdOps.isUnit d = true := by
  intro left hleft right hright hmultiplicity
  have hne : left ≠ right := by
    intro heq
    apply hmultiplicity
    exact congrArg SqfFactor.multiplicity heq
  have hcoprime := coprime_of_mem
    (properties_sqfOps (R := R) n cmp p).pairwise
    left hleft right hright hne
  exact hcoprime

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
theorem sqfDecomp_multiplicity_pos [IsMonomialOrder cmp]
    [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, 0 < f.multiplicity := by
  simpa [sqfDecomp, PositiveMultiplicities] using
    positive_sqfOps (R := R) n cmp p

omit [LawfulGcdOps R] [LawfulBezoutOps R] in
theorem sqfDecomp_multiplicity_sorted [IsMonomialOrder cmp]
    [NatNoZero R] (p : MvPoly n R cmp) :
    List.Pairwise (fun f g => f.multiplicity < g.multiplicity)
      (sqfDecomp p).factors := by
  simpa [sqfDecomp, SortedMultiplicities] using
    sorted_sqfOps (R := R) n cmp p

theorem sqfDecomp_nonconstant [IsMonomialOrder cmp]
    [NatNoZero R] (p : MvPoly n R cmp) :
    ∀ f ∈ (sqfDecomp p).factors, ¬ IsConst f.factor := by
  simpa [sqfDecomp] using
    (properties_sqfOps (R := R) n cmp p).nonconstant

end Hex.MvPoly
