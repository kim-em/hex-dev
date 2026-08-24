/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
public import HexBasic.ExactDiv
public import HexMvGcd.Coeff
public import HexMvPoly.Query

@[expose] public section
set_option backward.proofsInPublic true

/-!
Checked single-divisor reduction for distributed multivariate polynomials.

The loops use the well-founded monomial order, not an arbitrary fuel bound.
Every coefficient quotient is checked by multiplying it back before it can
affect the quotient polynomial.

The SPEC originally omitted `LawfulGcdOps R` from quotient completeness and
decidable divisibility. That assumption is necessary: a bare `GcdOps` may set
`exactDiv` to a junk operation. The executable functions and forward soundness
remain available under bare `GcdOps`; completeness and instances that consume
it require the law package.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Dvd

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]

/-- Polynomial divisibility, with the quotient on the left to agree with the
library's multiplication-facing exact-division convention. -/
instance instDvd : Dvd (MvPoly n R cmp) where
  dvd g f := ∃ q, f = q * g

end Dvd

section Divide

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R] [IsMonomialOrder cmp]

/-- The leading-monomial relation lifted with `none` as its least element.
This makes zero smaller than every nonzero running dividend. -/
def leadRel (a b : MvPoly n R cmp) : Prop :=
  Option.lt (fun x y => cmp x y = .lt) a.leadingMono b.leadingMono

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] in
theorem leadRel_wf :
    WellFounded (leadRel (n := n) (R := R) (cmp := cmp)) := by
  apply InvImage.wf (fun p : MvPoly n R cmp => p.leadingMono)
  exact Option.wellFounded_lt IsMonomialOrder.wf

local instance instDivideWf : WellFoundedRelation (MvPoly n R cmp) where
  rel := leadRel
  wf := leadRel_wf

private theorem mul_left_cancel {a b c : Mono n}
    (h : Mono.mul a b = Mono.mul a c) : b = c := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  have hj := congrArg (fun m : Mono n => m[j]) h
  simp only [Mono.getElem_mul] at hj
  exact Nat.add_left_cancel hj

omit [Std.LawfulEqCmp cmp] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] in
private theorem mul_isLE {a b c d : Mono n}
    (hab : (cmp a b).isLE) (hcd : (cmp c d).isLE) :
    (cmp (Mono.mul a c) (Mono.mul b d)).isLE := by
  have hleft : (cmp (Mono.mul a c) (Mono.mul b c)).isLE := by
    rw [← IsMonomialOrder.mul_mono (cmp := cmp) a b c]
    exact hab
  have hright : (cmp (Mono.mul b c) (Mono.mul b d)).isLE := by
    rw [Mono.mul_comm b c, Mono.mul_comm b d,
      ← IsMonomialOrder.mul_mono (cmp := cmp) c d b]
    exact hcd
  exact Std.TransCmp.isLE_trans hleft hright

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] in
private theorem left_eq_of_mul_eq {a b c d : Mono n}
    (hab : (cmp a b).isLE) (hcd : (cmp c d).isLE)
    (hmul : Mono.mul a c = Mono.mul b d) : a = b := by
  cases hcmp : cmp a b with
  | lt =>
      have hleft : cmp (Mono.mul a c) (Mono.mul b c) = .lt := by
        rw [← IsMonomialOrder.mul_mono (cmp := cmp) a b c]
        exact hcmp
      have hright : (cmp (Mono.mul b c) (Mono.mul b d)).isLE := by
        rw [Mono.mul_comm b c, Mono.mul_comm b d,
          ← IsMonomialOrder.mul_mono (cmp := cmp) c d b]
        exact hcd
      have hlt := Std.TransCmp.lt_of_lt_of_isLE hleft hright
      rw [hmul] at hlt
      have hself : cmp (Mono.mul b d) (Mono.mul b d) = .eq :=
        Std.ReflCmp.compare_self
      rw [hself] at hlt
      contradiction
  | eq => exact Std.LawfulEqCmp.eq_of_compare hcmp
  | gt => simp [hcmp] at hab

omit [DecidableEq R] [Dvd R] [GcdOps R] in
private theorem leadingTerm_monomial_mul {g : MvPoly n R cmp}
    {m mg : Mono n} {c cg : R}
    (hg : g.leadingTerm = some (mg, cg)) (hprod : c * cg ≠ 0) :
    (monomial m c * g).leadingTerm =
      some (Mono.mul m mg, c * cg) := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  have hcoeff : coeff (Mono.mul m mg) (monomial m c * g) = c * cg := by
    rw [coeff_mul]
    have hmem : (m, mg) ∈ Mono.splits (Mono.mul m mg) :=
      (Mono.splits_mem_iff ..).mpr rfl
    calc
      (Mono.splits (Mono.mul m mg)).foldl
          (fun acc ab =>
            acc + coeff ab.1 (monomial m c : MvPoly n R cmp) *
              coeff ab.2 g) 0 =
          (Mono.splits (Mono.mul m mg)).foldl
            (fun acc ab => acc + if ab = (m, mg) then c * cg else 0) 0 := by
              apply List.foldl_congr
              intro acc ab hab
              by_cases hab' : ab = (m, mg)
              · subst ab
                rw [Hex.ite_eq_left rfl, coeff_monomial,
                  Hex.ite_eq_left rfl, coeff_eq_of_leadingTerm hg]
              · rw [Hex.ite_eq_right hab']
                by_cases ham : ab.1 = m
                · have hmul := (Mono.splits_mem_iff ..).mp hab
                  have hbm : ab.2 = mg := by
                    apply mul_left_cancel (a := m)
                    calc
                      Mono.mul m ab.2 = Mono.mul ab.1 ab.2 := by rw [ham]
                      _ = Mono.mul m mg := hmul
                  exact False.elim (hab' (Prod.ext ham hbm))
                · rw [coeff_monomial, Hex.ite_eq_right ham,
                    Lean.Grind.Semiring.zero_mul]
      _ = 0 + c * cg :=
        List.foldl_add_single _ _ _ _ hmem
          (Mono.splits_nodup (Mono.mul m mg))
      _ = c * cg := by grind
  apply (leadingTerm_eq_some_iff
    (monomial m c * g) (Mono.mul m mg) (c * cg)).mpr
  constructor
  · cases hopt : (monomial m c * g).coeff? (Mono.mul m mg) with
    | none =>
        have hzero : coeff (Mono.mul m mg) (monomial m c * g) = 0 := by
          unfold coeff
          rw [hopt]
          rfl
        exact False.elim (hprod (hcoeff.symm.trans hzero))
    | some value =>
        have hvalue : value = c * cg := by
          have hlookup :
              coeff (Mono.mul m mg) (monomial m c * g) = value := by
            unfold coeff
            rw [hopt]
            rfl
          exact hlookup.symm.trans hcoeff
        exact congrArg some hvalue
  · intro k hk
    rcases exists_mul_of_mem hk with ⟨a, ha, b, hb, rfl⟩
    have ham : a = m := by
      have hacoeff := (mem_monomials_iff a
        (monomial m c : MvPoly n R cmp)).mp ha
      rw [coeff_monomial] at hacoeff
      by_cases heq : a = m
      · exact heq
      · rw [Hex.ite_eq_right heq] at hacoeff
        exact False.elim (hacoeff rfl)
    subst a
    rw [Mono.mul_comm m b, Mono.mul_comm m mg,
      ← IsMonomialOrder.mul_mono (cmp := cmp) b mg m]
    exact le_leadingTerm hg b hb

/-- The leading term of a product is the product of the leading terms over a
coefficient domain. -/
theorem leadingTerm_mul [LawfulGcdOps R]
    {p q : MvPoly n R cmp} {mp mq : Mono n} {cp cq : R}
    (hp : p.leadingTerm = some (mp, cp))
    (hq : q.leadingTerm = some (mq, cq)) :
    (p * q).leadingTerm = some (Mono.mul mp mq, cp * cq) := by
  have hpc := (leadingTerm_eq_some_iff p mp cp).mp hp |>.1
  have hqc := (leadingTerm_eq_some_iff q mq cq).mp hq |>.1
  have hcp : cp ≠ 0 := by
    intro hzero
    exact p.coeff?_ne_zero mp (hpc.trans (congrArg some hzero))
  have hcq : cq ≠ 0 := by
    intro hzero
    exact q.coeff?_ne_zero mq (hqc.trans (congrArg some hzero))
  have hprod : cp * cq ≠ 0 := by
    intro hzero
    rcases LawfulGcdOps.no_zero_div cp cq hzero with hzero | hzero
    · exact hcp hzero
    · exact hcq hzero
  have hcoeff : coeff (Mono.mul mp mq) (p * q) = cp * cq := by
    rw [coeff_mul]
    have hmem : (mp, mq) ∈ Mono.splits (Mono.mul mp mq) :=
      (Mono.splits_mem_iff ..).mpr rfl
    calc
      (Mono.splits (Mono.mul mp mq)).foldl
          (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 =
          (Mono.splits (Mono.mul mp mq)).foldl
            (fun acc ab => acc + if ab = (mp, mq) then cp * cq else 0) 0 := by
              apply List.foldl_congr
              intro acc ab hab
              by_cases hpq : ab = (mp, mq)
              · subst ab
                rw [Hex.ite_eq_left rfl, coeff_eq_of_leadingTerm hp,
                  coeff_eq_of_leadingTerm hq]
              · rw [Hex.ite_eq_right hpq]
                by_cases hpa : coeff ab.1 p = 0
                · rw [hpa, Lean.Grind.Semiring.zero_mul]
                · by_cases hqb : coeff ab.2 q = 0
                  · rw [hqb, Lean.Grind.Semiring.mul_zero]
                  · have hma : ab.1 ∈ p.monomials :=
                      (mem_monomials_iff ab.1 p).mpr hpa
                    have hmb : ab.2 ∈ q.monomials :=
                      (mem_monomials_iff ab.2 q).mpr hqb
                    have ha := le_leadingTerm hp ab.1 hma
                    have hb := le_leadingTerm hq ab.2 hmb
                    have hmul := (Mono.splits_mem_iff ..).mp hab
                    have heqa : ab.1 = mp :=
                      left_eq_of_mul_eq ha hb hmul
                    have heqb : ab.2 = mq := by
                      have hmul' : Mono.mul mp ab.2 = Mono.mul mp mq := by
                        exact (congrArg (fun a => Mono.mul a ab.2) heqa).symm.trans hmul
                      exact mul_left_cancel hmul'
                    exact False.elim (hpq (Prod.ext heqa heqb))
      _ = 0 + cp * cq :=
        List.foldl_add_single _ _ _ _ hmem
          (Mono.splits_nodup (Mono.mul mp mq))
      _ = cp * cq := by grind
  apply (leadingTerm_eq_some_iff (p * q)
    (Mono.mul mp mq) (cp * cq)).mpr
  constructor
  · cases hopt : (p * q).coeff? (Mono.mul mp mq) with
    | none =>
        have hzero : coeff (Mono.mul mp mq) (p * q) = 0 := by
          unfold coeff
          rw [hopt]
          rfl
        exact False.elim (hprod (hcoeff.symm.trans hzero))
    | some value =>
        have hvalue : value = cp * cq := by
          have hlookup : coeff (Mono.mul mp mq) (p * q) = value := by
            unfold coeff
            rw [hopt]
            rfl
          exact hlookup.symm.trans hcoeff
        exact congrArg some hvalue
  · intro m hm
    rcases exists_mul_of_mem hm with ⟨a, ha, b, hb, rfl⟩
    exact mul_isLE (le_leadingTerm hp a ha) (le_leadingTerm hq b hb)

omit [DecidableEq R] [Dvd R] [GcdOps R] in
private theorem leadRel_sub_of_cancel {r s : MvPoly n R cmp}
    {m : Mono n} {c : R} (hr : r.leadingTerm = some (m, c))
    (hs : ∀ k ∈ s.monomials, (cmp k m).isLE)
    (hc : coeff m s = c) : leadRel (r - s) r := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  unfold leadRel
  rw [leadingMono_eq, leadingMono_eq]
  rw [hr]
  cases hnext : (r - s).leadingTerm with
  | none => exact True.intro
  | some next =>
      rcases next with ⟨k, d⟩
      change cmp k m = .lt
      have hk : k ∈ (r - s).monomials := by
        apply (mem_monomials_iff k (r - s)).mpr
        intro hzero
        have hd := coeff_eq_of_leadingTerm hnext
        rw [hzero] at hd
        have hdne : d ≠ 0 := by
          have hlookup := (leadingTerm_eq_some_iff (r - s) k d).mp hnext |>.1
          intro hdzero
          exact (r - s).coeff?_ne_zero k
            (hlookup.trans (congrArg some hdzero))
        exact hdne hd.symm
      have hle : (cmp k m).isLE := by
        by_cases hkr : k ∈ r.monomials
        · exact le_leadingTerm hr k hkr
        · apply hs k
          apply (mem_monomials_iff k s).mpr
          intro hks
          have hzero : coeff k (r - s) = 0 := by
            rw [coeff_sub, coeff_eq_zero_of_not_mem k r hkr, hks]
            exact Lean.Grind.AddCommGroup.sub_self 0
          exact ((mem_monomials_iff k (r - s)).mp hk) hzero
      cases hcmp : cmp k m with
      | lt => rfl
      | eq =>
          have hkm : k = m := Std.LawfulEqCmp.eq_of_compare hcmp
          subst k
          have hzero : coeff m (r - s) = 0 := by
            rw [coeff_sub, coeff_eq_of_leadingTerm hr, hc]
            exact Lean.Grind.AddCommGroup.sub_self c
          exact False.elim (((mem_monomials_iff m (r - s)).mp hk) hzero)
      | gt => simp [hcmp] at hle

omit [DecidableEq R] [Dvd R] [GcdOps R] in
private theorem leadRel_moveLeading {r : MvPoly n R cmp}
    {m : Mono n} {c : R} (hr : r.leadingTerm = some (m, c)) :
    leadRel (r - monomial m c) r := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  apply leadRel_sub_of_cancel hr
  · intro k hk
    have hkcoeff := (mem_monomials_iff k
      (monomial m c : MvPoly n R cmp)).mp hk
    rw [coeff_monomial] at hkcoeff
    have hkm : k = m := by
      by_cases heq : k = m
      · exact heq
      · rw [Hex.ite_eq_right heq] at hkcoeff
        exact False.elim (hkcoeff rfl)
    subst k
    simp only [Std.ReflCmp.compare_self, Ordering.isLE]
  · rw [coeff_monomial]
    simp

omit [DecidableEq R] [Dvd R] [GcdOps R] in
private theorem leadRel_reduce {g r : MvPoly n R cmp}
    {mr mg mq : Mono n} {cr cg cq : R}
    (hr : r.leadingTerm = some (mr, cr))
    (hg : g.leadingTerm = some (mg, cg))
    (hmq : Mono.div mg mr = some mq) (hcq : cq * cg = cr) :
    leadRel (r - monomial mq cq * g) r := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  have hmono : Mono.mul mq mg = mr := by
    rw [Mono.mul_comm]
    exact (Mono.div_eq_some_iff mg mr mq).mp hmq
  have hcr : cr ≠ 0 := by
    have hlookup := (leadingTerm_eq_some_iff r mr cr).mp hr |>.1
    intro hzero
    exact r.coeff?_ne_zero mr (hlookup.trans (congrArg some hzero))
  have hprod : cq * cg ≠ 0 := by
    intro hzero
    apply hcr
    rw [← hcq]
    exact hzero
  have hlead := leadingTerm_monomial_mul (m := mq) hg hprod
  rw [hmono, hcq] at hlead
  exact leadRel_sub_of_cancel hr (le_leadingTerm hlead)
    (coeff_eq_of_leadingTerm hlead)

/-- Move the leading term of `r` into the accumulated remainder. -/
def moveLeading (r s : MvPoly n R cmp) (m : Mono n) (c : R) :
    MvPoly n R cmp × MvPoly n R cmp :=
  let t := monomial m c
  (r - t, s + t)

/-- The well-founded division-with-remainder loop. -/
def divModAux (g q r s : MvPoly n R cmp) :
    MvPoly n R cmp × MvPoly n R cmp :=
  match _hr : r.leadingTerm with
  | none => (q, s)
  | some (mr, cr) =>
      match _hg : g.leadingTerm with
      | none => (q, s + r)
      | some (mg, cg) =>
          match hmq : Mono.div mg mr with
          | none =>
              let next := moveLeading r s mr cr
              divModAux g q next.1 next.2
          | some mq =>
              let cq := GcdOps.exactDiv cr cg
              if cq * cg = cr then
                let t := monomial mq cq
                divModAux g (q + t) (r - t * g) s
              else
                let next := moveLeading r s mr cr
                divModAux g q next.1 next.2
termination_by r
decreasing_by
  all_goals simp_wf
  · simpa [moveLeading] using leadRel_moveLeading _hr
  · simpa [cq, t] using leadRel_reduce _hr _hg hmq ‹cq * cg = cr›
  · simpa [moveLeading] using leadRel_moveLeading _hr

/-- Division with remainder against one divisor. The zero-divisor branch is
fixed as `(0, f)`. -/
def divMod (f g : MvPoly n R cmp) : MvPoly n R cmp × MvPoly n R cmp :=
  if g = 0 then (0, f) else divModAux g 0 f 0

/-- The fail-fast exact-division loop. Unlike `divModAux`, a term that cannot
be cancelled immediately rejects the candidate. -/
def divExactAux (g q r : MvPoly n R cmp) : Option (MvPoly n R cmp) :=
  match _hr : r.leadingTerm with
  | none => some q
  | some (mr, cr) =>
      match _hg : g.leadingTerm with
      | none => none
      | some (mg, cg) =>
          match hmq : Mono.div mg mr with
          | none => none
          | some mq =>
              let cq := GcdOps.exactDiv cr cg
              if cq * cg = cr then
                let t := monomial mq cq
                divExactAux g (q + t) (r - t * g)
              else
                none
termination_by r
decreasing_by
  simp_wf
  simpa [cq, t] using leadRel_reduce _hr _hg hmq ‹cq * cg = cr›

/-- Exact quotient, rejecting a zero divisor before entering the fail-fast
reduction loop. -/
def divExact? (f g : MvPoly n R cmp) : Option (MvPoly n R cmp) :=
  if g = 0 then
    none
  else if f = 0 then
    some 0
  else
    divExactAux g 0 f

/-- No term of `r` is cancellable by the leading term of `g`. -/
def ReducedBy (r g : MvPoly n R cmp) : Prop :=
  ∀ m ∈ r.monomials,
    match g.leadingTerm with
    | none => True
    | some (mg, cg) =>
        match Mono.div mg m with
        | none => True
        | some _ => GcdOps.exactDiv (coeff m r) cg * cg ≠ coeff m r

/-- The running dividend is strictly below every term already accumulated in
the remainder. -/
private def Above (r s : MvPoly n R cmp) : Prop :=
  ∀ {m c}, r.leadingTerm = some (m, c) →
    ∀ k ∈ s.monomials, cmp m k = .lt

omit [Dvd R] [GcdOps R] [IsMonomialOrder cmp] in
private theorem mem_monomials_add {p q : MvPoly n R cmp} {m : Mono n}
    (h : m ∈ (p + q).monomials) :
    m ∈ p.monomials ∨ m ∈ q.monomials := by
  by_cases hp : m ∈ p.monomials
  · exact Or.inl hp
  · by_cases hq : m ∈ q.monomials
    · exact Or.inr hq
    · have hzero : coeff m (p + q) = 0 := by
        rw [coeff_add, coeff_eq_zero_of_not_mem m p hp,
          coeff_eq_zero_of_not_mem m q hq]
        exact Lean.Grind.AddCommMonoid.zero_add 0
      exact False.elim (((mem_monomials_iff m (p + q)).mp h) hzero)

omit [Dvd R] in
private theorem reduced_add_monomial {g s : MvPoly n R cmp}
    {m : Mono n} {c : R} (hs : ReducedBy s g) (hsm : coeff m s = 0)
    (hterm :
      match g.leadingTerm with
      | none => True
      | some (mg, cg) =>
          match Mono.div mg m with
          | none => True
          | some _ => GcdOps.exactDiv c cg * cg ≠ c) :
    ReducedBy (s + monomial m c) g := by
  intro k hk
  by_cases hkm : k = m
  · subst k
    have hcoeff : coeff m (s + monomial m c) = c := by
      rw [coeff_add, hsm, coeff_monomial]
      rw [Hex.ite_eq_left rfl]
      exact Lean.Grind.AddCommMonoid.zero_add c
    simpa only [hcoeff] using hterm
  · have hks : k ∈ s.monomials := by
      rcases mem_monomials_add hk with hks | hkmono
      · exact hks
      · have hkcoeff := (mem_monomials_iff k
          (monomial m c : MvPoly n R cmp)).mp hkmono
        rw [coeff_monomial, Hex.ite_eq_right hkm] at hkcoeff
        exact False.elim (hkcoeff rfl)
    have hcoeff : coeff k (s + monomial m c) = coeff k s := by
      rw [coeff_add, coeff_monomial, Hex.ite_eq_right hkm,
        Lean.Grind.AddCommMonoid.add_zero]
    simpa only [hcoeff] using hs k hks

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] in
private theorem above_of_leadRel {r r' s : MvPoly n R cmp}
    (hrel : leadRel r' r) (hs : Above r s) : Above r' s := by
  intro m' c' hr' k hk
  cases hr : r.leadingTerm with
  | none =>
      unfold leadRel at hrel
      rw [leadingMono_eq, leadingMono_eq, hr', hr] at hrel
      exact False.elim hrel
  | some term =>
      rcases term with ⟨m, c⟩
      have hm'm : cmp m' m = .lt := by
        unfold leadRel at hrel
        rw [leadingMono_eq, leadingMono_eq, hr', hr] at hrel
        exact hrel
      exact Std.TransCmp.lt_trans hm'm (hs hr k hk)

omit [DecidableEq R] [Dvd R] [GcdOps R] in
private theorem above_add_monomial {r r' s : MvPoly n R cmp}
    {m : Mono n} {c : R} (hr : r.leadingTerm = some (m, c))
    (hrel : leadRel r' r) (hs : Above r s) :
    Above r' (s + monomial m c) := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  have hs' : Above r' s := above_of_leadRel hrel hs
  intro m' c' hr' k hk
  rcases mem_monomials_add hk with hks | hkmono
  · exact hs' hr' k hks
  · have hkcoeff := (mem_monomials_iff k
      (monomial m c : MvPoly n R cmp)).mp hkmono
    rw [coeff_monomial] at hkcoeff
    have hkm : k = m := by
      by_cases heq : k = m
      · exact heq
      · rw [Hex.ite_eq_right heq] at hkcoeff
        exact False.elim (hkcoeff rfl)
    subst k
    unfold leadRel at hrel
    rw [leadingMono_eq, leadingMono_eq, hr', hr] at hrel
    exact hrel

omit [Dvd R] in
private theorem divModAux_spec (g q r s : MvPoly n R cmp) :
    q * g + r + s =
      (divModAux g q r s).1 * g + (divModAux g q r s).2 := by
  revert q s
  refine leadRel_wf.induction
    (C := fun r => ∀ q s : MvPoly n R cmp,
      q * g + r + s =
        (divModAux g q r s).1 * g + (divModAux g q r s).2) r ?_
  intro r ih q s
  rw [divModAux]
  split
  next hr =>
    have hrzero := (leadingTerm_eq_none_iff r).mp hr
    subst r
    simp only [Lean.Grind.AddCommMonoid.add_zero]
  next mr cr hr =>
    split
    next hg =>
      have hgzero := (leadingTerm_eq_none_iff g).mp hg
      subst g
      simp only [Lean.Grind.Semiring.mul_zero,
        Lean.Grind.AddCommMonoid.zero_add]
      exact Lean.Grind.AddCommMonoid.add_comm r s
    next mg cg hg =>
      split
      next hmq =>
        dsimp [moveLeading]
        rw [← ih (r - monomial mr cr) (leadRel_moveLeading hr)
          q (s + monomial mr cr)]
        grind
      next mq hmq =>
        dsimp only
        split
        next hcheck =>
          rw [← ih (r - monomial mq (GcdOps.exactDiv cr cg) * g)
            (leadRel_reduce hr hg hmq hcheck)
            (q + monomial mq (GcdOps.exactDiv cr cg)) s]
          grind
        next hcheck =>
          dsimp [moveLeading]
          rw [← ih (r - monomial mr cr) (leadRel_moveLeading hr)
            q (s + monomial mr cr)]
          grind

omit [Dvd R] in
private theorem divModAux_reduced (g q r s : MvPoly n R cmp)
    (hgzero : g ≠ 0) (hs : ReducedBy s g) (hrs : Above r s) :
    ReducedBy (divModAux g q r s).2 g := by
  revert q s
  refine leadRel_wf.induction
    (C := fun r => ∀ q s : MvPoly n R cmp,
      ReducedBy s g → Above r s →
        ReducedBy (divModAux g q r s).2 g) r ?_
  intro r ih q s hs hrs
  rw [divModAux]
  split
  next hr => exact hs
  next mr cr hr =>
    split
    next hg =>
      exact False.elim (hgzero ((leadingTerm_eq_none_iff g).mp hg))
    next mg cg hg =>
      split
      next hmq =>
        have hmnot : mr ∉ s.monomials := by
          intro hm
          have hlt := hrs hr mr hm
          have hself : cmp mr mr = .eq := Std.ReflCmp.compare_self
          rw [hself] at hlt
          contradiction
        have hs' : ReducedBy (s + monomial mr cr) g := by
          apply reduced_add_monomial hs
            (coeff_eq_zero_of_not_mem mr s hmnot)
          rw [hg]
          simp only
          rw [hmq]
          trivial
        have hrel := leadRel_moveLeading hr
        dsimp [moveLeading]
        exact ih (r - monomial mr cr) hrel q
          (s + monomial mr cr) hs'
          (above_add_monomial hr hrel hrs)
      next mq hmq =>
        dsimp only
        split
        next hcheck =>
          have hrel := leadRel_reduce hr hg hmq hcheck
          exact ih (r - monomial mq (GcdOps.exactDiv cr cg) * g) hrel
            (q + monomial mq (GcdOps.exactDiv cr cg)) s hs
            (above_of_leadRel hrel hrs)
        next hcheck =>
          have hmnot : mr ∉ s.monomials := by
            intro hm
            have hlt := hrs hr mr hm
            have hself : cmp mr mr = .eq := Std.ReflCmp.compare_self
            rw [hself] at hlt
            contradiction
          have hs' : ReducedBy (s + monomial mr cr) g := by
            apply reduced_add_monomial hs
              (coeff_eq_zero_of_not_mem mr s hmnot)
            rw [hg]
            simp only
            rw [hmq]
            exact hcheck
          have hrel := leadRel_moveLeading hr
          dsimp [moveLeading]
          exact ih (r - monomial mr cr) hrel q
            (s + monomial mr cr) hs'
            (above_add_monomial hr hrel hrs)

omit [Dvd R] in
/-- Division with remainder reconstructs its dividend. -/
theorem divMod_spec (f g : MvPoly n R cmp) :
    f = (divMod f g).1 * g + (divMod f g).2 := by
  unfold divMod
  split
  next hg =>
    subst g
    simp only [Lean.Grind.Semiring.zero_mul,
      Lean.Grind.AddCommMonoid.zero_add]
  next hg =>
    simpa only [Lean.Grind.Semiring.zero_mul,
      Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommMonoid.add_zero] using divModAux_spec g 0 f 0

omit [Dvd R] in
/-- The returned remainder has no term reducible by the divisor's leading
term. -/
theorem divMod_reduced {f g : MvPoly n R cmp} (hg : g ≠ 0) :
    ReducedBy (divMod f g).2 g := by
  unfold divMod
  rw [Hex.ite_eq_right hg]
  apply divModAux_reduced g 0 f 0 hg
  · intro m hm
    have hmne := (mem_monomials_iff m (0 : MvPoly n R cmp)).mp hm
    exact False.elim (hmne (coeff_zero m))
  · intro m c hm k hk
    have hkne := (mem_monomials_iff k (0 : MvPoly n R cmp)).mp hk
    exact False.elim (hkne (coeff_zero k))

omit [Dvd R] in
/-- Exact division rejects a zero right argument. -/
@[simp] theorem divExact?_zero_right (f : MvPoly n R cmp) :
    divExact? f 0 = none := by
  simp [divExact?]

omit [Dvd R] in
private theorem divExactAux_spec (g q r out : MvPoly n R cmp)
    (hout : divExactAux g q r = some out) :
    q * g + r = out * g := by
  revert q out
  refine leadRel_wf.induction
    (C := fun r => ∀ q out : MvPoly n R cmp,
      divExactAux g q r = some out → q * g + r = out * g) r ?_
  intro r ih q out hout
  rw [divExactAux] at hout
  split at hout
  next hr =>
    have hrzero := (leadingTerm_eq_none_iff r).mp hr
    simp only [Option.some.injEq] at hout
    subst r
    subst out
    exact Lean.Grind.AddCommMonoid.add_zero (q * g)
  next mr cr hr =>
    split at hout
    next hg => contradiction
    next mg cg hg =>
      split at hout
      next hmq => contradiction
      next mq hmq =>
        dsimp only at hout
        split at hout
        next hcheck =>
          have hrec := ih
            (r - monomial mq (GcdOps.exactDiv cr cg) * g)
            (leadRel_reduce hr hg hmq hcheck)
            (q + monomial mq (GcdOps.exactDiv cr cg)) out hout
          grind
        next hcheck => contradiction

omit [Dvd R] in
/-- Every quotient returned by the checked loop reconstructs the dividend.
This direction needs no laws for `GcdOps` because each scalar quotient was
validated by multiplication. -/
theorem eq_mul_of_divExact?_eq_some {f g q : MvPoly n R cmp}
    (h : divExact? f g = some q) : f = q * g := by
  unfold divExact? at h
  split at h
  next hg => contradiction
  next hg =>
    split at h
    next hf =>
      simp only [Option.some.injEq] at h
      subst f
      subst q
      exact (Lean.Grind.Semiring.zero_mul g).symm
    next hf =>
      simpa only [Lean.Grind.Semiring.zero_mul,
        Lean.Grind.AddCommMonoid.zero_add] using
          divExactAux_spec g 0 f q h

private theorem divExactAux_mul [LawfulGcdOps R]
    (g q acc : MvPoly n R cmp) (hgzero : g ≠ 0) :
    divExactAux g acc (q * g) = some (acc + q) := by
  revert acc
  refine leadRel_wf.induction
    (C := fun q => ∀ acc : MvPoly n R cmp,
      divExactAux g acc (q * g) = some (acc + q)) q ?_
  intro q ih acc
  cases hq : q.leadingTerm with
  | none =>
      have hqzero := (leadingTerm_eq_none_iff q).mp hq
      subst q
      rw [Lean.Grind.Semiring.zero_mul, divExactAux]
      have hzero : (0 : MvPoly n R cmp).leadingTerm = none :=
        (leadingTerm_eq_none_iff 0).mpr rfl
      rw [hzero]
      exact congrArg some (Lean.Grind.AddCommMonoid.add_zero acc).symm
  | some term =>
      rcases term with ⟨mq, cq⟩
      cases hg : g.leadingTerm with
      | none =>
          exact False.elim (hgzero ((leadingTerm_eq_none_iff g).mp hg))
      | some term =>
          rcases term with ⟨mg, cg⟩
          have hlead := leadingTerm_mul hq hg
          rw [divExactAux, hlead]
          simp only
          rw [hg]
          simp only
          have hdiv : Mono.div mg (Mono.mul mq mg) = some mq := by
            apply (Mono.div_eq_some_iff mg (Mono.mul mq mg) mq).mpr
            exact Mono.mul_comm mg mq
          rw [hdiv]
          simp only
          have hcg : cg ≠ 0 := by
            have hlookup := (leadingTerm_eq_some_iff g mg cg).mp hg |>.1
            intro hzero
            exact g.coeff?_ne_zero mg
              (hlookup.trans (congrArg some hzero))
          rw [LawfulGcdOps.exactDiv_cancel cq cg hcg,
            Hex.ite_eq_left rfl]
          have hpoly :
              q * g - monomial mq cq * g =
                (q - monomial mq cq) * g := by
            grind
          rw [hpoly, ih (q - monomial mq cq)
            (leadRel_moveLeading hq) (acc + monomial mq cq)]
          congr 1
          grind

private theorem mul_ne_zero [LawfulGcdOps R]
    {p q : MvPoly n R cmp} (hpzero : p ≠ 0) (hqzero : q ≠ 0) :
    p * q ≠ 0 := by
  intro hzero
  cases hp : p.leadingTerm with
  | none => exact hpzero ((leadingTerm_eq_none_iff p).mp hp)
  | some pterm =>
      rcases pterm with ⟨mp, cp⟩
      cases hq : q.leadingTerm with
      | none => exact hqzero ((leadingTerm_eq_none_iff q).mp hq)
      | some qterm =>
          rcases qterm with ⟨mq, cq⟩
          have hlead := leadingTerm_mul hp hq
          rw [hzero, leadingTerm_zero] at hlead
          contradiction

/-- Under lawful coefficient division, the checked exact quotient is complete
as well as sound. -/
theorem divExact?_eq [LawfulGcdOps R] {f g q : MvPoly n R cmp}
    (hg : g ≠ 0) : divExact? f g = some q ↔ f = q * g := by
  constructor
  · exact eq_mul_of_divExact?_eq_some
  · intro hf
    subst f
    by_cases hq : q = 0
    · subst q
      rw [Lean.Grind.Semiring.zero_mul]
      simp [divExact?, hg]
    · have hprod : q * g ≠ 0 := mul_ne_zero hq hg
      unfold divExact?
      rw [Hex.ite_eq_right hg, Hex.ite_eq_right hprod]
      simpa only [Lean.Grind.AddCommMonoid.zero_add] using
        divExactAux_mul g q 0 hg

/-- A known nonzero divisor makes the exact-division loop succeed. -/
theorem divExact?_isSome_of_dvd [LawfulGcdOps R] {f g : MvPoly n R cmp}
    (hg : g ≠ 0) : g ∣ f → (divExact? f g).isSome := by
  rintro ⟨q, rfl⟩
  rw [(divExact?_eq hg).mpr rfl]
  rfl

/-- Decidable polynomial divisibility. The zero divisor is decided by equality;
the nonzero branch uses checked exact division. -/
instance instDecidableDvd [LawfulGcdOps R] (g f : MvPoly n R cmp) :
    Decidable (g ∣ f) :=
  if hg : g = 0 then
    if hf : f = 0 then
      isTrue (by
        subst g
        subst f
        exact ⟨0, by rw [Lean.Grind.Semiring.zero_mul]⟩)
    else
      isFalse (by
        rintro ⟨q, hq⟩
        rw [hg, Lean.Grind.Semiring.mul_zero] at hq
        exact hf hq)
  else
    match hq : divExact? f g with
    | some q =>
        isTrue ⟨q, (divExact?_eq hg).mp hq⟩
    | none =>
        isFalse fun hd => by
          have hs := divExact?_isSome_of_dvd hg hd
          simp [hq] at hs

/-- Total exact division. Its zero and inexact branches use the stable junk
value zero. -/
instance instDiv : Div (MvPoly n R cmp) where
  div f g := (divExact? f g).getD 0

/-- Total multivariate division cancels every known nonzero exact right
factor. -/
instance instExactDivLaws [LawfulGcdOps R] : ExactDivLaws (MvPoly n R cmp) where
  mul_div_cancel_right := by
    intro a b hb
    change (divExact? (a * b) b).getD 0 = a
    have hq : divExact? (a * b) b = some a :=
      (divExact?_eq hb).mpr rfl
    simp [hq]

end Divide

end Hex.MvPoly
