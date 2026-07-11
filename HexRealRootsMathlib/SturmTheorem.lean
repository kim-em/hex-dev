/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.SturmChainDefs

public section

/-!
Sturm's theorem over `Polynomial ℝ`, stated as the five-step chain of the
SPEC. Everything here is a slice over `Polynomial ℝ` with no `HexRealRoots`
dependence.

The three local lemmas (`sturmVar_const_of_no_zero`, `sturmVar_interior_cross`,
`sturmVar_root_cross`) describe the behaviour of `Sturm.sturmVar` across the
finitely many zeros of the chain elements. The two global results
(`sturm_half_open`, `sturm_line`) are the telescoping consequences: the number
of real roots of `p` in a half-open interval `(a, b]` is the drop in
`sturmVar` from `a` to `b`, and the total number of real roots is the drop
from `−∞` to `+∞`.

The theorem bodies are `sorry` in this scaffold PR; each carries the intended
proof sketch from the SPEC. They are discharged by the follow-up PRs M2–M5.
The `±∞` variation counts `Sturm.sturmVarNegInf` / `Sturm.sturmVarPosInf` are
defined here as real definitions (no `sorry`), reading the sign of each chain
element at infinity off its leading coefficient and degree parity.
-/

open Filter Topology

namespace Sturm

/-- Sign variations of the chain at `+∞`: the sign of each element there is the
sign of its leading coefficient, so this is the zero-skipping variation count
of the leading coefficients. The zero polynomial contributes leading
coefficient `0`, which the zero-skipping convention drops. -/
@[expose]
noncomputable def sturmVarPosInf (chain : List (Polynomial ℝ)) : ℕ :=
  signVariations (chain.map Polynomial.leadingCoeff)

/-- Sign variations of the chain at `−∞`: the sign of an element there is the
sign of its leading coefficient times `(-1) ^ degree`, so this is the
zero-skipping variation count of `leadingCoeff · (-1) ^ natDegree`. -/
@[expose]
noncomputable def sturmVarNegInf (chain : List (Polynomial ℝ)) : ℕ :=
  signVariations (chain.map (fun q => q.leadingCoeff * (-1) ^ q.natDegree))

/-- **Sign persistence.** A polynomial with no zero on `[a, b]` keeps a constant
sign there: its evaluation signs at the two endpoints agree. If they differed,
the two endpoint values would straddle `0` and the intermediate value theorem
would supply an interior zero. -/
theorem eval_sign_eq_of_no_zero {q : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hz : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    SignType.sign (q.eval a) = SignType.sign (q.eval b) := by
  have hna : q.eval a ≠ 0 := hz a ⟨le_refl a, hab⟩
  have hnb : q.eval b ≠ 0 := hz b ⟨hab, le_refl b⟩
  have hpos : 0 < q.eval a * q.eval b := by
    rcases lt_or_gt_of_ne (mul_ne_zero hna hnb) with hlt | hgt
    · exfalso
      have hmem : (0 : ℝ) ∈ Set.uIcc (q.eval a) (q.eval b) := by
        rcases mul_neg_iff.mp hlt with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Set.mem_uIcc.mpr (Or.inr ⟨hy.le, hx.le⟩)
        · exact Set.mem_uIcc.mpr (Or.inl ⟨hx.le, hy.le⟩)
      have hsub := intermediate_value_uIcc (a := a) (b := b)
        (f := fun x => q.eval x) q.continuousOn
      obtain ⟨c, hc, hc0⟩ := hsub hmem
      rw [Set.uIcc_of_le hab] at hc
      exact hz c hc hc0
    · exact hgt
  rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sign_pos h1, sign_pos h2]
  · rw [sign_neg h1, sign_neg h2]

/-- Build the sign-pattern relation `SVRel` between the evaluations of a
polynomial list at a "generic" point `a` (where every element is nonzero) and a
"special" point `r` (where some interior elements may vanish). The hypotheses
are exactly what an `IsSturmChain` supplies restricted to the relevant interval:
every element is nonzero at `a`; the head and last elements are nonzero at `r`;
whenever an interior element vanishes at `r` its neighbours are nonzero there
with opposite signs; and every element nonzero at `r` has the same sign at `a`
and `r`. -/
private theorem buildSVRel (a r : ℝ) :
    ∀ (cs : List (Polynomial ℝ)),
      (∀ q ∈ cs, q.eval a ≠ 0) →
      (∀ q, cs.head? = some q → q.eval r ≠ 0) →
      (∀ q, cs.getLast? = some q → q.eval r ≠ 0) →
      (∀ (i : ℕ) (q0 q1 q2 : Polynomial ℝ), cs[i]? = some q0 → cs[i + 1]? = some q1 →
        cs[i + 2]? = some q2 → q1.eval r = 0 →
        q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0) →
      (∀ q ∈ cs, q.eval r ≠ 0 → SignType.sign (q.eval a) = SignType.sign (q.eval r)) →
      SVRel (cs.map (Polynomial.eval a)) (cs.map (Polynomial.eval r))
  | [], _, _, _, _, _ => SVRel.nil
  | [q0], hne0, hfront, _, _, hsame => by
      have hr : q0.eval r ≠ 0 := hfront q0 rfl
      exact SVRel.same (hne0 q0 (by simp)) hr (hsame q0 (by simp) hr) SVRel.nil
  | q0 :: q1 :: rest, hne0, hfront, hlast, halt, hsame => by
      have hr0 : q0.eval r ≠ 0 := hfront q0 rfl
      have ha0 : q0.eval a ≠ 0 := hne0 q0 (by simp)
      by_cases hq1 : q1.eval r = 0
      · cases rest with
        | nil => exact absurd hq1 (hlast q1 (by simp))
        | cons q2 rest' =>
            obtain ⟨hn0, hn2, hoppR⟩ := halt 0 q0 q1 q2 rfl rfl rfl hq1
            have hsx : SignType.sign (q0.eval a) = SignType.sign (q0.eval r) :=
              hsame q0 (by simp) hn0
            have hsy : SignType.sign (q2.eval a) = SignType.sign (q2.eval r) :=
              hsame q2 (by simp) hn2
            have hoppA : SignType.sign (q0.eval a) * SignType.sign (q2.eval a) = -1 := by
              rw [hsx, hsy, ← sign_mul, sign_eq_neg_one_iff]; exact hoppR
            have hne0' : ∀ q ∈ q2 :: rest', q.eval a ≠ 0 := fun q hq =>
              hne0 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
            have hfront' : ∀ q, (q2 :: rest').head? = some q → q.eval r ≠ 0 := by
              intro q hq; rw [List.head?_cons] at hq; cases hq; exact hn2
            have hlast' : ∀ q, (q2 :: rest').getLast? = some q → q.eval r ≠ 0 := by
              intro q hq
              exact hlast q (by rw [List.getLast?_cons_cons, List.getLast?_cons_cons]; exact hq)
            have halt' : ∀ (i : ℕ) (p0 p1 p2 : Polynomial ℝ), (q2 :: rest')[i]? = some p0 →
                (q2 :: rest')[i + 1]? = some p1 → (q2 :: rest')[i + 2]? = some p2 →
                p1.eval r = 0 → p0.eval r ≠ 0 ∧ p2.eval r ≠ 0 ∧ p0.eval r * p2.eval r < 0 := by
              intro i p0 p1 p2 h0 h1 h2 hz
              exact halt (i + 2) p0 p1 p2
                (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h0)
                (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h1)
                (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h2) hz
            have hsame' : ∀ q ∈ q2 :: rest', q.eval r ≠ 0 →
                SignType.sign (q.eval a) = SignType.sign (q.eval r) := fun q hq =>
              hsame q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
            have IH := buildSVRel a r (q2 :: rest') hne0' hfront' hlast' halt' hsame'
            simp only [List.map_cons] at IH ⊢
            rw [hq1]
            exact SVRel.collapse ha0 (hne0 q1 (by simp)) hn2 hsx hsy hoppA IH
      · have hne0' : ∀ q ∈ q1 :: rest, q.eval a ≠ 0 := fun q hq =>
          hne0 q (List.mem_cons_of_mem _ hq)
        have hfront' : ∀ q, (q1 :: rest).head? = some q → q.eval r ≠ 0 := by
          intro q hq; rw [List.head?_cons] at hq; cases hq; exact hq1
        have hlast' : ∀ q, (q1 :: rest).getLast? = some q → q.eval r ≠ 0 := by
          intro q hq
          exact hlast q (by rw [List.getLast?_cons_cons]; exact hq)
        have halt' : ∀ (i : ℕ) (p0 p1 p2 : Polynomial ℝ), (q1 :: rest)[i]? = some p0 →
            (q1 :: rest)[i + 1]? = some p1 → (q1 :: rest)[i + 2]? = some p2 →
            p1.eval r = 0 → p0.eval r ≠ 0 ∧ p2.eval r ≠ 0 ∧ p0.eval r * p2.eval r < 0 := by
          intro i p0 p1 p2 h0 h1 h2 hz
          exact halt (i + 1) p0 p1 p2
            (by rw [List.getElem?_cons_succ]; exact h0)
            (by rw [List.getElem?_cons_succ]; exact h1)
            (by rw [List.getElem?_cons_succ]; exact h2) hz
        have hsame' : ∀ q ∈ q1 :: rest, q.eval r ≠ 0 →
            SignType.sign (q.eval a) = SignType.sign (q.eval r) := fun q hq =>
          hsame q (List.mem_cons_of_mem _ hq)
        have IH := buildSVRel a r (q1 :: rest) hne0' hfront' hlast' halt' hsame'
        simp only [List.map_cons] at IH ⊢
        exact SVRel.same ha0 hr0 (hsame q0 (by simp) hr0) IH

variable {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}

/-- **Local constancy.** On a closed interval `[a, b]` containing no zero of
any chain element, `sturmVar` takes the same value at the two endpoints.

Proof sketch (SPEC step 1): each element keeps a constant nonzero sign across
`[a, b]` by continuity of polynomial evaluation (`Polynomial.continuous_aeval`)
and the intermediate value theorem (`intermediate_value_Icc`): a sign change
would force a zero. The list of evaluation signs is therefore the same at `a`
and `b`, so `signVariations` — which depends only on those signs — agrees. -/
theorem sturmVar_const_of_no_zero (_hchain : IsSturmChain p chain)
    (a b : ℝ) (hab : a ≤ b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain b := by
  show signVariations (chain.map (Polynomial.eval a))
    = signVariations (chain.map (Polynomial.eval b))
  apply signVariations_congr
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q hq
  exact eval_sign_eq_of_no_zero hab (fun x hx => hz q hq x hx)

/-- **Interior-element crossing preserves `sturmVar`.** If `r` is not a root of
`p` and the only chain zeros in `[a, b]` occur at `r` (necessarily zeros of
interior elements), then `sturmVar` is unchanged from `a` to `b`.

Proof sketch (SPEC step 2): away from `r` local constancy applies on `[a, r]`
and `[r, b]`. At `r` the vanishing interior elements sit between neighbours of
opposite sign (`IsSturmChain.interior_alternates`), so each contributes exactly
one variation both immediately before and immediately after `r` regardless of
the sign it passes through, and the head pair (involving `p`, nonzero near `r`)
is unaffected. Hence the count at `a`, at `r`, and at `b` coincide. The value
at `r` itself is part of the statement because the global theorem places no
restriction on its endpoints, so a telescoping step may need the count exactly
at an interior-element zero. -/
theorem sturmVar_interior_cross (hchain : IsSturmChain p chain) (r : ℝ)
    (hpr : ¬ p.IsRoot r) (a b : ℝ) (har : a < r) (hrb : r < b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain r ∧ sturmVar chain r = sturmVar chain b := by
  have hab : a ≤ b := (har.trans hrb).le
  have hpr' : p.eval r ≠ 0 := hpr
  -- Chain-structure hypotheses at the special point `r`, shared by both calls.
  have hfront : ∀ q, chain.head? = some q → q.eval r ≠ 0 := by
    intro q hq; rw [hchain.head] at hq; cases hq; exact hpr'
  have hlast : ∀ q, chain.getLast? = some q → q.eval r ≠ 0 :=
    fun q hq => hchain.last_no_root q hq r
  have halt : ∀ (i : ℕ) (q0 q1 q2 : Polynomial ℝ), chain[i]? = some q0 →
      chain[i + 1]? = some q1 → chain[i + 2]? = some q2 → q1.eval r = 0 →
      q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0 :=
    fun i q0 q1 q2 h0 h1 h2 hz => hchain.interior_alternates i r q0 q1 q2 h0 h1 h2 hz
  constructor
  · show signVariations (chain.map (Polynomial.eval a))
      = signVariations (chain.map (Polynomial.eval r))
    refine (buildSVRel a r chain (fun q hq => hz q hq a ⟨le_refl a, hab⟩ (ne_of_lt har))
      hfront hlast halt (fun q hq hqr => ?_)).signVariations_eq.1
    exact eval_sign_eq_of_no_zero har.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hqr
      · exact hz q hq x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  · show signVariations (chain.map (Polynomial.eval r))
      = signVariations (chain.map (Polynomial.eval b))
    refine ((buildSVRel b r chain
      (fun q hq => hz q hq b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm)
      hfront hlast halt (fun q hq hqr => ?_)).signVariations_eq.1).symm
    exact (eval_sign_eq_of_no_zero hrb.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hqr
      · exact hz q hq x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm

/-- **Simple-zero crossing of `p` drops `sturmVar` by one, registering at `r`.**
If `r` is a (simple, by squarefreeness) root of `p` and the only chain zeros in
`[a, b]` occur at `r`, then `sturmVar` at `a` exceeds the value at `b` by
exactly one, and the drop has already registered at `r`: the value at `r`
equals the value at `b`.

Proof sketch (SPEC step 3): the head pair `(p, q)` with `q = chain[1]` has
`p * q < 0` just left of `r` and `p * q > 0` just right (`root_flank`), so this
pair contributes one variation for `x < r` and none for `x ≥ r`; with the
zero-skipping convention the zero of `p` at `r` is dropped, so the change
registers at `r` itself. All interior crossings at `r` are variation-neutral by
step 2, and away from `r` `sturmVar` is locally constant by step 1. The
half-open registration is the one design-sensitive point: it is what makes the
executable half-open counts match with no endpoint hypotheses. -/
theorem sturmVar_root_cross (_hp : p ≠ 0) (_hsf : Squarefree p)
    (_hchain : IsSturmChain p chain) (r : ℝ) (_hr : p.IsRoot r)
    (a b : ℝ) (_har : a < r) (_hrb : r < b)
    (_hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0)
    (_hpz : ∀ x ∈ Set.Icc a b, x ≠ r → ¬ p.IsRoot x) :
    sturmVar chain a = sturmVar chain b + 1 ∧ sturmVar chain r = sturmVar chain b := by
  sorry

/-- **Sturm's theorem, half-open form.** For `p ≠ 0` squarefree with a
generalised Sturm chain, the drop in `sturmVar` from `a` to `b` equals the
number of real roots of `p` in the half-open interval `(a, b]`, counted as the
cardinality of the corresponding filtered submultiset of `p.roots`.

Proof sketch (SPEC step 4): telescope steps 1–3 over the finitely many zeros of
the chain elements in `(a, b]`. Zeros of interior elements are variation-neutral
(step 2); each root of `p` drops the count by exactly one and registers at the
root under the half-open convention (step 3); between consecutive chain zeros
`sturmVar` is constant (step 1). The signed total is therefore the number of
roots of `p` in `(a, b]`. -/
theorem sturm_half_open (_hp : p ≠ 0) (_hsf : Squarefree p)
    (_hchain : IsSturmChain p chain) {a b : ℝ} (_hab : a < b) :
    (sturmVar chain a : ℤ) - sturmVar chain b =
      (p.roots.filter (fun r => a < r ∧ r ≤ b)).card := by
  sorry

/-- **Sturm's theorem, line form.** For `p ≠ 0` squarefree with a generalised
Sturm chain, the total number of real roots of `p` equals the drop in `sturmVar`
from `−∞` to `+∞`.

Proof sketch (SPEC step 5): take `a` below and `b` above every real root
(e.g. beyond a Cauchy bound). Then `sturmVar chain a = sturmVarNegInf chain` and
`sturmVar chain b = sturmVarPosInf chain`, because each chain element has
constant sign past its largest real zero equal to its sign at the corresponding
infinity, and `(a, b]` contains every real root. Apply `sturm_half_open`; the
filtered multiset is all of `p.roots`. -/
theorem sturm_line (_hp : p ≠ 0) (_hsf : Squarefree p)
    (_hchain : IsSturmChain p chain) :
    (sturmVarNegInf chain : ℤ) - sturmVarPosInf chain = p.roots.card := by
  sorry

end Sturm
