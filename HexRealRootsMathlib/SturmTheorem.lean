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

variable {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}

/-- **Local constancy.** On a closed interval `[a, b]` containing no zero of
any chain element, `sturmVar` takes the same value at the two endpoints.

Proof sketch (SPEC step 1): each element keeps a constant nonzero sign across
`[a, b]` by continuity of polynomial evaluation (`Polynomial.continuous_aeval`)
and the intermediate value theorem (`intermediate_value_Icc`): a sign change
would force a zero. The list of evaluation signs is therefore the same at `a`
and `b`, so `signVariations` — which depends only on those signs — agrees. -/
theorem sturmVar_const_of_no_zero (_hchain : IsSturmChain p chain)
    (a b : ℝ) (_hab : a ≤ b)
    (_hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain b := by
  sorry

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
theorem sturmVar_interior_cross (_hchain : IsSturmChain p chain) (r : ℝ)
    (_hpr : ¬ p.IsRoot r) (a b : ℝ) (_har : a < r) (_hrb : r < b)
    (_hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain r ∧ sturmVar chain r = sturmVar chain b := by
  sorry

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
