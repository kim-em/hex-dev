/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib

public section

/-!
Self-contained scaffolding for Sturm's theorem over `Polynomial ℝ`.

This module defines the zero-skipping sign-variation count `Sturm.sturmVar`
of a chain of real polynomials at a point, and the predicate
`Sturm.IsSturmChain` capturing the sign axioms that the root-counting
argument uses. Nothing here refers to any `HexRealRoots` executable type:
the development is a slice over `Polynomial ℝ` that is intended to be
upstreamable to Mathlib once exercised by the executable-correspondence
files that arrive in later PRs.

The zero-skipping convention: the variation count of a sign pattern such as
`(+, 0, −)` is `1`. Concretely we drop the zero evaluations and count the
adjacent pairs of opposite sign among what remains.
-/

open Filter Topology

namespace Sturm

/-- Count the sign changes of a real list: the number of adjacent pairs
whose product is negative. Callers first drop the zero entries (see
`Sturm.signVariations`), so on a zero-free list this is exactly the number
of adjacent opposite-sign pairs. -/
@[expose]
noncomputable def countSignChanges : List ℝ → ℕ
  | a :: b :: rest => (if a * b < 0 then 1 else 0) + countSignChanges (b :: rest)
  | _ => 0

@[simp] theorem countSignChanges_nil : countSignChanges [] = 0 := rfl

@[simp] theorem countSignChanges_singleton (a : ℝ) : countSignChanges [a] = 0 := rfl

theorem countSignChanges_cons_cons (a b : ℝ) (rest : List ℝ) :
    countSignChanges (a :: b :: rest) =
      (if a * b < 0 then 1 else 0) + countSignChanges (b :: rest) := rfl

/-- Zero-skipping sign variations of a real list: drop the zeros, then count
the adjacent opposite-sign pairs. This is the variation count that both the
pointwise chain evaluations and the leading-coefficient signs at `±∞` feed
into. -/
@[expose]
noncomputable def signVariations (l : List ℝ) : ℕ :=
  countSignChanges (l.filter (fun v => decide (v ≠ 0)))

@[simp] theorem signVariations_nil : signVariations [] = 0 := rfl

/-- Prepending a zero entry does not change the sign variations. -/
theorem signVariations_cons_zero (l : List ℝ) :
    signVariations (0 :: l) = signVariations l := by
  simp [signVariations]

/-- Prepending a nonzero entry `a` to a list whose first surviving entry has
the same sign as `a` (or which becomes empty after dropping zeros) is
governed by `countSignChanges`; this unfolding lemma exposes the recursion to
downstream local-sign arguments. -/
theorem signVariations_cons_ne (a : ℝ) (l : List ℝ) (ha : a ≠ 0) :
    signVariations (a :: l) =
      countSignChanges (a :: l.filter (fun v => decide (v ≠ 0))) := by
  simp [signVariations, ha]

/-- Zero-skipping sign variations of the chain `chain` evaluated at `x`:
the sign variations of the list of evaluations `chain.map (·.eval x)`. -/
@[expose]
noncomputable def sturmVar (chain : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
  signVariations (chain.map (Polynomial.eval x))

@[simp] theorem sturmVar_nil (x : ℝ) : sturmVar [] x = 0 := rfl

/-- A chain element that vanishes at `x` contributes no variation at `x`:
`sturmVar` ignores it. -/
theorem sturmVar_cons_zero {q : Polynomial ℝ} {x : ℝ} (h : q.eval x = 0)
    (chain : List (Polynomial ℝ)) :
    sturmVar (q :: chain) x = sturmVar chain x := by
  simp [sturmVar, List.map_cons, signVariations, h]

/-- A generalised Sturm chain for `p`: the sign axioms that the counting
argument actually uses, packaged as explicit fields. The chain is stored as
a plain `List (Polynomial ℝ)` and elements are addressed by index through
`getElem?`, so no length lower bound is baked in (a nonzero constant `p` has
the one-element chain `[p]`).

The fields, in the numbering of the SPEC:

* `nonempty` / `head` — the chain is nonempty and its head is `p`;
* `root_flank` — at every real root `r` of `p` there is a second element
  `q` (`chain[1] = q`), nonzero at `r`, with `p * q` negative on a punctured
  left neighbourhood of `r` and positive on a punctured right neighbourhood.
  Phrasing the second element existentially forbids the degenerate witness in
  which `p` has a root but the chain has no derivative-like second entry;
* `consec_coprime` — consecutive elements never vanish at a common point;
* `interior_alternates` — when an interior element (one with both neighbours
  present) vanishes at a point, both neighbours are nonzero there and have
  opposite signs, so the local pattern is `(±, 0, ∓)`;
* `last_no_root` — the last element has no real zero. -/
structure IsSturmChain (p : Polynomial ℝ) (chain : List (Polynomial ℝ)) : Prop where
  /-- The chain is nonempty. -/
  nonempty : chain ≠ []
  /-- The head of the chain is `p`. -/
  head : chain.head? = some p
  /-- At every real root `r` of `p`, the chain has a second element `q`,
  nonzero at `r`, with `p * q` negative just left of `r` and positive just
  right of `r`. -/
  root_flank : ∀ r : ℝ, p.IsRoot r → ∃ q : Polynomial ℝ, chain[1]? = some q ∧
    q.eval r ≠ 0 ∧
    (∀ᶠ x in 𝓝[<] r, (p * q).eval x < 0) ∧
    (∀ᶠ x in 𝓝[>] r, 0 < (p * q).eval x)
  /-- Consecutive elements have no common real zero. -/
  consec_coprime : ∀ (i : ℕ) (x : ℝ) (a b : Polynomial ℝ),
    chain[i]? = some a → chain[i + 1]? = some b → a.eval x = 0 → b.eval x ≠ 0
  /-- Whenever the interior element `b = chain[i+1]` vanishes at `x`, its two
  neighbours `a = chain[i]` and `c = chain[i+2]` are nonzero there and have
  opposite signs. -/
  interior_alternates : ∀ (i : ℕ) (x : ℝ) (a b c : Polynomial ℝ),
    chain[i]? = some a → chain[i + 1]? = some b → chain[i + 2]? = some c →
    b.eval x = 0 → a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0
  /-- The last element of the chain has no real zero. -/
  last_no_root : ∀ q : Polynomial ℝ, chain.getLast? = some q → ∀ x : ℝ, q.eval x ≠ 0

end Sturm
