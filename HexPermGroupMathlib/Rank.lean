/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Enumerate
public import HexPermGroupMathlib.Group
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Control.Random

public section

namespace Hex.PermGroup

/-- The number of rejection attempts `randomIndex` makes before it returns
index zero. -/
@[expose] def randomIndexAttempts : Nat := 128

/-- Read `k` generator draws as the base-`width` digits of a number below
`width ^ k`, least significant digit first. Each draw is shifted down by `lo`
and reduced modulo `width`. The reduction changes nothing for a draw in the
generator's range `[lo, lo + width - 1]`. -/
@[expose] def randomDigits {g : Type} [RandomGen g] {m : Type → Type} [Monad m]
    (lo width : Nat) : Nat → RandGT g m Nat
  | 0 => pure 0
  | k + 1 => do
    let d ← _root_.Rand.next
    let rest ← randomDigits lo width k
    pure ((d - lo) % width + width * rest)

/-- Starting from `(k, span)`, multiply `span` by `width` at most `fuel` times
until it reaches `bound`, and return the final count and span. -/
@[expose] def digitSpan (width bound : Nat) : (fuel k span : Nat) → Nat × Nat
  | 0, k, span => (k, span)
  | fuel + 1, k, span =>
    if bound ≤ span then (k, span) else digitSpan width bound fuel (k + 1) (span * width)

/-- An index in `Fin bound` drawn by rejection sampling from the generator.

Let `[lo, hi]` be the generator's range and `width = hi + 1 - lo`. Take the
least `k` with `bound ≤ width ^ k` and `span = width ^ k`. One attempt reads `k`
draws as a number `x < span` (`randomDigits`) and accepts it when `x` is below
`limit`, the largest multiple of `bound` that is at most `span`, returning
`x % bound`. No modular reduction is applied to an incomplete range.

If the draws are independent and uniform on `[lo, hi]`, then `x` is uniform
below `span`, an accepted `x` is uniform below `limit`, and `x % bound` is
exactly uniform on `Fin bound`. Since `bound ≤ span`, `limit > span / 2`, so
each attempt accepts with probability above one half. After
`randomIndexAttempts = 128` rejections in a row the result is index zero.
That happens with probability below `2 ^ (-128)`, so each index has
probability within `2 ^ (-128)` of `1 / bound`, and exactly `1 / bound`
conditional on some attempt being accepted. The fixed number of attempts keeps
the definition total in `RandGT g m` for every monad `m`, including for
generators that are not uniform. A range with fewer than two values carries
no randomness, and the result is then index zero without any draw. -/
@[expose] def randomIndex {g : Type} [RandomGen g] {m : Type → Type} [Monad m]
    (bound : Nat) (h : 0 < bound) : RandGT g m (Fin bound) := do
  let (lo, hi) ← _root_.Rand.range
  let width := hi + 1 - lo
  if width < 2 ∨ bound = 1 then
    return ⟨0, h⟩
  let (k, span) := digitSpan width bound (bound.log2 + 1) 0 1
  attempt lo width k (span - span % bound) randomIndexAttempts
where
  /-- At most `fuel` attempts with acceptance threshold `limit`. -/
  attempt (lo width k limit : Nat) : Nat → RandGT g m (Fin bound)
    | 0 => pure ⟨0, h⟩
    | fuel + 1 => do
      let x ← randomDigits lo width k
      if x < limit then pure ⟨x % bound, Nat.mod_lt _ h⟩
      else attempt lo width k limit fuel

end Hex.PermGroup

namespace Hex.PermGroup.Group

/-- The computational rank and unrank functions form an equivalence. -/
@[expose] def rankEquiv (G : Group n) : Element G ≃ Fin G.order where
  toFun := G.rank
  invFun := G.unrank
  left_inv := G.unrank_rank
  right_inv := G.rank_unrank

/-- The same indexing identifies the corresponding Mathlib subgroup. -/
@[expose] def indexEquiv (G : Group n) : Fin G.order ≃ closure G.generators :=
  G.rankEquiv.symm.trans (Element.equiv G).toEquiv

/-- Each output element receives exactly the mass at its unique input index. -/
theorem unrank_probability (G : Group n) (source : PMF (Fin G.order)) (p : Element G) :
    (source.map G.unrank) p = source (G.rank p) := by
  classical
  rw [PMF.map_apply]
  have he (k : Fin G.order) : p = G.unrank k ↔ k = G.rank p := by
    constructor
    · intro h
      rw [h, G.rank_unrank]
    · rintro rfl
      exact (G.unrank_rank p).symm
  simp only [he]
  simp

/-- Conditional uniformity: unranking preserves uniform mass supplied on the
bounded indices. No assumption about a pseudorandom implementation is made. -/
theorem sample_uniform (G : Group n) (source : PMF (Fin G.order))
    (h : ∀ k, source k = (G.order : ENNReal)⁻¹) (p : Element G) :
    (source.map G.unrank) p = (G.order : ENNReal)⁻¹ := by
  rw [unrank_probability, h]

/-- The effect-polymorphic sampling API has the same probability contract when
its index source is a probability mass function. -/
theorem sampleFrom_probability
    (draw : (bound : Nat) → 0 < bound → PMF (Fin bound)) (G : Group n) (p : Element G) :
    (sampleFrom draw G) p = (draw G.order G.order_pos) (G.rank p) :=
  unrank_probability G (draw G.order G.order_pos) p

/-- An element of `G` drawn with Mathlib's random-generator interface: unrank an
index from `randomIndex`. If the generator's draws are independent and uniform
on its range, each element has probability within `2 ^ (-128)` of
`1 / order G`, and exactly `1 / order G` conditional on the index draw
accepting within its attempt limit. Mathlib's `randFin` is not used, because it
reduces a draw modulo the bound and is therefore biased. -/
@[expose] def randomElement {g : Type} [RandomGen g] {m : Type → Type} [Monad m]
    (G : Group n) : RandGT g m (Element G) :=
  G.sampleFrom randomIndex

instance {m : Type → Type} [Monad m] (G : Group n) : Random m (Element G) where
  random := G.randomElement

/-- Enumerated permutation values are exactly the corresponding subgroup. -/
theorem enumerate_spec (G : Group n) (e : Equiv.Perm (Fin n)) :
    e ∈ G.enumerate.map (fun p => p.val.toEquiv) ↔ e ∈ closure G.generators := by
  constructor
  · intro h
    obtain ⟨p, _, rfl⟩ := Array.mem_map.mp h
    exact generated_iff_mem.mp p.property
  · intro h
    let p : Element G := ⟨Perm.ofEquiv e, generated_iff_mem.mpr (by simpa using h)⟩
    exact Array.mem_map.mpr ⟨p, G.mem_enumerate p, Perm.toEquiv_ofEquiv e⟩

end Hex.PermGroup.Group
