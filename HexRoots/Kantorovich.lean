/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Pellet

public section

/-!
The Newton-Kantorovich atom witnesses of the complex root isolator. On the
closed square `s` itself (with the sup norm, so the square is the closed ball
of radius `r = 2^{−s.prec}` about its centre), the exact Taylor coefficients
`(c₀, …, c_n)` of `p` at the centre yield three strict exact-dyadic
comparisons certifying that `p` has exactly one root there, simple, in the open
square. Identifying ℂ with ℝ² carrying the sup norm, multiplication by `ζ` is a
matrix whose sup-operator norm is `hi(ζ)` exactly, which is what makes the
Newton-Kantorovich hypotheses exact-dyadic comparisons rather than error
budgets.

With `A` the approximate inverse of `p'(m)` built from the exact reciprocal
`w = conj(c₁)·invFloor (normSq c₁)` of `c₁`, and `dₖ = w·cₖ`, the witness data
is `y = lo(d₀)` (the sup norm of the Newton residual), `z₁ = hi(1 − d₁)` (the
sup-operator norm of `1 − A∘p'(m)`), and the radial Lipschitz bound
`z₂ = 2·Σ_{k=2}^{n} k·hi(dₖ)·ρ^{k−2}` with `ρ = 1449·2^{−prec−10}` the dyadic
upper bound for `√2·r`. The checks are `0 < normSq c₁`,
`y + z₁·r + z₂·r²/2 < r`, and `z₁ + z₂·r < 1`.

The atom certificate is a disjunction of this Newton-Kantorovich form with the
single-root Pellet form, so consumers of isolations never care which route
fired. Everything reachable from `nkWitnessCheck` is `@[expose]`, so the kernel
reduces the witnesses across module boundaries under `decide`; the range fold
below (rather than a `for` loop or `Array.map`) is what makes that reduction go
through.
-/
namespace Hex

/-- Floor of `1/x` at precision `q`, for positive `x`: with `x = n·2^{−k}`
    (`n` odd positive), `1/x = 2^k/n`, so the floor on the `2^{−q}` grid is
    `⌊2^{q+k}/n⌋·2^{−q}`, one integer division. This agrees with
    `Dyadic.invAtPrec` on positive arguments (both floor `1/x` to the
    `2^{−q}` grid, so `0 ≤ 1/x − result < 2^{−q}`), but it kernel-reduces:
    `invAtPrec` routes through `Rat` normalisation, whose `Nat.gcd`
    well-founded recursion `decide` cannot unfold. Junk `0` on `x ≤ 0`
    (and on `q + k < 0`, where the floor is `0` anyway since `n ≥ 1`). -/
@[expose] def Dyadic.invFloor (x : Dyadic) (q : Int) : Dyadic :=
  match x with
  | .zero => 0
  | .ofOdd n k _ =>
    if n < 0 then 0
    else
      let e := q + k
      if e < 0 then 0
      else .ofIntWithPrec (((2 ^ e.toNat : Nat) : Int) / n) q

/-- On positive inputs, the kernel-reducible reciprocal used by
    `nkWitnessCheck` agrees with the standard dyadic reciprocal. -/
theorem Dyadic.invFloor_eq_invAtPrec_of_pos {x : Dyadic} (hx : 0 < x) (q : Int) :
    Hex.Dyadic.invFloor x q = x.invAtPrec q := by
  rcases x with _ | ⟨n, k, hn⟩
  · contradiction
  simp only [Dyadic.invFloor]
  have hnpos : 0 < n := by
    rw [← Dyadic.toRat_lt_toRat_iff] at hx
    simpa only [Dyadic.toRat_zero,
      Dyadic.toRat_ofOdd_eq_mul_two_pow,
      Rat.mul_pos_iff_of_pos_right (Rat.zpow_pos (by decide : (0 : Rat) < 2)),
      Rat.intCast_pos] using hx
  simp only [show ¬ n < 0 by omega, ↓reduceIte]
  apply Dyadic.eq_invAtPrec hx
  · split
    · change (0 : Dyadic).precision ≤ some q
      rw [show (0 : Dyadic) = .zero from rfl]
      exact Option.none_le
    · rename_i h
      by_cases hz : ((2 ^ (q + k).toNat : Nat) : Int) / n = 0
      · rw [hz]
        change (0 : Dyadic).precision ≤ some q
        rw [show (0 : Dyadic) = .zero from rfl]
        exact Option.none_le
      · exact Dyadic.precision_ofIntWithPrec_le hz q
  · rw [← Dyadic.toRat_le_toRat_iff]
    simp only [Dyadic.toRat_mul]
    split
    · simp only [Dyadic.toRat_zero]
      rw [Rat.zero_mul]
      change (0 : Rat) ≤ Dyadic.toRat (1 : Dyadic)
      rw [← Dyadic.toRat_zero, Dyadic.toRat_le_toRat_iff]
      decide
    · simp only [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
        Dyadic.toRat_ofOdd_eq_mul_two_pow]
      rename_i he
      have hdiv := Int.ediv_mul_le (((2 ^ (q + k).toNat : Nat) : Int))
        (Int.ne_of_gt hnpos)
      have hdiv' : ((((2 ^ (q + k).toNat : Nat) : Int) / n * n : Int) : Rat) ≤
          (((2 ^ (q + k).toNat : Nat) : Int) : Rat) :=
        Rat.intCast_le_intCast.mpr hdiv
      simp only [Rat.intCast_mul] at hdiv'
      have hpows : (2 : Rat) ^ (-q) * 2 ^ (-k) = 2 ^ (-(q + k)) := by
        rw [← Rat.zpow_add (by decide)]
        congr 1 <;> omega
      have hpow : ((((2 ^ (q + k).toNat : Nat) : Int) : Rat)) *
          (2 : Rat) ^ (-(q + k)) = 1 := by
        have hqk : q + k = ((q + k).toNat : Int) := by omega
        have hcastpow : ((((2 ^ (q + k).toNat : Nat) : Int) : Rat)) =
            (2 : Rat) ^ (q + k) := by
          rw [hqk, Rat.zpow_natCast, Rat.intCast_natCast]
          simp only [Int.toNat_natCast]
          exact Rat.natCast_pow 2 _
        rw [hcastpow, Rat.zpow_neg]
        exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.zpow_pos (by decide)))
      have hone : Dyadic.toRat (1 : Dyadic) = (1 : Rat) := by rfl
      rw [hone]
      calc
        _ = (((((2 ^ (q + k).toNat : Nat) : Int) / n : Int) : Rat)) * (n : Rat) *
            (2 ^ (-q) * 2 ^ (-k)) := by grind
        _ = (((((2 ^ (q + k).toNat : Nat) : Int) / n : Int) : Rat)) * (n : Rat) *
            2 ^ (-(q + k)) := by rw [hpows]
        _ ≤ ((((2 ^ (q + k).toNat : Nat) : Int) : Rat)) *
            2 ^ (-(q + k)) :=
          Rat.mul_le_mul_of_nonneg_right hdiv' (Rat.zpow_nonneg (by decide))
        _ = 1 := hpow
  · rw [← Dyadic.toRat_lt_toRat_iff]
    simp only [Dyadic.toRat_mul, Dyadic.toRat_add,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
      Dyadic.toRat_ofOdd_eq_mul_two_pow]
    split
    · simp only [Dyadic.toRat_zero]
      rename_i he
      have hone : Dyadic.toRat (1 : Dyadic) = (1 : Rat) := by rfl
      rw [hone]
      simp only [Rat.intCast_one, Rat.one_mul, Rat.zero_add]
      have hpows : (2 : Rat) ^ (-q) * 2 ^ (-k) = 2 ^ (-(q + k)) := by
        rw [← Rat.zpow_add (by decide)]
        congr 1 <;> omega
      have hpow_gt : (1 : Rat) < 2 ^ (-(q + k)) := by
        have hmpos : 0 < -(q + k) := by omega
        obtain ⟨m, hm⟩ : ∃ m : Nat, -(q + k) = (m + 1 : Nat) := by
          exact ⟨(-(q + k)).toNat - 1, by omega⟩
        rw [hm, Rat.zpow_natCast]
        clear hm he
        induction m with
        | zero => decide
        | succ m ih =>
          rw [Rat.pow_succ]
          have hstep : (2 : Rat) ^ (m + 1) < (2 : Rat) ^ (m + 1) * 2 := by
            simpa using Rat.mul_lt_mul_of_pos_left (by decide : (1 : Rat) < 2)
              (Rat.pow_pos (by decide : (0 : Rat) < 2) : 0 < (2 : Rat) ^ (m + 1))
          apply Rat.not_le.mp
          intro h
          exact Rat.not_le.mpr ih (Rat.le_trans (Rat.le_of_lt hstep) h)
      have hnrat : (1 : Rat) ≤ (n : Rat) :=
        Rat.intCast_le_intCast.mpr (show (1 : Int) ≤ n by omega)
      have hmul : 2 ^ (-(q + k)) ≤ (n : Rat) * 2 ^ (-(q + k)) := by
        simpa using Rat.mul_le_mul_of_nonneg_right hnrat
          (Rat.zpow_nonneg (by decide : (0 : Rat) ≤ 2))
      have hfinal : (1 : Rat) < (n : Rat) * 2 ^ (-(q + k)) := by
        apply Rat.not_le.mp
        intro h
        exact Rat.not_le.mpr hpow_gt (Rat.le_trans hmul h)
      rw [← hpows] at hfinal
      grind
    · rename_i he
      simp only [Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
      have hone : Dyadic.toRat (1 : Dyadic) = (1 : Rat) := by rfl
      rw [hone]
      let a : Int := (2 ^ (q + k).toNat : Nat)
      have hlt := Int.lt_ediv_add_one_mul_self a hnpos
      have hlt' : (a : Rat) < (((a / n + 1 : Int) : Rat)) * (n : Rat) := by
        rw [← Rat.intCast_mul, Rat.intCast_lt_intCast]
        exact hlt
      simp only [Rat.intCast_add, Rat.intCast_one] at hlt'
      have hpows : (2 : Rat) ^ (-q) * 2 ^ (-k) = 2 ^ (-(q + k)) := by
        rw [← Rat.zpow_add (by decide)]
        congr 1 <;> omega
      have hpow0 : ((((2 ^ (q + k).toNat : Nat) : Int) : Rat)) *
          (2 : Rat) ^ (-(q + k)) = 1 := by
        have hqk : q + k = ((q + k).toNat : Int) := by omega
        have hcastpow : ((((2 ^ (q + k).toNat : Nat) : Int) : Rat)) =
            (2 : Rat) ^ (q + k) := by
          rw [hqk, Rat.zpow_natCast, Rat.intCast_natCast]
          simp only [Int.toNat_natCast]
          exact Rat.natCast_pow 2 _
        rw [hcastpow, Rat.zpow_neg]
        exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.zpow_pos (by decide)))
      have hpow : (a : Rat) * (2 : Rat) ^ (-(q + k)) = 1 := by
        simpa [a] using hpow0
      have hltmul := Rat.mul_lt_mul_of_pos_right hlt'
        (Rat.zpow_pos (by decide : (0 : Rat) < 2) : 0 < (2 : Rat) ^ (-(q + k)))
      rw [hpow] at hltmul
      dsimp [a] at hltmul ⊢
      rw [← hpows] at hltmul
      grind

/-- The Newton-Kantorovich contraction check on the closed square `s` itself
    (sup norm), with `r = 2^{−s.prec}` the half-width. Writing
    `cs = taylor p s.center` for the exact Taylor coefficients and requiring
    `2 ≤ cs.size` with `0 < normSq c₁`, it builds the exact reciprocal
    `w = conj(c₁)·invFloor (normSq c₁) q` (pinned precision
    `q = 8 + max 0 (ceilLog2 (normSq c₁))`), the residuals `dₖ = w·cₖ`, and the
    exact dyadic bounds `y = lo(d₀)`, `z₁ = hi(1 − d₁)`, and the radial
    Lipschitz bound `z₂ = 2·Σ_{k=2}^{n} k·hi(dₖ)·ρ^{k−2}` with `ρ = s.radiusHi`.
    It then returns the conjunction of the three strict exact-dyadic
    comparisons `0 < normSq c₁`, `y + z₁·r + z₂·r²/2 < r`, and
    `z₁ + z₂·r < 1`. -/
@[expose] def nkWitnessCheck (p : ZPoly) (s : DyadicSquare) : Bool :=
  let cs := taylor p s.center
  if 2 ≤ cs.size then
    let c₁ := cs.getD 1 (0, 0)
    let nsq := GaussDyadic.normSq c₁
    let q := 8 + max 0 (Hex.Dyadic.ceilLog2 nsq)
    let u := Hex.Dyadic.invFloor nsq q
    let w : GaussDyadic := (c₁.1 * u, -(c₁.2) * u)
    let d0 := GaussDyadic.mul w (cs.getD 0 (0, 0))
    let d1 := GaussDyadic.mul w (cs.getD 1 (0, 0))
    let y := GaussDyadic.lo d0
    let z₁ := Hex.Dyadic.abs (1 - d1.1) + Hex.Dyadic.abs d1.2
    let ρ := s.radiusHi
    -- One fold with a running power `ρ^{k−2}` (multiplied by `ρ` each step),
    -- accumulating `Σ_{k=2}^{cs.size−1} k·hi(w·cₖ)·ρ^{k−2}`.
    let z₂sum :=
      ((List.range cs.size).foldl (init := ((0 : Dyadic), (1 : Dyadic)))
        fun acc i =>
          if 2 ≤ i then
            let di := GaussDyadic.mul w (cs.getD i (0, 0))
            (acc.1 + Dyadic.ofInt i * GaussDyadic.hi di * acc.2, acc.2 * ρ)
          else acc).1
    let z₂ := (2 : Dyadic) * z₂sum
    let r := Dyadic.ofIntWithPrec 1 s.prec
    let halfRSq := Dyadic.ofIntWithPrec 1 (2 * s.prec + 1)
    decide (0 < nsq)
      && decide (y + z₁ * r + z₂ * halfRSq < r)
      && decide (z₁ + z₂ * r < 1)
  else
    false

/-- Newton-Kantorovich contraction witness on the closed square `s` itself
    (sup norm), with `r = 2^{−s.prec}` the half-width and `y, z₁, z₂` the exact
    dyadic bounds:

      `0 < normSq c₁  ∧  y + z₁·r + z₂·r²/2 < r  ∧  z₁ + z₂·r < 1`.

    Implies (Mathlib companion): `p` has exactly one root in the closed square,
    it is simple, and it lies in the open square. -/
@[expose] def nkWitness (p : ZPoly) (s : DyadicSquare) : Prop := nkWitnessCheck p s = true

instance {p : ZPoly} {s : DyadicSquare} : Decidable (nkWitness p s) :=
  inferInstanceAs (Decidable (_ = true))

/-- An atom certificate: either certificate form for "exactly one simple root
    in the certified region". The two disjuncts certify different regions (the
    closed square for `nkWitness`, the circumscribed disc for the Pellet form);
    every consumer needs only the shared consequence that the root lies in the
    stored square's circumscribed disc. -/
@[expose] def atomWitness (p : ZPoly) (s : DyadicSquare) : Prop :=
  nkWitness p s ∨ witness p s 1

instance {p : ZPoly} {s : DyadicSquare} : Decidable (atomWitness p s) :=
  inferInstanceAs (Decidable (nkWitness p s ∨ witness p s 1))

/-- Which atom certificates `certify?` attempts, and in which order.
    `nkThenPellet` is the default; the singleton strategies exist for the
    side-by-side comparison of the two atom forms. -/
inductive AtomStrategy | nk | pellet | nkThenPellet
deriving DecidableEq, Repr

/-- An atom: one square whose certified region (the square itself for the
    Newton-Kantorovich disjunct, the circumscribed disc for the Pellet
    disjunct) contains exactly one simple root. -/
structure DyadicRootIsolation (p : ZPoly) where
  /-- The isolating square. -/
  square : DyadicSquare
  /-- Either atom certificate on the square's certified region. -/
  witness : Hex.atomWitness p square

/-- The result of certifying one component: an atom (either atom certificate)
    or a `k ≥ 1` Pellet cluster. -/
inductive Certified (p : ZPoly) where
  /-- Exactly one simple root, isolated as an atom. -/
  | atom (iso : DyadicRootIsolation p)
  /-- Exactly `k` roots with multiplicity, certified as a Pellet cluster. -/
  | cluster (cl : DyadicRootCluster p)

/-- Repackage a certified `k = 1` cluster as an atom, taking the Pellet
    disjunct of `atomWitness` on the enclosing square. Total: the cluster's
    Pellet witness already certifies exactly one root in the enclosing disc. -/
def DyadicRootCluster.atomize {p : ZPoly} (c : DyadicRootCluster p) (h : c.k = 1) :
    DyadicRootIsolation p :=
  ⟨encSquare c.squares, Or.inr (h ▸ c.witness)⟩

/-- Certify an arbitrary candidate square as an atom, deciding both
    `atomWitness` disjuncts fresh. This is the documented way to build a
    `DyadicRootIsolation` outside the drivers, e.g. after transforming an
    isolation's square (hex-number-field's `inv?` re-certification). -/
def certifyAtom? (p : ZPoly) (s : DyadicSquare) : Option (DyadicRootIsolation p) :=
  if h : atomWitness p s then some ⟨s, h⟩ else none

end Hex
