/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.Multifactor
public import HexHensel.Quadratic

public section

/-!
Quadratic multifactor Hensel lifting.

This module exposes `multifactorLiftQuadratic`, the production multifactor
Hensel lifter named on equal footing with `multifactorLift` in
`hex-hensel`. The implementation reuses the full per-step primitive
`quadraticHenselStep` while a later correction still needs Bezout witnesses,
then uses `quadraticHenselFactors` for the final factor-only correction inside
a count-balanced product tree with a guarded dominant-degree split. Iteration returns the
exact requested precision `p^k`, with at most one exponent of transient
overshoot rather than the old next-power-of-two schedule.

The companion theorem states the ordered-product congruence contract for
the lifted array. The linear-vs-quadratic agreement obligation lives in
`hex-hensel-mathlib`.
-/

namespace Hex

namespace ZPoly

/-- Number of quadratic-doubling steps needed to reach precision `p^k`
from data valid modulo `p`. Returns `0` when `k ≤ 1` (no doubling needed)
and `⌊log₂ (k - 1)⌋ + 1` otherwise, the least `n` with `k ≤ 2 ^ n`.
This remains the public fuel bound used by downstream recombination searches. -/
@[expose]
def quadraticDoublingSteps (k : Nat) : Nat :=
  if k ≤ 1 then 0 else (k - 1).log2 + 1

/-- Zero requested precision needs no quadratic doubling steps. -/
@[simp, grind =] theorem quadraticDoublingSteps_zero :
    quadraticDoublingSteps 0 = 0 := by
  simp [quadraticDoublingSteps]

/-- Precision `p^1` is the input precision, so it needs no doubling steps. -/
@[simp, grind =] theorem quadraticDoublingSteps_one :
    quadraticDoublingSteps 1 = 0 := by
  simp [quadraticDoublingSteps]

/-- Canonicalise every component of a quadratic lift at precision `p^k`. -/
private def reduceLift
    (p k : Nat) [ZMod64.Bounds p]
    (r : QuadraticLiftResult) : QuadraticLiftResult :=
  { g := ZPoly.reduceModPow r.g p k
    h := ZPoly.reduceModPow r.h p k
    s := ZPoly.reduceModPow r.s p k
    t := ZPoly.reduceModPow r.t p k }

/-- Return a lift reduced at exactly exponent `k`. Recursing through
`ceil(k / 2)` limits a correction's transient working exponent to `k` when
even and `k + 1` when odd, instead of the next power of two. -/
private def liftExact
    (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    (k : Nat) → QuadraticLiftResult → QuadraticLiftResult
  | k, acc =>
      if k ≤ 1 then
        reduceLift p k acc
      else
        let half := (k + 1) / 2
        let prior := liftExact p f half acc
        reduceLift p k <|
          quadraticHenselStep (p ^ half) f prior.g prior.h prior.s prior.t
  termination_by k => k
  decreasing_by omega

/-- Lift a Bezout-witnessed factorisation modulo `p` to one valid modulo
`p^k` by iterating `quadraticHenselStep` at exact requested exponents.

Each recursive level first reaches `p^ceil(k/2)`, doubles once, and reduces
to `p^k`. This uses the same logarithmic number of quadratic steps as the
power-of-two schedule while avoiding excess big-integer precision. -/
def henselLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) : QuadraticLiftResult :=
  liftExact p f k { g, h, s, t }

/-- Exact-exponent lift of only the final two factors. Earlier levels retain
Bezout witnesses for the next correction; the last level omits the witness
update because multifactor recursion consumes only the two factors. -/
def henselLiftFactors
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) : ZPoly × ZPoly :=
  if k ≤ 1 then
    (ZPoly.reduceModPow g p k, ZPoly.reduceModPow h p k)
  else
    let half := (k + 1) / 2
    let prior := liftExact p f half { g, h, s, t }
    let factors := quadraticHenselFactors (p ^ half) f
      prior.g prior.h prior.s prior.t
    (ZPoly.reduceModPow factors.1 p k, ZPoly.reduceModPow factors.2 p k)

/-- The factor-only final step is byte-identical to projecting the full lift. -/
theorem henselLiftFactors_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) :
    henselLiftFactors p k f g h s t =
      ((henselLiftQuadratic p k f g h s t).g,
        (henselLiftQuadratic p k f g h s t).h) := by
  unfold henselLiftFactors henselLiftQuadratic
  rw [liftExact]
  split
  · rfl
  · dsimp only
    rw [quadraticHenselFactors_eq]
    rfl

theorem henselLiftFactors_fst
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) :
    (henselLiftFactors p k f g h s t).1 = (henselLiftQuadratic p k f g h s t).g := by
  rw [henselLiftFactors_eq]

theorem henselLiftFactors_snd
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) :
    (henselLiftFactors p k f g h s t).2 = (henselLiftQuadratic p k f g h s t).h := by
  rw [henselLiftFactors_eq]

/-- Sum of polynomial degrees used to estimate the work on one side of a
multifactor Hensel split. -/
def factorDegreeSum (factors : List ZPoly) : Nat :=
  factors.foldl (fun total g => total + g.degree?.getD 0) 0

/-- Largest polynomial degree in a prospective multifactor Hensel node. -/
def factorMaxDegree (factors : List ZPoly) : Nat :=
  factors.foldl (fun largest g => max largest (g.degree?.getD 0)) 0

/-- Degree imbalance produced by splitting `factors` at `i`. -/
def splitImbalance (factors : List ZPoly) (i : Nat) : Nat :=
  let left := factorDegreeSum (factors.take i)
  let right := factorDegreeSum (factors.drop i)
  if left ≤ right then right - left else left - right

/-- Choose a nontrivial prefix split for a multifactor Hensel node. When one
modular factor has more than half the total degree, choose the prefix split
whose two total degrees are closest; this avoids recursively pairing that
dominant factor with a much smaller neighbour. Otherwise keep the count-halving
tree, whose deliberately unbalanced degree splits can make the root XGCD much
cheaper. The final clamp makes the result valid for every list of length at
least two, independently of the degree data. -/
def balancedSplitIndex (factors : List ZPoly) : Nat :=
  let candidates := (List.range (factors.length - 1)).map (fun i => i + 1)
  let raw :=
    if factorDegreeSum factors < 2 * factorMaxDegree factors then
      candidates.foldl (init := 1) fun best i =>
        if splitImbalance factors i < splitImbalance factors best then i else best
    else
      factors.length / 2
  max 1 (min raw (factors.length - 1))

theorem balancedSplitIndex_pos (factors : List ZPoly) :
    0 < balancedSplitIndex factors := by
  simp only [balancedSplitIndex]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)

theorem balancedSplitIndex_lt_length
    (factors : List ZPoly) (h : 2 ≤ factors.length) :
    balancedSplitIndex factors < factors.length := by
  simp only [balancedSplitIndex]
  omega

/-- Recursive list-shape worker behind `multifactorLiftQuadratic`, shaped as a
count-balanced product tree except where a dominant-degree factor calls for a
degree-aware split. At each non-singleton step it lifts the left product `g`
against the right product `h` via `henselLiftFactors`, then recurses into both
sides with the lifted sub-products as the new targets. The two recursive
outputs are concatenated `L`-then-`R`, so the returned array stays in the
original factor order. The singleton case returns the input reduced modulo
`p^k`; the empty case returns the empty array. Every output is the same reduced
value because the Hensel lift is unique modulo `p^k`. -/
@[expose]
def multifactorLiftQuadraticList
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Array ZPoly
  | [] => #[]
  | [_g] => #[ZPoly.reduceModPow f p k]
  | g₀ :: g₁ :: rest =>
      let gs := g₀ :: g₁ :: rest
      let split := balancedSplitIndex gs
      let L := gs.take split
      let R := gs.drop split
      let g := Array.polyProduct L.toArray
      let h := Array.polyProduct R.toArray
      let xgcd := ZPoly.normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftFactors p k f g h s t
      multifactorLiftQuadraticList p k lifted.1 L ++
        multifactorLiftQuadraticList p k lifted.2 R
  termination_by factors => factors.length
  decreasing_by
    all_goals
      simp only [List.length_take, List.length_drop, List.length_cons]
      have hpos := balancedSplitIndex_pos (g₀ :: g₁ :: rest)
      have hlt := balancedSplitIndex_lt_length (g₀ :: g₁ :: rest) (by simp)
      simp only [List.length_cons] at hlt
      omega

/--
Quadratic multifactor Hensel lift.

Lifts an ordered array of factors of `f` from congruence modulo `p` to
congruence modulo `p^k` using the doubling step
{name}`Hex.ZPoly.quadraticHenselStep`
inside the guarded multifactor product tree.
-/
@[expose]
def multifactorLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftQuadraticList p k f factors.toList

/-- The proof state carried by one quadratic Hensel loop modulus `m`. A
caller writing proofs against this invariant must supply three conjuncts,
in this order:

1. **Product congruence**: `acc.g * acc.h ≡ f (mod m)`;
2. **Bezout congruence**: `acc.s * acc.g + acc.t * acc.h ≡ 1 (mod m)`;
3. **Leading factor monic**: `acc.g` is monic.

The forward theorem `QuadraticLiftLoopInvariant.of_product_bezout_monic` takes
the three facts in the same order. Together they are exactly the preconditions
consumed by one application of {name}`Hex.ZPoly.quadraticHenselStep` and,
inductively, by the exact-exponent recursion. -/
def QuadraticLiftLoopInvariant
    (m : Nat) (f : ZPoly) (acc : QuadraticLiftResult) : Prop :=
  ZPoly.congr (acc.g * acc.h) f m ∧
    ZPoly.congr (acc.s * acc.g + acc.t * acc.h) 1 m ∧
    DensePoly.Monic acc.g

/-- Constructor for the initial quadratic split invariant from the three
proof obligations supplied by factor-product, Bezout, and monicness facts. -/
@[grind =>]
theorem QuadraticLiftLoopInvariant.of_product_bezout_monic
    {m : Nat} {f g h s t : ZPoly}
    (hprod : ZPoly.congr (g * h) f m)
    (hbezout : ZPoly.congr (s * g + t * h) 1 m)
    (hg_monic : DensePoly.Monic g) :
    QuadraticLiftLoopInvariant m f { g, h, s, t } :=
  ⟨hprod, hbezout, hg_monic⟩

/-- Product-congruence projection of `QuadraticLiftLoopInvariant`. -/
@[simp, grind =>]
theorem QuadraticLiftLoopInvariant.prod_congr
    {m : Nat} {f : ZPoly} {acc : QuadraticLiftResult}
    (h : QuadraticLiftLoopInvariant m f acc) :
    ZPoly.congr (acc.g * acc.h) f m := h.1

/-- Bezout-congruence projection of `QuadraticLiftLoopInvariant`. -/
@[simp, grind =>]
theorem QuadraticLiftLoopInvariant.bezout_congr
    {m : Nat} {f : ZPoly} {acc : QuadraticLiftResult}
    (h : QuadraticLiftLoopInvariant m f acc) :
    ZPoly.congr (acc.s * acc.g + acc.t * acc.h) 1 m := h.2.1

/-- Monicness projection of `QuadraticLiftLoopInvariant`: the leading factor
`acc.g` is monic. -/
@[simp, grind =>]
theorem QuadraticLiftLoopInvariant.monic
    {m : Nat} {f : ZPoly} {acc : QuadraticLiftResult}
    (h : QuadraticLiftLoopInvariant m f acc) :
    DensePoly.Monic acc.g := h.2.2

/--
One quadratic step preserves the loop invariant while replacing `m` by `m*m`.

This is the local invariant-preservation surface consumed by the quadratic
lift recursion.
-/
theorem quadraticLiftLoopInvariant_step
    (m : Nat) (f : ZPoly) (acc : QuadraticLiftResult)
    (hm : 1 < m)
    (hinv : QuadraticLiftLoopInvariant m f acc) :
    let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
    QuadraticLiftLoopInvariant (m * m) f next := by
  rcases hinv with ⟨hprod, hbez, hmonic⟩
  intro next
  have hstep :
      ZPoly.congr (next.g * next.h) f (m * m) ∧
        ZPoly.congr (next.s * next.g + next.t * next.h) 1 (m * m) := by
    simpa [next] using
      quadraticHenselStep_spec m f acc.g acc.h acc.s acc.t hm hprod hbez hmonic
  exact
    ⟨hstep.1, hstep.2,
      by
        simpa [next] using
          quadraticHenselStep_monic m f acc.g acc.h acc.s acc.t hm hmonic⟩

private theorem congr_of_modulus_dvd
    (f g : ZPoly) {m n : Nat}
    (hmn : m ∣ n)
    (hfg : ZPoly.congr f g n) :
    ZPoly.congr f g m := by
  intro i
  have hmnInt : (m : Int) ∣ (n : Int) := by
    exact_mod_cast hmn
  exact Int.emod_eq_zero_of_dvd
    (Int.dvd_trans hmnInt (Int.dvd_of_emod_eq_zero (hfg i)))

private theorem congr_of_pow_le
    (p a b : Nat) (f g : ZPoly)
    (hab : a ≤ b)
    (hfg : ZPoly.congr f g (p ^ b)) :
    ZPoly.congr f g (p ^ a) :=
  congr_of_modulus_dvd f g (Nat.pow_dvd_pow p hab) hfg

/--
The doubling count reaches the requested precision exponent.

After `quadraticDoublingSteps k` iterations from precision exponent `1`, the
quadratic wrapper has reached exponent `2 ^ quadraticDoublingSteps k`, which
is at least `k`.
-/
theorem le_two_pow_quadraticDoublingSteps (k : Nat) :
    k ≤ 2 ^ quadraticDoublingSteps k := by
  by_cases hk : k ≤ 1
  · simp [quadraticDoublingSteps, hk]
  · have hpred_lt : k - 1 < 2 ^ ((k - 1).log2 + 1) :=
      Nat.lt_log2_self
    simp [quadraticDoublingSteps, hk]
    omega

private theorem congr_mul_reduceModPow_pair
    (p k : Nat) [ZMod64.Bounds p] (g h : ZPoly) :
    ZPoly.congr
      (ZPoly.reduceModPow g p k * ZPoly.reduceModPow h p k)
      (g * h)
      (p ^ k) := by
  apply ZPoly.congr_mul
  · exact ZPoly.congr_reduceModPow g p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  · exact ZPoly.congr_reduceModPow h p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))

/-- Reducing every component from exponent `n` to a positive exponent `k ≤ n`
preserves the quadratic lift invariant. -/
private theorem reduceLift_invariant
    (p k n : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (acc : QuadraticLiftResult)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant (p ^ n) f acc) :
    QuadraticLiftLoopInvariant (p ^ k) f (reduceLift p k acc) := by
  have hprod_k : ZPoly.congr (acc.g * acc.h) f (p ^ k) :=
    congr_of_pow_le p k n _ _ hkn hinv.prod_congr
  have hprod_red := congr_mul_reduceModPow_pair p k acc.g acc.h
  have hprod :
      ZPoly.congr
        ((reduceLift p k acc).g * (reduceLift p k acc).h) f (p ^ k) := by
    exact ZPoly.congr_trans _ _ _ _ (by simpa [reduceLift] using hprod_red) hprod_k
  have hbez_k : ZPoly.congr (acc.s * acc.g + acc.t * acc.h) 1 (p ^ k) :=
    congr_of_pow_le p k n _ _ hkn hinv.bezout_congr
  have hred_sg := congr_mul_reduceModPow_pair p k acc.s acc.g
  have hred_th := congr_mul_reduceModPow_pair p k acc.t acc.h
  have hbez_red :
      ZPoly.congr
        ((reduceLift p k acc).s * (reduceLift p k acc).g +
          (reduceLift p k acc).t * (reduceLift p k acc).h)
        (acc.s * acc.g + acc.t * acc.h) (p ^ k) := by
    simpa [reduceLift] using ZPoly.congr_add _ _ _ _ _ hred_sg hred_th
  have hbez := ZPoly.congr_trans _ _ _ _ hbez_red hbez_k
  have hmonic : DensePoly.Monic (reduceLift p k acc).g := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simpa [reduceLift] using
      reduceModPow_monic_of_monic p k' acc.g hp hinv.monic
  exact ⟨hprod, hbez, hmonic⟩

/-- Exact-exponent recursion preserves the quadratic invariant at precisely
the requested positive exponent. -/
private theorem liftExact_invariant
    (p : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (k : Nat) (acc : QuadraticLiftResult)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f acc) :
    QuadraticLiftLoopInvariant (p ^ k) f (liftExact p f k acc) := by
  induction k, acc using liftExact.induct (p := p) (f := f) with
  | case1 k acc hsmall =>
      have hk_one : k = 1 := by omega
      subst k
      rw [liftExact]
      apply reduceLift_invariant p 1 1 f acc (by omega) (by omega) hp
      simpa using hinv
  | case2 k acc hlarge half ih =>
      rw [liftExact]
      simp only [if_neg hlarge]
      let prior := liftExact p f half acc
      let next := quadraticHenselStep (p ^ half) f
        prior.g prior.h prior.s prior.t
      have hhalf_pos : 1 ≤ half := by
        dsimp [half]
        omega
      have hk_le : k ≤ 2 * half := by
        dsimp [half]
        omega
      have hprior : QuadraticLiftLoopInvariant (p ^ half) f prior := by
        exact ih hhalf_pos hinv
      have hm : 1 < p ^ half := Nat.one_lt_pow (Nat.ne_of_gt hhalf_pos) hp
      have hstep : QuadraticLiftLoopInvariant (p ^ (2 * half)) f next := by
        have hsquare := quadraticLiftLoopInvariant_step
          (p ^ half) f prior hm hprior
        have hpow : p ^ half * p ^ half = p ^ (2 * half) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        simpa [next, hpow] using hsquare
      exact reduceLift_invariant p k (2 * half) f next hk hk_le hp hstep

/-- Canonical reduction at a positive exponent does not change either factor
modulo the base prime. -/
private theorem reduceLift_factors_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (acc : QuadraticLiftResult) (hk : 1 ≤ k) :
    ZPoly.congr (reduceLift p k acc).g acc.g p ∧
      ZPoly.congr (reduceLift p k acc).h acc.h p := by
  have hpos : 0 < p ^ k := Nat.pow_pos (ZMod64.Bounds.pPos (p := p))
  have hgk := ZPoly.congr_reduceModPow acc.g p k hpos
  have hhk := ZPoly.congr_reduceModPow acc.h p k hpos
  have hg := congr_of_pow_le p 1 k _ _ hk hgk
  have hh := congr_of_pow_le p 1 k _ _ hk hhk
  simpa [reduceLift, Nat.pow_one] using And.intro hg hh

/-- Exact-exponent lifting retains both input factors modulo the base prime. -/
private theorem liftExact_factors_congr_mod_base
    (p : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (k : Nat) (acc : QuadraticLiftResult)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f acc) :
    ZPoly.congr (liftExact p f k acc).g acc.g p ∧
      ZPoly.congr (liftExact p f k acc).h acc.h p := by
  induction k, acc using liftExact.induct (p := p) (f := f) with
  | case1 k acc hsmall =>
      have hk_one : k = 1 := by omega
      subst k
      rw [liftExact]
      exact reduceLift_factors_congr_mod_base p 1 acc (by omega)
  | case2 k acc hlarge half ih =>
      rw [liftExact]
      simp only [if_neg hlarge]
      let prior := liftExact p f half acc
      let next := quadraticHenselStep (p ^ half) f
        prior.g prior.h prior.s prior.t
      have hhalf_pos : 1 ≤ half := by
        dsimp [half]
        omega
      have hprior_congr :
          ZPoly.congr prior.g acc.g p ∧ ZPoly.congr prior.h acc.h p :=
        ih hhalf_pos hinv
      have hprior_inv : QuadraticLiftLoopInvariant (p ^ half) f prior :=
        liftExact_invariant p f half acc hhalf_pos hp hinv
      have hm : 1 < p ^ half := Nat.one_lt_pow (Nat.ne_of_gt hhalf_pos) hp
      have hstep_m := quadraticHenselStep_factor_congr_mod_base
        (p ^ half) f prior.g prior.h prior.s prior.t hm hprior_inv.prod_congr
      have hp_dvd : p ∣ p ^ half := by
        have hdvd := Nat.pow_dvd_pow p hhalf_pos
        simpa [Nat.pow_one] using hdvd
      have hstep_p :
          ZPoly.congr next.g prior.g p ∧ ZPoly.congr next.h prior.h p := by
        exact ⟨congr_of_modulus_dvd _ _ hp_dvd (by simpa [next] using hstep_m.1),
          congr_of_modulus_dvd _ _ hp_dvd (by simpa [next] using hstep_m.2)⟩
      have hreduced := reduceLift_factors_congr_mod_base p k next hk
      exact ⟨
        ZPoly.congr_trans _ _ _ p hreduced.1
          (ZPoly.congr_trans _ _ _ p hstep_p.1 hprior_congr.1),
        ZPoly.congr_trans _ _ _ p hreduced.2
          (ZPoly.congr_trans _ _ _ p hstep_p.2 hprior_congr.2)⟩

/--
The cofactor produced by `henselLiftQuadratic` is congruent to the input
cofactor modulo `p`. Every exact-exponent step adjusts `h` by a multiple of
the current modulus, and canonical reduction preserves the base congruence.

This is the surface used downstream by the multifactor `_of_factorsModP`
boundary theorem: it lets the recursive call on `lifted.h, rest` reuse the
same mod-`p` product hypothesis the caller supplies for the head split.
-/
theorem henselLiftQuadratic_h_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    ZPoly.congr (henselLiftQuadratic p k f g h s t).h h p := by
  simpa [henselLiftQuadratic] using
    (liftExact_factors_congr_mod_base p f k { g, h, s, t } hk hp hinv).2

/--
The leading factor produced by `henselLiftQuadratic` is congruent to the input
leading factor modulo `p`. Parallel to `henselLiftQuadratic_h_congr_mod_base`;
used downstream to show each output of `multifactorLiftQuadratic` reduces mod
`p` to its corresponding input factor.
-/
theorem henselLiftQuadratic_g_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    ZPoly.congr (henselLiftQuadratic p k f g h s t).g g p := by
  simpa [henselLiftQuadratic] using
    (liftExact_factors_congr_mod_base p f k { g, h, s, t } hk hp hinv).1

/-- The factor-only lift's left result retains the input factor modulo `p`. -/
theorem henselLiftFactors_fst_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    ZPoly.congr (henselLiftFactors p k f g h s t).1 g p := by
  rw [henselLiftFactors_fst]
  exact henselLiftQuadratic_g_congr_mod_base p k f g h s t hk hp hinv

/-- The factor-only lift's right result retains the input cofactor modulo `p`. -/
theorem henselLiftFactors_snd_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    ZPoly.congr (henselLiftFactors p k f g h s t).2 h p := by
  rw [henselLiftFactors_snd]
  exact henselLiftQuadratic_h_congr_mod_base p k f g h s t hk hp hinv

/-- Public correctness contract for the binary quadratic wrapper: starting
from a `QuadraticLiftLoopInvariant p f { g, h, s, t }`, the lifted pair
satisfies `lifted.g * lifted.h ≡ f (mod p^k)`. -/
theorem henselLiftQuadratic_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    let lifted := henselLiftQuadratic p k f g h s t
    ZPoly.congr (lifted.g * lifted.h) f (p ^ k) := by
  exact (liftExact_invariant p f k { g, h, s, t } hk hp hinv).prod_congr

/-- The factor-only exact lift multiplies to the target modulo `p^k`. -/
theorem henselLiftFactors_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    ZPoly.congr
      ((henselLiftFactors p k f g h s t).1 *
        (henselLiftFactors p k f g h s t).2) f (p ^ k) := by
  rw [henselLiftFactors_fst, henselLiftFactors_snd]
  exact henselLiftQuadratic_spec p k f g h s t hk hp hinv

/-- Public Bezout-pair contract for the binary quadratic wrapper. The lifted
Bezout pair remains valid modulo the exact requested precision `p^k`. -/
theorem henselLiftQuadratic_bezout_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    let lifted := henselLiftQuadratic p k f g h s t
    ZPoly.congr (lifted.s * lifted.g + lifted.t * lifted.h) 1 (p ^ k) := by
  exact (liftExact_invariant p f k { g, h, s, t } hk hp hinv).bezout_congr

/--
Recursive preconditions required by the guarded quadratic multifactor tree.

In the non-singleton arm the factor list is split at `balancedSplitIndex`; the
three conjuncts
are exactly the inputs `henselLiftFactors_spec` consumes for the binary split
of the left product `g := Array.polyProduct L.toArray` against the right product
`h := Array.polyProduct R.toArray`, followed by the recursive preconditions for
each lifted sub-product:

1. `QuadraticLiftLoopInvariant` at modulus `p` — initial state package
   (product congruence, Bezout, monicness) for the binary exact lift;
2. `QuadraticMultifactorLiftInvariant` for the left half with `lifted.1`
   as the new target;
3. `QuadraticMultifactorLiftInvariant` for the right half with `lifted.2`
   as the new target.

The base cases impose the trivial obligations: `congr 1 f (p ^ k)` for the
empty list (vacuous product) and no preconditions for a singleton.
-/
@[expose]
def QuadraticMultifactorLiftInvariant
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Prop
  | [] => ZPoly.congr 1 f (p ^ k)
  | [_g] => True
  | g₀ :: g₁ :: rest =>
      let gs := g₀ :: g₁ :: rest
      let split := balancedSplitIndex gs
      let L := gs.take split
      let R := gs.drop split
      let g := Array.polyProduct L.toArray
      let h := Array.polyProduct R.toArray
      let xgcd := normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftFactors p k f g h s t
      QuadraticLiftLoopInvariant p f { g, h, s, t } ∧
        QuadraticMultifactorLiftInvariant p k lifted.1 L ∧
          QuadraticMultifactorLiftInvariant p k lifted.2 R
  termination_by factors => factors.length
  decreasing_by
    all_goals
      simp only [List.length_take, List.length_drop, List.length_cons]
      have hpos := balancedSplitIndex_pos (g₀ :: g₁ :: rest)
      have hlt := balancedSplitIndex_lt_length (g₀ :: g₁ :: rest) (by simp)
      simp only [List.length_cons] at hlt
      omega

/--
The split-coprimality boundary data needed to initialise every quadratic split
in the balanced multifactor tree from factors modulo `p`.

In the non-singleton arm the factor list is split at `balancedSplitIndex`, and
the requirement is
that the normalised XGCD of the left lifted product
`Array.polyProduct ((L.map FpPoly.liftToZ).toArray)` against the right lifted
product `Array.polyProduct ((R.map FpPoly.liftToZ).toArray)` returns `gcd = 1`
in `FpPoly p`, and that the same coprimality holds recursively on each half.
The base cases (empty list, singleton) are vacuous.

Consumed by `quadraticMultifactorLiftInvariant_of_factorsModP`: the
per-split `gcd = 1` lifts via `normalizedXGCD_liftToZ_bezout_congr_of_gcd_eq_one`
into the Bezout half of `QuadraticLiftLoopInvariant`.
-/
@[expose]
def QuadraticMultifactorCoprimeSplits
    (p : Nat) [ZMod64.Bounds p] : List (FpPoly p) → Prop
  | [] => True
  | [_g] => True
  | g₀ :: g₁ :: rest =>
      let gs := g₀ :: g₁ :: rest
      let split := balancedSplitIndex (gs.map FpPoly.liftToZ)
      let L := gs.take split
      let R := gs.drop split
      let g := Array.polyProduct ((L.map FpPoly.liftToZ).toArray)
      let h := Array.polyProduct ((R.map FpPoly.liftToZ).toArray)
      let xgcd := normalizedXGCD p g h
      xgcd.gcd = (1 : FpPoly p) ∧
        QuadraticMultifactorCoprimeSplits p L ∧
          QuadraticMultifactorCoprimeSplits p R
  termination_by factors => factors.length
  decreasing_by
    all_goals
      simp only [List.length_take, List.length_drop, List.length_cons]
      have hpos := balancedSplitIndex_pos
        ((g₀ :: g₁ :: rest).map FpPoly.liftToZ)
      have hlt := balancedSplitIndex_lt_length
        ((g₀ :: g₁ :: rest).map FpPoly.liftToZ) (by simp)
      simp only [List.length_map, List.length_cons] at hlt
      omega

/-- Induction-on-`factors` correctness statement feeding
`multifactorLiftQuadratic_spec`: the ordered product of the lifted
factors is congruent to `f` modulo `p^k`, provided each recursive binary
split supplies the quadratic Hensel invariant package threaded by
`QuadraticMultifactorLiftInvariant`. -/
private theorem multifactorLiftQuadraticList_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors) :
    ZPoly.congr
      (Array.polyProduct (multifactorLiftQuadraticList p k f factors))
      f
      (p ^ k) := by
  induction f, factors using multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f =>
      rw [multifactorLiftQuadraticList, polyProduct_empty]
      rwa [QuadraticMultifactorLiftInvariant] at hinv
  | case2 f _g =>
      rw [multifactorLiftQuadraticList, polyProduct_singleton]
      exact ZPoly.congr_reduceModPow f p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  | case3 f g₀ g₁ rest =>
      rename_i ihL ihR
      simp only [QuadraticMultifactorLiftInvariant] at hinv
      obtain ⟨hstart, hinvL, hinvR⟩ := hinv
      have hcL := ihL hinvL
      have hcR := ihR hinvR
      rw [multifactorLiftQuadraticList, polyProduct_append]
      exact ZPoly.congr_trans _ _ _ (p ^ k)
        (ZPoly.congr_mul _ _ _ _ (p ^ k) hcL hcR)
        (henselLiftFactors_spec p k f _ _ _ _ hk hp hstart)

/--
The product of the lifted factors is congruent to `f` modulo `p^k`,
under the recursive precondition package consumed by the quadratic
multifactor lifting tree.

The lift-uniqueness companion (linear-vs-quadratic agreement after
canonicalisation) lives in `hex-hensel-mathlib`.
-/
theorem multifactorLiftQuadratic_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors.toList) :
    ZPoly.congr (Array.polyProduct (multifactorLiftQuadratic p k f factors))
      f (p ^ k) := by
  simpa [multifactorLiftQuadratic] using
    multifactorLiftQuadraticList_spec p k f factors.toList hk hp hinv

private theorem int_eq_of_congr_of_bounds
    {a b : Int} {m : Nat}
    (hcongr : (a - b) % (m : Int) = 0)
    (ha_nonneg : 0 ≤ a) (ha_lt : a < (m : Int))
    (hb_nonneg : 0 ≤ b) (hb_lt : b < (m : Int)) :
    a = b := by
  have hmod_eq : a % (m : Int) = b % (m : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hcongr
  rw [Int.emod_eq_of_lt ha_nonneg ha_lt, Int.emod_eq_of_lt hb_nonneg hb_lt] at hmod_eq
  exact hmod_eq

private theorem int_eq_zero_of_mod_zero_of_bounds
    {a : Int} {m : Nat}
    (hm : 1 < m)
    (hmod : a % (m : Int) = 0)
    (ha_nonneg : 0 ≤ a) (ha_lt : a < (m : Int)) :
    a = 0 := by
  exact int_eq_of_congr_of_bounds (by simpa using hmod)
    ha_nonneg ha_lt (by decide) (by exact_mod_cast (Nat.zero_lt_of_lt hm))

/--
If a bounded nonnegative cofactor `h` satisfies a coefficientwise congruence
`g * h ≡ f (mod m)` against monic `g` and `f`, then `h` is monic. The proof
compares the possible top coefficient of `g * h` with the top coefficient of
`f`; the coefficient bounds rule out wraparound modulo `m`.

Consumed by `monic_reduceModPow_of_congr_mul_monic_monic`, which specialises
this to the `reduceModPow`-canonicalised cofactor consumed by
`henselLiftQuadratic_h_monic`.
-/
theorem monic_of_congr_mul_monic_monic
    {g h f : Hex.ZPoly} {m : Nat}
    (hm : 1 < m)
    (hcongr : Hex.ZPoly.congr (g * h) f m)
    (hg_monic : Hex.DensePoly.Monic g)
    (hf_monic : Hex.DensePoly.Monic f)
    (hh_bound_lt : ∀ i, h.coeff i < Int.ofNat m)
    (hh_bound_nonneg : ∀ i, 0 ≤ h.coeff i)
    (hh_ne_zero : h ≠ 0) :
    Hex.DensePoly.Monic h := by
  have hg_ne_zero : g ≠ 0 := by
    intro hg_zero
    have hlead : Hex.DensePoly.leadingCoeff g = (0 : Int) := by
      rw [hg_zero]
      simp
    rw [hg_monic] at hlead
    omega
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hlead : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      rw [hf_zero]
      simp
    rw [hf_monic] at hlead
    omega
  have hg_pos : 0 < g.size := Hex.ZPoly.size_pos_of_ne_zero g hg_ne_zero
  have hh_pos : 0 < h.size := Hex.ZPoly.size_pos_of_ne_zero h hh_ne_zero
  have hf_pos : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero f hf_ne_zero
  let gTop := g.size - 1
  let hTop := h.size - 1
  let fTop := f.size - 1
  have hg_top : g.coeff gTop = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_pos]
    exact hg_monic
  have hf_top : f.coeff fTop = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_pos]
    exact hf_monic
  have hprod_size :
      (g * h).size = g.size + h.size - 1 :=
    Hex.ZPoly.mul_size_eq_top_succ_of_nonzero g h hg_pos hh_pos
  have hsum_not_gt : ¬ fTop < gTop + hTop := by
    intro hlt
    have hf_zero : f.coeff (gTop + hTop) = 0 := by
      apply Hex.DensePoly.coeff_eq_zero_of_size_le f
      unfold fTop at hlt
      omega
    have hprod_top :
        (g * h).coeff (gTop + hTop) = h.coeff hTop := by
      have htop := Hex.ZPoly.coeff_mul_top g h hg_pos hh_pos
      unfold gTop hTop
      rw [htop, hg_top]
      omega
    have hmod : h.coeff hTop % (m : Int) = 0 := by
      have hc := hcongr (gTop + hTop)
      rw [hprod_top, hf_zero] at hc
      simpa using hc
    have hlead_zero : h.coeff hTop = 0 :=
      int_eq_zero_of_mod_zero_of_bounds hm hmod
        (hh_bound_nonneg hTop) (hh_bound_lt hTop)
    have hlead_ne : h.coeff hTop ≠ 0 := by
      unfold hTop
      exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size h hh_pos
    exact hlead_ne hlead_zero
  have hsum_not_lt : ¬ gTop + hTop < fTop := by
    intro hlt
    have hprod_zero : (g * h).coeff fTop = 0 := by
      apply Hex.DensePoly.coeff_eq_zero_of_size_le (g * h)
      rw [hprod_size]
      unfold gTop hTop fTop at hlt
      omega
    have hbad : (0 : Int) = 1 := by
      have hc := hcongr fTop
      rw [hprod_zero, hf_top] at hc
      exact int_eq_of_congr_of_bounds hc
        (by decide) (by exact_mod_cast (Nat.zero_lt_of_lt hm))
        (by decide) (by exact_mod_cast hm)
    omega
  have hsum_eq : gTop + hTop = fTop := by omega
  have hprod_top_at_f :
      (g * h).coeff fTop = h.coeff hTop := by
    rw [← hsum_eq]
    change (g * h).coeff (g.size - 1 + (h.size - 1)) = h.coeff (h.size - 1)
    rw [Hex.ZPoly.coeff_mul_top g h hg_pos hh_pos]
    have hg_top' : g.coeff (g.size - 1) = (1 : Int) := by
      simpa [gTop] using hg_top
    rw [hg_top']
    omega
  have hlead_one : h.coeff hTop = (1 : Int) := by
    have hc := hcongr fTop
    rw [hprod_top_at_f, hf_top] at hc
    exact int_eq_of_congr_of_bounds hc
      (hh_bound_nonneg hTop) (hh_bound_lt hTop)
      (by decide) (by exact_mod_cast hm)
  rw [Hex.DensePoly.Monic, Hex.DensePoly.leadingCoeff_eq_coeff_last h hh_pos]
  unfold hTop at hlead_one
  exact hlead_one

/--
Specialisation of `monic_of_congr_mul_monic_monic` for cofactors already
canonicalised by `Hex.ZPoly.reduceModPow`; its coefficients automatically lie
in `[0, p^k)`.

Consumed by `henselLiftQuadratic_h_monic`, where the correctness congruence
`(lifted.g * lifted.h) ≡ f (mod p^k)` already supplies a `reduceModPow`-form
cofactor.
-/
theorem monic_reduceModPow_of_congr_mul_monic_monic
    {g h f : Hex.ZPoly} {p k : Nat}
    (hm : 1 < p ^ k)
    (hcongr : Hex.ZPoly.congr (g * Hex.ZPoly.reduceModPow h p k) f (p ^ k))
    (hg_monic : Hex.DensePoly.Monic g)
    (hf_monic : Hex.DensePoly.Monic f)
    (hh_ne_zero : Hex.ZPoly.reduceModPow h p k ≠ 0) :
    Hex.DensePoly.Monic (Hex.ZPoly.reduceModPow h p k) := by
  have hpos : 0 < p ^ k := Nat.zero_lt_of_lt hm
  have hpos_int : (0 : Int) < (p ^ k : Int) := by
    exact_mod_cast hpos
  apply monic_of_congr_mul_monic_monic hm hcongr hg_monic hf_monic
  · intro i
    rw [Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpos]
    exact Int.emod_lt_of_pos _ hpos_int
  · intro i
    rw [Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpos]
    exact Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hpos))
  · exact hh_ne_zero

/-- The exact lift's cofactor is canonicalised at its requested exponent. -/
private theorem liftExact_h_eq_reduce
    (p : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (k : Nat) (acc : QuadraticLiftResult) :
    ∃ raw, (liftExact p f k acc).h = ZPoly.reduceModPow raw p k := by
  rw [liftExact]
  split <;> simp only [reduceLift] <;> exact ⟨_, rfl⟩

/-- The lifted monic factor `lifted.g` produced by `henselLiftQuadratic` is
monic. The exact-exponent recursion preserves `Monic acc.g` via
`quadraticHenselStep_monic`; each `reduceModPow` cleanup preserves it via
`reduceModPow_monic_of_monic`.

Consumed (alongside `henselLiftQuadratic_h_monic`) by
`multifactorLiftQuadratic_each_monic` to discharge per-output monicness inside
the balanced split tree. -/
theorem henselLiftQuadratic_g_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    DensePoly.Monic (henselLiftQuadratic p k f g h s t).g := by
  exact (liftExact_invariant p f k { g, h, s, t } hk hp hinv).monic

/-- The lifted cofactor `lifted.h` produced by `henselLiftQuadratic` is monic
when `f` is monic. Derived from the cofactor monic lemma
`monic_reduceModPow_of_congr_mul_monic_monic` applied to the correctness congruence
`(lifted.g * lifted.h) ≡ f (mod p^k)` and `henselLiftQuadratic_g_monic`.

Consumed (alongside `henselLiftQuadratic_g_monic`) by
`multifactorLiftQuadratic_each_monic` to discharge per-output monicness inside
the balanced split tree. -/
theorem henselLiftQuadratic_h_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    DensePoly.Monic (henselLiftQuadratic p k f g h s t).h := by
  have hpk_gt_one : 1 < p ^ k := Nat.one_lt_pow (by omega : k ≠ 0) hp
  have hpk_pos : 0 < p ^ k := Nat.zero_lt_of_lt hpk_gt_one
  obtain ⟨raw, hraw⟩ := liftExact_h_eq_reduce p f k { g, h, s, t }
  have hg_monic_lifted :
      DensePoly.Monic (henselLiftQuadratic p k f g h s t).g :=
    henselLiftQuadratic_g_monic p k f g h s t hk hp hinv
  have hspec_let := henselLiftQuadratic_spec p k f g h s t hk hp hinv
  have hspec :
      ZPoly.congr
        ((henselLiftQuadratic p k f g h s t).g *
          (henselLiftQuadratic p k f g h s t).h) f (p ^ k) := hspec_let
  have hh_eq :
      (henselLiftQuadratic p k f g h s t).h =
        ZPoly.reduceModPow raw p k := by
    simpa [henselLiftQuadratic] using hraw
  have hcongr_form :
      ZPoly.congr
        ((henselLiftQuadratic p k f g h s t).g *
          ZPoly.reduceModPow raw p k) f (p ^ k) := by
    rw [← hh_eq]; exact hspec
  have hh_ne_zero : (henselLiftQuadratic p k f g h s t).h ≠ 0 := by
    intro hzero
    have hf_ne_zero : f ≠ 0 := by
      intro hf_z
      have hlead : DensePoly.leadingCoeff f = (0 : Int) := by
        rw [hf_z]; simp
      rw [hf_monic] at hlead
      omega
    have hf_pos : 0 < f.size := ZPoly.size_pos_of_ne_zero f hf_ne_zero
    have hf_top : f.coeff (f.size - 1) = (1 : Int) := by
      rw [← DensePoly.leadingCoeff_eq_coeff_last f hf_pos]
      exact hf_monic
    have hmul_zero :
        (henselLiftQuadratic p k f g h s t).g *
          (henselLiftQuadratic p k f g h s t).h = 0 := by
      rw [hzero, DensePoly.mul_comm_poly (S := Int)]
      exact DensePoly.zero_mul _
    have hspec_zero :
        ZPoly.congr (0 : ZPoly) f (p ^ k) := by
      rw [← hmul_zero]; exact hspec
    have hc := hspec_zero (f.size - 1)
    rw [DensePoly.coeff_zero, hf_top] at hc
    have hdvd : (p ^ k : Int) ∣ ((0 : Int) - 1) :=
      Int.dvd_of_emod_eq_zero hc
    have hdvd_one : (p ^ k : Int) ∣ (1 : Int) := by
      have : (p ^ k : Int) ∣ -(1 : Int) := by simpa using hdvd
      simpa using (Int.dvd_neg).mp this
    have hdvd_one_nat : p ^ k ∣ 1 := by
      have h := Int.ofNat_dvd.mp (by exact_mod_cast hdvd_one)
      exact h
    have : p ^ k = 1 := Nat.eq_one_of_dvd_one hdvd_one_nat
    omega
  have hh_red_ne_zero : ZPoly.reduceModPow raw p k ≠ 0 := by
    rw [← hh_eq]; exact hh_ne_zero
  have hmonic_reduce :
      DensePoly.Monic (ZPoly.reduceModPow raw p k) :=
    monic_reduceModPow_of_congr_mul_monic_monic
      (g := (henselLiftQuadratic p k f g h s t).g)
      (h := raw) (f := f) (p := p) (k := k)
      hpk_gt_one hcongr_form hg_monic_lifted hf_monic hh_red_ne_zero
  rw [hh_eq]; exact hmonic_reduce

/-- The left factor of the factor-only lift is monic. -/
theorem henselLiftFactors_fst_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    DensePoly.Monic (henselLiftFactors p k f g h s t).1 := by
  rw [henselLiftFactors_fst]
  exact henselLiftQuadratic_g_monic p k f g h s t hk hp hinv

/-- The right factor of the factor-only lift is monic when the target is. -/
theorem henselLiftFactors_snd_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticLiftLoopInvariant p f { g, h, s, t }) :
    DensePoly.Monic (henselLiftFactors p k f g h s t).2 := by
  rw [henselLiftFactors_snd]
  exact henselLiftQuadratic_h_monic p k f g h s t hk hp hf_monic hinv

/-- The constant polynomial `1` is monic. -/
theorem monic_one : DensePoly.Monic (1 : ZPoly) := by
  unfold DensePoly.Monic; simp

/-- A product of monic integer polynomials is monic. -/
theorem monic_mul {a b : ZPoly}
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b) :
    DensePoly.Monic (a * b) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp [DensePoly.Monic, DensePoly.leadingCoeff_zero] at ha
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hb; simp [DensePoly.Monic, DensePoly.leadingCoeff_zero] at hb
  unfold DensePoly.Monic at *
  rw [leadingCoeff_mul_of_nonzero a b ha0 hb0, ha, hb, Int.one_mul]

/-- The `Array.polyProduct` of a list of monic integer polynomials is monic.
Needed because a balanced split multiplies a whole half of the factor list into
each side of the binary Hensel step, so the leading factor is a product rather
than a single input factor. -/
theorem monic_polyProduct_toArray (l : List ZPoly)
    (h : ∀ g ∈ l, DensePoly.Monic g) :
    DensePoly.Monic (Array.polyProduct l.toArray) := by
  induction l with
  | nil => simpa using monic_one
  | cons g rest ih =>
      rw [polyProduct_cons_toArray]
      exact monic_mul (h g (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-- The lifted product splits across a list concatenation: multiplying the
lifted products of two halves equals the lifted product of the concatenation.
This is the algebraic content that lets a balanced split's two sub-products
recombine to the whole modular product. -/
theorem polyProduct_map_liftToZ_append
    (p : Nat) [ZMod64.Bounds p] (L R : List (FpPoly p)) :
    Array.polyProduct ((L.map FpPoly.liftToZ).toArray) *
      Array.polyProduct ((R.map FpPoly.liftToZ).toArray) =
    Array.polyProduct (((L ++ R).map FpPoly.liftToZ).toArray) := by
  rw [List.map_append,
    show ((L.map FpPoly.liftToZ ++ R.map FpPoly.liftToZ).toArray)
        = (L.map FpPoly.liftToZ).toArray ++ (R.map FpPoly.liftToZ).toArray from by simp,
    polyProduct_append]

/--
Build the recursive quadratic multifactor lift invariant from the natural
mod-`p` boundary facts. The caller supplies, for the list of `FpPoly p`
factors lifted via `FpPoly.liftToZ`:

* `hf_monic` and `hfactors_monic` — `f` and every factor is monic
  (each split's leading factor is monic; `f` itself is needed
  recursively as the doubling-loop's target stays monic);
* `hproduct_mod_p` — the lifted ordered product is congruent to `f` mod `p`
  (feeds the product half of `QuadraticLiftLoopInvariant`);
* `hcoprime : QuadraticMultifactorCoprimeSplits p factors` — every split's
  normalised XGCD has `gcd = 1` over `FpPoly p` (feeds the Bezout half
  via `normalizedXGCD_liftToZ_bezout_congr_of_gcd_eq_one`);
* `hnonempty` — the factor list is nonempty (rules out the vacuous base
  case which would force `congr 1 f (p^k)`).

The recursive tail re-establishes the same package using
`henselLiftQuadratic_h_congr_mod_base` for the lifted complementary factor
and `henselLiftQuadratic_h_monic` for its monicness.
-/
theorem quadraticMultifactorLiftInvariant_of_factorsModP
    (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : ZPoly) (factors : List (FpPoly p))
    (hp : 1 < p)
    (hk : 1 ≤ k)
    (hf_monic : DensePoly.Monic f)
    (hfactors_monic : ∀ g ∈ factors, DensePoly.Monic g)
    (hproduct_mod_p :
      ZPoly.congr
        (Array.polyProduct ((factors.map FpPoly.liftToZ).toArray))
        f p)
    (hcoprime : QuadraticMultifactorCoprimeSplits p factors)
    (hnonempty : factors ≠ []) :
    QuadraticMultifactorLiftInvariant p k f
      (factors.map FpPoly.liftToZ) := by
  induction factors using QuadraticMultifactorCoprimeSplits.induct (p := p)
      generalizing f with
  | case1 => exact absurd rfl hnonempty
  | case2 g => simp [QuadraticMultifactorLiftInvariant]
  | case3 g₀ g₁ rest gs split L R ihL ihR =>
      simp only [QuadraticMultifactorCoprimeSplits] at hcoprime
      obtain ⟨hgcd, hcopL, hcopR⟩ := hcoprime
      simp only [List.map_cons]
      rw [QuadraticMultifactorLiftInvariant]
      simp only [← List.map_cons, ← List.map_take, ← List.map_drop]
      have hLmonic :
          ∀ x ∈ (List.take (balancedSplitIndex
              ((g₀ :: g₁ :: rest).map FpPoly.liftToZ))
              (g₀ :: g₁ :: rest)).map FpPoly.liftToZ, DensePoly.Monic x := by
        intro x hx; rw [List.mem_map] at hx
        obtain ⟨g, hgL, rfl⟩ := hx
        exact FpPoly.monic_liftToZ_of_monic g hp
          (hfactors_monic g (List.mem_of_mem_take hgL))
      have hprod : ZPoly.congr
          (Array.polyProduct ((List.take (balancedSplitIndex
                ((g₀ :: g₁ :: rest).map FpPoly.liftToZ))
                (g₀ :: g₁ :: rest)).map FpPoly.liftToZ).toArray *
            Array.polyProduct ((List.drop (balancedSplitIndex
                ((g₀ :: g₁ :: rest).map FpPoly.liftToZ))
                (g₀ :: g₁ :: rest)).map FpPoly.liftToZ).toArray) f p := by
        rw [polyProduct_map_liftToZ_append, List.take_append_drop]
        exact hproduct_mod_p
      have hbez := normalizedXGCD_liftToZ_bezout_congr_of_gcd_eq_one p _ _ hgcd
      have hstart := QuadraticLiftLoopInvariant.of_product_bezout_monic hprod hbez
        (monic_polyProduct_toArray _ hLmonic)
      refine ⟨hstart, ?_, ?_⟩
      · refine ihL _ (henselLiftFactors_fst_monic p k f _ _ _ _ hk hp hstart)
          (fun g hg => hfactors_monic g (List.mem_of_mem_take hg))
          (ZPoly.congr_symm _ _ _
            (henselLiftFactors_fst_congr_mod_base p k f _ _ _ _ hk hp hstart))
          hcopL ?_
        show List.take (balancedSplitIndex
          ((g₀ :: g₁ :: rest).map FpPoly.liftToZ)) (g₀ :: g₁ :: rest) ≠ []
        apply List.ne_nil_of_length_pos
        simp only [List.length_take]
        have hpos := balancedSplitIndex_pos
          ((g₀ :: g₁ :: rest).map FpPoly.liftToZ)
        have hlen : 0 < (g₀ :: g₁ :: rest).length := by simp
        omega
      · refine ihR _ (henselLiftFactors_snd_monic p k f _ _ _ _ hk hp hf_monic hstart)
          (fun g hg => hfactors_monic g (List.mem_of_mem_drop hg))
          (ZPoly.congr_symm _ _ _
            (henselLiftFactors_snd_congr_mod_base p k f _ _ _ _ hk hp hstart))
          hcopR ?_
        show List.drop (balancedSplitIndex
          ((g₀ :: g₁ :: rest).map FpPoly.liftToZ)) (g₀ :: g₁ :: rest) ≠ []
        apply List.ne_nil_of_length_pos
        simp only [List.length_drop]
        have hlt := balancedSplitIndex_lt_length
          ((g₀ :: g₁ :: rest).map FpPoly.liftToZ) (by simp)
        simp only [List.length_map] at hlt
        omega

/-- The lengths of a list's `take`/`drop` split sum to the whole length. -/
private theorem length_take_add_drop {α : Type} (l : List α) (n : Nat) :
    (l.take n).length + (l.drop n).length = l.length := by
  simp only [List.length_take, List.length_drop]; omega

/-- Output length of `multifactorLiftQuadraticList` matches the input list length.
This is the structural fact used by indexed per-output statements such as
`multifactorLiftQuadraticList_each_congr_mod_base`. -/
private theorem multifactorLiftQuadraticList_toList_length
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) (factors : List ZPoly) :
    (multifactorLiftQuadraticList p k f factors).toList.length = factors.length := by
  induction f, factors using multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => simp [multifactorLiftQuadraticList]
  | case2 f _g => simp [multifactorLiftQuadraticList]
  | case3 f g₀ g₁ rest =>
      rename_i ihL ihR
      rw [multifactorLiftQuadraticList, Array.toList_append, List.length_append, ihL, ihR]
      exact length_take_add_drop _ _

/-- The `multifactorLiftQuadratic` output has one entry per input factor.
Used by the Mathlib-side injectivity wrapper to relate output array
indices to original modular-factor indices. -/
@[simp, grind =] theorem multifactorLiftQuadratic_size_eq_input
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) (factors : Array ZPoly) :
    (multifactorLiftQuadratic p k f factors).size = factors.size := by
  unfold multifactorLiftQuadratic
  rw [Array.size_eq_length_toList,
    multifactorLiftQuadraticList_toList_length, ← Array.size_eq_length_toList]

/-- The empty-input boundary of `multifactorLiftQuadratic`: no factors in,
no factors out. -/
@[simp, grind =] theorem multifactorLiftQuadratic_empty
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    multifactorLiftQuadratic p k f #[] = #[] := by
  simp [multifactorLiftQuadratic, multifactorLiftQuadraticList]

/-- The singleton-input boundary of `multifactorLiftQuadratic`: a single
factor input collapses to the target polynomial reduced modulo `p^k`. The
input factor is discarded because the only remaining lift target is `f` itself
under the trivial split `f = f * 1`. -/
@[simp, grind =] theorem multifactorLiftQuadratic_singleton
    (p k : Nat) [ZMod64.Bounds p] (f g : ZPoly) :
    multifactorLiftQuadratic p k f #[g] = #[ZPoly.reduceModPow f p k] := by
  simp [multifactorLiftQuadratic, multifactorLiftQuadraticList]

/-- Per-index congruence transports across a list concatenation, given that the
output/input prefixes have equal length. This is the index-bookkeeping surface
for the balanced tree's `L`-then-`R` output split. -/
private theorem congr_getD_append (p : Nat) (o1 o2 f1 f2 : List ZPoly)
    (hlen : o1.length = f1.length)
    (h1 : ∀ (i : Nat), ZPoly.congr (o1[i]?.getD 0) (f1[i]?.getD 0) p)
    (h2 : ∀ (i : Nat), ZPoly.congr (o2[i]?.getD 0) (f2[i]?.getD 0) p) :
    ∀ (i : Nat), ZPoly.congr ((o1 ++ o2)[i]?.getD 0) ((f1 ++ f2)[i]?.getD 0) p := by
  intro i
  by_cases hi : i < o1.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hlen ▸ hi)]
    exact h1 i
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_lt hi), hlen]
    exact h2 (i - f1.length)

/-- Helper: list-level per-output mod-`p` preservation, stated via `getD 0` to
avoid index-proof motive issues. Each entry of
`(multifactorLiftQuadraticList p k f factors).toList` is congruent modulo `p`
to the corresponding entry of `factors`. -/
private theorem multifactorLiftQuadraticList_each_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hfactors_monic : ∀ g ∈ factors, DensePoly.Monic g)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors)
    (hproduct : ZPoly.congr (Array.polyProduct factors.toArray) f p) :
    ∀ (i : Nat),
      ZPoly.congr
        ((multifactorLiftQuadraticList p k f factors).toList[i]?.getD 0)
        (factors[i]?.getD 0) p := by
  induction f, factors using multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => intro i; rw [multifactorLiftQuadraticList]; simp; exact ZPoly.congr_refl 0 p
  | case2 f _g =>
      intro i
      rw [multifactorLiftQuadraticList]
      match i with
      | 0 =>
          simp only [List.getElem?_cons_zero, Option.getD_some]
          have hg : ZPoly.congr _g f p := by
            simpa [Array.polyProduct] using hproduct
          have hred : ZPoly.congr (ZPoly.reduceModPow f p k) f p := by
            have h1 : ZPoly.congr (ZPoly.reduceModPow f p k) f (p ^ k) :=
              ZPoly.congr_reduceModPow f p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
            have h2 := congr_of_pow_le p 1 k _ _ hk h1
            simpa [Nat.pow_one] using h2
          exact ZPoly.congr_trans _ _ _ p hred (ZPoly.congr_symm _ _ _ hg)
      | Nat.succ i' => simp; exact ZPoly.congr_refl 0 p
  | case3 f g₀ g₁ rest gs half L R gg hh xg ss tt lifted ihL ihR =>
      simp only [QuadraticMultifactorLiftInvariant] at hinv
      obtain ⟨hstart, hinvL, hinvR⟩ := hinv
      have hg_monic := henselLiftFactors_fst_monic p k f _ _ _ _ hk hp hstart
      have hh_monic := henselLiftFactors_snd_monic p k f _ _ _ _ hk hp hf_monic hstart
      have hgc := henselLiftFactors_fst_congr_mod_base p k f _ _ _ _ hk hp hstart
      have hhc := henselLiftFactors_snd_congr_mod_base p k f _ _ _ _ hk hp hstart
      have ihL' := ihL hg_monic (fun q hq => hfactors_monic q (List.mem_of_mem_take hq))
        hinvL (ZPoly.congr_symm _ _ _ hgc)
      have ihR' := ihR hh_monic (fun q hq => hfactors_monic q (List.mem_of_mem_drop hq))
        hinvR (ZPoly.congr_symm _ _ _ hhc)
      have hlen := multifactorLiftQuadraticList_toList_length p k lifted.1 L
      have key := congr_getD_append p _ _ L R hlen ihL' ihR'
      rw [List.take_append_drop] at key
      intro i
      rw [multifactorLiftQuadraticList, Array.toList_append]
      exact key i

/-- Each output of `multifactorLiftQuadratic` is congruent modulo `p` to the
corresponding input factor, given the monic / lift-invariant / mod-`p` product
hypotheses of `quadraticMultifactorLiftInvariant_of_factorsModP`.

This is the per-output mod-`p` preservation surface consumed by the Mathlib
theorem `henselLiftData_liftedFactor_injective`: pairing it with
`Nodup` of the original modular factor list shows distinct lifted factors
remain distinct as integer polynomials.

The size equality `multifactorLiftQuadratic_size_eq_input` is the companion
fact relating output array indices to input array indices. -/
theorem multifactorLiftQuadratic_each_congr_mod_base
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hfactors_monic : ∀ g ∈ factors, DensePoly.Monic g)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors.toList)
    (hproduct : ZPoly.congr (Array.polyProduct factors) f p) :
    ∀ (i : Nat),
      ZPoly.congr
        ((multifactorLiftQuadratic p k f factors).toList[i]?.getD 0)
        (factors.toList[i]?.getD 0) p := by
  intro i
  have hfactors_monic_list : ∀ g ∈ factors.toList, DensePoly.Monic g := by
    intro g hg
    exact hfactors_monic g (by simpa using hg)
  have hproduct_list :
      ZPoly.congr (Array.polyProduct factors.toList.toArray) f p := by
    simpa using hproduct
  exact
    multifactorLiftQuadraticList_each_congr_mod_base p k f factors.toList hk hp
      hf_monic hfactors_monic_list hinv hproduct_list i

/-- Every factor produced by the quadratic multifactor list lift is monic,
provided the input invariant holds and `f` is monic. Per-output monicity is
threaded through the recursion on `factors` and feeds the public list-lift
correctness statement. -/
private theorem multifactorLiftQuadraticList_each_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors) :
    ∀ entry ∈ (multifactorLiftQuadraticList p k f factors).toList,
      DensePoly.Monic entry := by
  induction f, factors using multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => rw [multifactorLiftQuadraticList]; intro entry hmem; simp at hmem
  | case2 f _g =>
      rw [multifactorLiftQuadraticList]
      intro entry hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact reduceModPow_monic_of_monic p k' f hp hf_monic
  | case3 f g₀ g₁ rest =>
      rename_i ihL ihR
      simp only [QuadraticMultifactorLiftInvariant] at hinv
      obtain ⟨hstart, hinvL, hinvR⟩ := hinv
      have ihL' := ihL (henselLiftFactors_fst_monic p k f _ _ _ _ hk hp hstart) hinvL
      have ihR' := ihR (henselLiftFactors_snd_monic p k f _ _ _ _ hk hp hf_monic hstart) hinvR
      rw [multifactorLiftQuadraticList]
      intro entry hmem
      rw [Array.toList_append, List.mem_append] at hmem
      rcases hmem with h | h
      · exact ihL' entry h
      · exact ihR' entry h

/-- Every output of {name}`Hex.ZPoly.multifactorLiftQuadratic` is monic when the input
polynomial `f` is monic and the quadratic multifactor lift invariant package
holds.

The proof applies {name}`Hex.ZPoly.henselLiftFactors_fst_monic` and
{name}`Hex.ZPoly.henselLiftFactors_snd_monic` at each balanced split node,
providing the monicness fact used by the Mathlib-facing wrapper. -/
theorem multifactorLiftQuadratic_each_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : QuadraticMultifactorLiftInvariant p k f factors.toList) :
    ∀ i : Fin (multifactorLiftQuadratic p k f factors).size,
      DensePoly.Monic (multifactorLiftQuadratic p k f factors)[i] := by
  intro i
  have hmem :
      (multifactorLiftQuadratic p k f factors)[i] ∈
        (multifactorLiftQuadratic p k f factors).toList :=
    Array.getElem_mem_toList i.isLt
  exact multifactorLiftQuadraticList_each_monic p k f factors.toList hk hp
    hf_monic hinv _ hmem

end ZPoly

end Hex
