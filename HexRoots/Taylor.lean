/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Basic

public section

/-!
Exact Gaussian-dyadic Taylor expansion of an integer polynomial `p` at a
Gaussian-dyadic centre `z`. The result `#[c₀, …, c_n]` collects the
coefficients of `p(X + z) = Σ cₖ Xᵏ`, where

```
cₖ = Σ_{j ≥ k} binomial(j, k) · aⱼ · z^{j−k}
```

is computed *exactly* over `Dyadic[i]`, each `cₖ` a Gaussian dyadic. No
binomial coefficients are materialised: the expansion is produced by
repeated synthetic division (Horner passes) in a single mutable array,
`O(n²)` exact Gaussian-dyadic operations. This is the dominant cost of
every witness check in the library.
-/
namespace Hex

namespace GaussDyadic

/-- A natural multiple of a Gaussian dyadic. -/
@[expose] def nsmul (n : Nat) (w : GaussDyadic) : GaussDyadic :=
  mul (ofInt n) w

/-- A natural power of a Gaussian dyadic. -/
@[expose] def pow (z : GaussDyadic) : Nat → GaussDyadic
  | 0 => ofInt 1
  | n + 1 => mul (pow z n) z

@[simp] theorem add_zero (z : GaussDyadic) : add z (0, 0) = z := by
  cases z
  simp [add]

@[simp] theorem zero_add (z : GaussDyadic) : add (0, 0) z = z := by
  cases z
  simp [add]

theorem add_assoc (x y z : GaussDyadic) : add (add x y) z = add x (add y z) := by
  cases x; cases y; cases z
  simp [add, Dyadic.add_assoc]

theorem add_comm (x y : GaussDyadic) : add x y = add y x := by
  cases x; cases y
  simp [add, Dyadic.add_comm]

theorem add_cross (x y z w : GaussDyadic) :
    add (add x y) (add z w) = add (add x z) (add y w) := by
  rw [add_assoc x y, ← add_assoc y z w, add_comm y z,
    add_assoc z y w, ← add_assoc x z]

private theorem dyadic_sub_zero (x : Dyadic) : x - 0 = x := by
  rw [← Dyadic.toRat_inj, Dyadic.toRat_sub]
  rw [Rat.sub_eq_add_neg]
  simpa using Rat.add_zero x.toRat

@[simp] theorem mul_zero (z : GaussDyadic) : mul z (0, 0) = (0, 0) := by
  cases z
  simp [mul, dyadic_sub_zero]

@[simp] theorem zero_mul (z : GaussDyadic) : mul (0, 0) z = (0, 0) := by
  cases z
  simp [mul, dyadic_sub_zero]

@[simp] theorem mul_one (z : GaussDyadic) : mul z (ofInt 1) = z := by
  rcases z with ⟨x, y⟩
  unfold mul ofInt
  have h1 : Dyadic.ofInt 1 = (1 : Dyadic) := rfl
  rw [h1]
  simp [Dyadic.mul_one, dyadic_sub_zero]

@[simp] theorem one_mul (z : GaussDyadic) : mul (ofInt 1) z = z := by
  rcases z with ⟨x, y⟩
  unfold mul ofInt
  have h1 : Dyadic.ofInt 1 = (1 : Dyadic) := rfl
  rw [h1]
  simp [Dyadic.one_mul, dyadic_sub_zero]

theorem mul_add (x y z : GaussDyadic) : mul x (add y z) = add (mul x y) (mul x z) := by
  cases x; cases y; cases z
  apply Prod.ext <;>
    simp [mul, add, ← Dyadic.toRat_inj, Dyadic.toRat_add, Dyadic.toRat_sub,
      Dyadic.toRat_mul, Rat.sub_eq_add_neg, Rat.neg_add, Rat.mul_add] <;> ac_rfl

theorem add_mul (x y z : GaussDyadic) : mul (add x y) z = add (mul x z) (mul y z) := by
  cases x; cases y; cases z
  apply Prod.ext <;>
    simp [mul, add, ← Dyadic.toRat_inj, Dyadic.toRat_add, Dyadic.toRat_sub,
      Dyadic.toRat_mul, Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_mul] <;> ac_rfl

theorem mul_assoc (x y z : GaussDyadic) : mul (mul x y) z = mul x (mul y z) := by
  cases x; cases y; cases z
  apply Prod.ext <;>
    simp [mul, ← Dyadic.toRat_inj, Dyadic.toRat_add, Dyadic.toRat_sub,
      Dyadic.toRat_mul, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.neg_add, Rat.mul_neg, Rat.neg_mul, Rat.mul_assoc] <;> ac_rfl

theorem mul_comm (x y : GaussDyadic) : mul x y = mul y x := by
  cases x; cases y
  apply Prod.ext <;>
    simp [mul, Dyadic.mul_comm, Dyadic.add_comm]

@[simp] theorem pow_zero (z : GaussDyadic) : pow z 0 = ofInt 1 := rfl

@[simp] theorem pow_succ (z : GaussDyadic) (n : Nat) :
    pow z (n + 1) = mul (pow z n) z := rfl

theorem nsmul_add (m n : Nat) (z : GaussDyadic) :
    nsmul (m + n) z = add (nsmul m z) (nsmul n z) := by
  have h : ofInt (m + n) = add (ofInt m) (ofInt n) := by
    change (((m + n : Nat) : Dyadic), (0 : Dyadic)) =
      add (((m : Nat) : Dyadic), (0 : Dyadic)) (((n : Nat) : Dyadic), (0 : Dyadic))
    apply Prod.ext <;>
      simp [add, ← Dyadic.toRat_inj, Dyadic.toRat_add,
        Dyadic.toRat_natCast, Rat.natCast_add]
  unfold nsmul
  have hi : (↑(m + n) : Int) = ↑m + ↑n := by omega
  rw [hi, h, add_mul]

@[simp] theorem nsmul_one (z : GaussDyadic) : nsmul 1 z = z := by
  simp [nsmul]

theorem mul_nsmul (x y : GaussDyadic) (n : Nat) :
    mul x (nsmul n y) = nsmul n (mul x y) := by
  simp only [nsmul]
  rw [← mul_assoc, mul_comm x (ofInt n), mul_assoc]

theorem mul_term (z a : GaussDyadic) (n r : Nat) :
    mul z (nsmul n (mul a (pow z r))) =
      nsmul n (mul a (pow z (r + 1))) := by
  rw [mul_nsmul, pow_succ, ← mul_assoc, mul_comm z a, mul_assoc]
  rw [mul_comm z (pow z r)]

end GaussDyadic

/-- Sum `f 0 + ⋯ + f (n-1)` using named Gaussian-dyadic addition. -/
@[expose] def gaussSum (n : Nat) (f : Nat → GaussDyadic) : GaussDyadic :=
  (List.range n).foldl (fun s i => GaussDyadic.add s (f i)) (0, 0)

@[simp] theorem gaussSum_zero (f : Nat → GaussDyadic) : gaussSum 0 f = (0, 0) := rfl

theorem gaussSum_succ (n : Nat) (f : Nat → GaussDyadic) :
    gaussSum (n + 1) f = GaussDyadic.add (gaussSum n f) (f n) := by
  simp [gaussSum, List.range_succ, List.foldl_append]

theorem gaussSum_add (n : Nat) (f g : Nat → GaussDyadic) :
    gaussSum n (fun i => GaussDyadic.add (f i) (g i)) =
      GaussDyadic.add (gaussSum n f) (gaussSum n g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [gaussSum_succ, gaussSum_succ, gaussSum_succ, ih]
      simp only [GaussDyadic.add_assoc]
      rw [← GaussDyadic.add_assoc (gaussSum n g) (f n) (g n),
        GaussDyadic.add_comm (gaussSum n g) (f n), GaussDyadic.add_assoc]

theorem mul_gaussSum (z : GaussDyadic) (n : Nat) (f : Nat → GaussDyadic) :
    GaussDyadic.mul z (gaussSum n f) =
      gaussSum n (fun i => GaussDyadic.mul z (f i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [gaussSum_succ, GaussDyadic.mul_add, ih, gaussSum_succ]

theorem gaussSum_head (n : Nat) (f : Nat → GaussDyadic) :
    gaussSum (n + 1) f =
      GaussDyadic.add (f 0) (gaussSum n (fun i => f (i + 1))) := by
  induction n with
  | zero => simp [gaussSum_succ]
  | succ n ih =>
      rw [gaussSum_succ, ih, gaussSum_succ, GaussDyadic.add_assoc]

/-- The coefficient sequence after `k` synthetic-division passes, abstracted
    from arrays. Pass zero is the original leading coefficient; later passes
    have the corresponding Pascal-row finite sum. -/
private def taylorStage (z : GaussDyadic) (a : Nat → GaussDyadic) :
    Nat → Nat → GaussDyadic
  | 0, _ => a 0
  | k + 1, n =>
      gaussSum n fun r =>
        GaussDyadic.nsmul (Hex.Nat.choose (r + k) r)
          (GaussDyadic.mul (a r) (GaussDyadic.pow z r))

/-- One synthetic-division update advances the abstract coefficient sequence
    by one Pascal row. -/
private theorem taylorStage_step (z : GaussDyadic) (a : Nat → GaussDyadic)
    (k n : Nat) :
    taylorStage z a (k + 1) (n + 1) =
      GaussDyadic.add (taylorStage z a k (n + 1))
        (GaussDyadic.mul z (taylorStage z (fun r => a (r + 1)) (k + 1) n)) := by
  cases k with
  | zero =>
      simp only [Nat.zero_add]
      simp only [taylorStage]
      rw [gaussSum_head]
      simp only [Hex.Nat.choose_self, GaussDyadic.nsmul_one, GaussDyadic.pow_zero,
        GaussDyadic.mul_one]
      congr 1
      rw [mul_gaussSum]
      apply congrArg (gaussSum n)
      funext r
      simpa [taylorStage] using
        (GaussDyadic.mul_term z (a (r + 1)) 1 r).symm
  | succ k =>
      induction n with
      | zero =>
          simp [taylorStage, gaussSum_succ]
      | succ n ih =>
          simp only [taylorStage] at ih ⊢
          rw [gaussSum_succ] at ih ⊢
          rw [gaussSum_succ]
          rw [ih]
          rw [gaussSum_succ]
          rw [gaussSum_succ]
          rw [gaussSum_succ]
          rw [gaussSum_succ]
          rw [GaussDyadic.mul_add, GaussDyadic.mul_term]
          have hchoose :
              Hex.Nat.choose (n + 1 + (k + 1)) (n + 1) =
                Hex.Nat.choose (n + 1 + k) (n + 1) +
                  Hex.Nat.choose (n + (k + 1)) n := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Hex.Nat.choose_succ_succ (n + k + 1) n)
          rw [hchoose, GaussDyadic.nsmul_add]
          exact GaussDyadic.add_cross _ _ _ _

private theorem taylorStage_one (z : GaussDyadic) (a : Nat → GaussDyadic) (k : Nat) :
    taylorStage z a k 1 = a 0 := by
  cases k with
  | zero => rfl
  | succ k =>
      simp [taylorStage, gaussSum_succ]

namespace Taylor

/-- Initial coefficient array for Taylor expansion. -/
@[expose] def init (p : ZPoly) : Array GaussDyadic :=
  ((List.range p.size).map fun i => GaussDyadic.ofInt (p.coeff i)).toArray

/-- One in-place synthetic-division pass.

The Taylor implementation calls this with `n = p.size`; the separate argument keeps the
inner fold independent of the polynomial representation.
-/
@[expose] def pass (n : Nat) (z : GaussDyadic)
    (a : Array GaussDyadic) (k : Nat) : Array GaussDyadic :=
  (List.range ((n - 1) - k)).foldl (init := a) fun a jr =>
    let j := n - 2 - jr
    a.setIfInBounds j
      (GaussDyadic.add (a.getD j (0, 0)) (GaussDyadic.mul z (a.getD (j + 1) (0, 0))))

end Taylor

/-- Abstract value at array index `i` after `k` Taylor passes. -/
private def coeffStage (p : ZPoly) (z : GaussDyadic) (k i : Nat) : GaussDyadic :=
  taylorStage z (fun r => GaussDyadic.ofInt (p.coeff (i + r))) k (p.size - i)

private theorem coeffStage_step (p : ZPoly) (z : GaussDyadic) (k i : Nat)
    (hi : i + 1 < p.size) :
    coeffStage p z (k + 1) i =
      GaussDyadic.add (coeffStage p z k i)
        (GaussDyadic.mul z (coeffStage p z (k + 1) (i + 1))) := by
  unfold coeffStage
  have hlen : p.size - i = (p.size - (i + 1)) + 1 := by omega
  rw [hlen, taylorStage_step]
  have hf :
      (fun r => GaussDyadic.ofInt (p.coeff (i + (r + 1)))) =
        (fun r => GaussDyadic.ofInt (p.coeff (i + 1 + r))) := by
    funext r
    congr 2
    omega
  rw [hf]

private theorem coeffStage_last (p : ZPoly) (z : GaussDyadic) (k : Nat)
    {i : Nat} (hi : i + 1 = p.size) :
    coeffStage p z k i = GaussDyadic.ofInt (p.coeff i) := by
  unfold coeffStage
  have : p.size - i = 1 := by omega
  rw [this, taylorStage_one]
  simp

private def AtStage (p : ZPoly) (z : GaussDyadic) (k : Nat)
    (a : Array GaussDyadic) : Prop :=
  a.size = p.size ∧
    ∀ i, k ≤ i → i < p.size → a.getD i (0, 0) = coeffStage p z k i

private theorem init_atStage (p : ZPoly) (z : GaussDyadic) :
    AtStage p z 0 (Taylor.init p) := by
  constructor
  · simp [Taylor.init]
  · intro i _ hi
    simp [Taylor.init, coeffStage, taylorStage, hi]

private theorem pass_atStage (p : ZPoly) (z : GaussDyadic) (k : Nat)
    (a : Array GaussDyadic) (ha : AtStage p z k a) :
    (Taylor.pass p.size z a k).size = p.size ∧
      ∀ i, k ≤ i → i < p.size →
        (Taylor.pass p.size z a k).getD i (0, 0) = coeffStage p z (k + 1) i := by
  let m := (p.size - 1) - k
  let step : Array GaussDyadic → Nat → Array GaussDyadic := fun b jr =>
    let j := p.size - 2 - jr
    b.setIfInBounds j
      (GaussDyadic.add (b.getD j (0, 0))
        (GaussDyadic.mul z (b.getD (j + 1) (0, 0))))
  have hloop : ∀ r, r ≤ m →
      let b := (List.range r).foldl step a
      b.size = p.size ∧ ∀ i, k ≤ i → i < p.size →
        b.getD i (0, 0) =
          if p.size - 1 - r ≤ i then coeffStage p z (k + 1) i
          else coeffStage p z k i := by
    intro r hr
    induction r with
    | zero =>
        dsimp
        constructor
        · exact ha.1
        · intro i hki hi
          rw [ha.2 i hki hi]
          split <;> rename_i h
          · have hilast : i + 1 = p.size := by omega
            rw [coeffStage_last p z k hilast, coeffStage_last p z (k + 1) hilast]
          · rfl
    | succ r ih =>
        have hrm : r ≤ m := by omega
        have ih' := ih hrm
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        let b := (List.range r).foldl step a
        let j := p.size - 2 - r
        have hbsize : b.size = p.size := ih'.1
        have hjlt : j < p.size := by
          dsimp [j, m] at ⊢
          omega
        change (step b r).size = p.size ∧ ∀ i, k ≤ i → i < p.size →
          (step b r).getD i (0, 0) =
            if p.size - 1 - (r + 1) ≤ i then coeffStage p z (k + 1) i
            else coeffStage p z k i
        constructor
        · rw [show (step b r).size = b.size by simp [step, Array.size_setIfInBounds], hbsize]
        · intro i hki hi
          have hjki : k ≤ j := by
            dsimp [j, m] at ⊢
            omega
          have hj1lt : j + 1 < p.size := by
            dsimp [j, m] at ⊢
            omega
          by_cases hij : i = j
          · subst i
            have hget : (step b r).getD j (0, 0) =
                GaussDyadic.add (b.getD j (0, 0))
                  (GaussDyadic.mul z (b.getD (j + 1) (0, 0))) := by
              unfold step
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt]
              · rfl
              · simpa [hbsize] using hjlt
            rw [hget, ih'.2 j hjki hjlt, ih'.2 (j + 1) (by omega) hj1lt]
            have hjold : ¬ p.size - 1 - r ≤ j := by
              dsimp [j]
              omega
            have hj1new : p.size - 1 - r ≤ j + 1 := by
              dsimp [j]
              omega
            rw [if_neg hjold, if_pos hj1new, ← coeffStage_step p z k j hj1lt]
            rw [if_pos]
            dsimp [j]
            omega
          · have hget : (step b r).getD i (0, 0) = b.getD i (0, 0) := by
              unfold step
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne]
              · rw [← Array.getD_eq_getD_getElem?]
              · exact Ne.symm hij
            rw [hget, ih'.2 i hki hi]
            have hiff : p.size - 1 - (r + 1) ≤ i ↔ p.size - 1 - r ≤ i := by
              dsimp [j] at hij
              omega
            split <;> rename_i h
            · rw [if_pos (hiff.mpr h)]
            · rw [if_neg (fun h' => h (hiff.mp h'))]
  unfold Taylor.pass
  have hm := hloop m (Nat.le_refl m)
  constructor
  · exact hm.1
  · intro i hki hi
    rw [hm.2 i hki hi]
    rw [if_pos]
    dsimp [m]
    omega

private theorem pass_getD_of_lt (n : Nat) (z : GaussDyadic) (a : Array GaussDyadic)
    {i k : Nat} (hik : i < k) :
    (Taylor.pass n z a k).getD i (0, 0) = a.getD i (0, 0) := by
  let m := (n - 1) - k
  let step : Array GaussDyadic → Nat → Array GaussDyadic := fun b jr =>
    let j := n - 2 - jr
    b.setIfInBounds j
      (GaussDyadic.add (b.getD j (0, 0))
        (GaussDyadic.mul z (b.getD (j + 1) (0, 0))))
  have hloop : ∀ r, r ≤ m →
      ((List.range r).foldl step a).getD i (0, 0) = a.getD i (0, 0) := by
    intro r hr
    induction r with
    | zero => rfl
    | succ r ih =>
        have hrm : r ≤ m := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, step]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne]
        · rw [← Array.getD_eq_getD_getElem?, ih hrm]
        · dsimp [m] at hr
          omega
  unfold Taylor.pass
  exact hloop m (Nat.le_refl m)

private def FullStage (p : ZPoly) (z : GaussDyadic) (k : Nat)
    (a : Array GaussDyadic) : Prop :=
  a.size = p.size ∧ ∀ i, i < p.size →
    a.getD i (0, 0) =
      if i < k then coeffStage p z (i + 1) i else coeffStage p z k i

private theorem init_fullStage (p : ZPoly) (z : GaussDyadic) :
    FullStage p z 0 (Taylor.init p) := by
  constructor
  · exact (init_atStage p z).1
  · intro i hi
    rw [(init_atStage p z).2 i (Nat.zero_le _) hi]
    simp

private theorem pass_fullStage (p : ZPoly) (z : GaussDyadic) (k : Nat)
    (a : Array GaussDyadic) (ha : FullStage p z k a) :
    FullStage p z (k + 1) (Taylor.pass p.size z a k) := by
  have hastage : AtStage p z k a := by
    constructor
    · exact ha.1
    · intro i hki hi
      rw [ha.2 i hi, if_neg (by omega)]
  have hadv := pass_atStage p z k a hastage
  constructor
  · exact hadv.1
  · intro i hi
    by_cases hik : i < k
    · rw [pass_getD_of_lt p.size z a hik, ha.2 i hi, if_pos hik,
        if_pos (by omega)]
    · rw [hadv.2 i (by omega) hi]
      by_cases hEq : i = k
      · subst i
        simp
      · rw [if_neg (by omega)]

private theorem fold_fullStage (p : ZPoly) (z : GaussDyadic) : ∀ r, r ≤ p.size →
    FullStage p z r
      ((List.range r).foldl (Taylor.pass p.size z) (Taylor.init p)) := by
  intro r hr
  induction r with
  | zero => exact init_fullStage p z
  | succ r ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact pass_fullStage p z r _ (ih (by omega))

/-- Closed-form coefficient of `X^k` in the Taylor shift. The range index
    `r` represents the source coefficient at `j = k + r`. -/
@[expose] def taylorCoeff (p : ZPoly) (z : GaussDyadic) (k : Nat) : GaussDyadic :=
  gaussSum (p.size - k) fun r =>
    GaussDyadic.nsmul (Hex.Nat.binom (k + r) k)
      (GaussDyadic.mul (GaussDyadic.ofInt (p.coeff (k + r))) (GaussDyadic.pow z r))

private theorem coeffStage_final (p : ZPoly) (z : GaussDyadic) (k : Nat) :
    coeffStage p z (k + 1) k = taylorCoeff p z k := by
  unfold coeffStage taylorCoeff taylorStage
  apply congrArg (gaussSum (p.size - k))
  funext r
  congr 2
  · rw [Hex.Nat.binom_eq_choose]
    have hsym := Hex.Nat.choose_symm (n := k + r) (k := k) (Nat.le_add_right k r)
    simpa [Nat.add_comm] using hsym

/-- Exact Taylor coefficients of `p` at the Gaussian-dyadic point `z`:
    returns `#[c₀, …, c_n]` with `p(X + z) = Σ cₖ Xᵏ`, where
    `cₖ = Σ_{j ≥ k} binomial(j, k) · aⱼ · z^{j−k}` exactly. The result has
    size `p.size` (empty for the zero polynomial, a single cast coefficient
    for a nonzero constant). Computed by repeated synthetic division, using
    only exact Gaussian-dyadic additions and multiplications. -/
@[expose] def taylor (p : ZPoly) (z : GaussDyadic) : Array GaussDyadic :=
  let n := p.size
  -- The single mutable array: initially the integer coefficients cast into
  -- `GaussDyadic`, then rewritten in place by the synthetic-division passes.
  let a₀ := Taylor.init p
  -- Pass `k` finalises `a[k]`: after it, `a[k]` is the Taylor coefficient `cₖ`.
  -- Pass `k`'s inner loop runs `j` from `n − 2` down to `k` (as `j = n − 2 − jr`
  -- for `jr` in `[0, (n−1)−k)`), applying one synthetic-division step
  -- `a[j] := a[j] + z·a[j+1]`. For `n ≤ 1` both loops are empty (`List.range n`
  -- is `[]` or `[0]` and the inner range `List.range ((n−1)−k)` is `[]`), so the
  -- result is just the cast coefficients. For `k = n − 1` the inner range is
  -- empty (`Nat` subtraction gives `0`), a no-op.
  (List.range n).foldl (init := a₀) (Taylor.pass n z)

/-- A `List.foldl` whose step function preserves array size preserves the
    size of the accumulator. Used to see through the synthetic-division loop
    in `taylor`, whose only mutation is `Array.setIfInBounds`. -/
private theorem size_foldl {β : Type _} {f : Array GaussDyadic → β → Array GaussDyadic}
    (hf : ∀ b x, (f b x).size = b.size) (l : List β) (a : Array GaussDyadic) :
    (l.foldl f a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons _ tl ih => simp only [List.foldl_cons, ih, hf]

/-- The Taylor expansion has one coefficient per stored coefficient of `p`:
    the synthetic-division passes only overwrite entries of the initial
    length-`p.size` array, never resize it. -/
theorem taylor_size (p : ZPoly) (z : GaussDyadic) : (taylor p z).size = p.size := by
  unfold taylor Taylor.pass
  rw [size_foldl (fun b x => size_foldl (fun _ _ => Array.size_setIfInBounds ..) _ b)]
  simp [Taylor.init]

/-- Characterization of a Taylor coefficient as the finite binomial sum
    `Σ_r binom(k+r,k) · a_(k+r) · z^r`. -/
theorem taylor_getD (p : ZPoly) (z : GaussDyadic) (k : Nat) :
    (taylor p z).getD k (0, 0) =
      if k < p.size then taylorCoeff p z k else (0, 0) := by
  have hfull : FullStage p z p.size (taylor p z) := by
    simpa [taylor] using fold_fullStage p z p.size (Nat.le_refl _)
  by_cases hk : k < p.size
  · rw [hfull.2 k hk, if_pos hk, if_pos hk, coeffStage_final]
  · rw [if_neg hk, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [taylor_size]; omega)]
    rfl

/-- In-bounds form of `taylor_getD`, convenient for companion proofs. -/
theorem taylor_getD_of_lt (p : ZPoly) (z : GaussDyadic) (k : Nat) (hk : k < p.size) :
    (taylor p z).getD k (0, 0) = taylorCoeff p z k := by
  simpa [hk] using taylor_getD p z k

end Hex
