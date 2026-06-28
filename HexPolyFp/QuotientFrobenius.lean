/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Quotient
public import HexPolyFp.SquareFree

public section

/-!
Quotient-side Frobenius properties for `F_p[X] / (g)`.

This module proves that the Frobenius iterate `β ↦ β ^ (p ^ n)` on the
quotient is an `F_p`-algebra endomorphism, derives the constant Fermat
identity, and packages the X-generation theorem: a single fixed point
at `Quotient.X` upgrades to a universal fixed point.
-/

namespace Hex
namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

namespace Quotient

variable {g : FpPoly p} {hmonic : DensePoly.Monic g}
variable {hg_pos : 0 < g.degree?.getD 0}

/-- A quotient sum equals the reduction of the underlying polynomial sum. -/
theorem add_eq_reduce_val (a b : Quotient g hmonic hg_pos) :
    a + b =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (a.val + b.val) := by
  apply ext
  show FpPoly.modByMonic g (a.val + b.val) hmonic =
    FpPoly.modByMonic g (a.val + b.val) hmonic
  rfl

/-- A quotient product equals the reduction of the underlying polynomial
product. -/
theorem mul_eq_reduce_val (a b : Quotient g hmonic hg_pos) :
    a * b =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (a.val * b.val) := by
  apply ext
  show FpPoly.modByMonic g (a.val * b.val) hmonic =
    FpPoly.modByMonic g (a.val * b.val) hmonic
  rfl

/-- Power of a product factors out in the quotient. -/
theorem mul_pow (a b : Quotient g hmonic hg_pos) (n : Nat) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
      change (a * b) ^ (0 : Nat) = a ^ (0 : Nat) * b ^ (0 : Nat)
      rw [pow_zero, pow_zero, pow_zero, one_mul]
  | succ n ih =>
      calc (a * b) ^ (n + 1)
          = (a * b) ^ n * (a * b) := by rw [pow_succ]
        _ = (a ^ n * b ^ n) * (a * b) := by rw [ih]
        _ = a ^ n * (b ^ n * (a * b)) := mul_assoc _ _ _
        _ = a ^ n * ((b ^ n * a) * b) := by rw [mul_assoc (b ^ n) a b]
        _ = a ^ n * ((a * b ^ n) * b) := by rw [mul_comm (b ^ n) a]
        _ = a ^ n * (a * (b ^ n * b)) := by rw [mul_assoc a (b ^ n) b]
        _ = (a ^ n * a) * (b ^ n * b) := (mul_assoc _ _ _).symm
        _ = a ^ (n + 1) * b ^ (n + 1) := by rw [pow_succ, pow_succ]

/-- For any quotient element `a` and exponent `n`, the `n`th power of `a`
equals the reduction of the polynomial-level `n`th power of its
representative. -/
theorem pow_eq_reduce_linearPow (a : Quotient g hmonic hg_pos) (n : Nat) :
    a ^ n =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (FpPoly.linearPow a.val n) := by
  rw [reduce_linearPow_eq_pow, reduce_val_self]

/-- Freshman's dream on the quotient (prime case): raising a sum to the
characteristic distributes additively. -/
theorem add_pow_prime (a b : Quotient g hmonic hg_pos) :
    (a + b) ^ p = a ^ p + b ^ p := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  rw [add_eq_reduce_val a b]
  rw [show (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (a.val + b.val)) ^ p =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (FpPoly.linearPow (a.val + b.val) p) from
    (reduce_linearPow_eq_pow (a.val + b.val) p).symm]
  rw [FpPoly.linearPow_add_prime hp]
  rw [reduce_add]
  rw [pow_eq_reduce_linearPow a, pow_eq_reduce_linearPow b]

omit [ZMod64.PrimeModulus p] in
private theorem zmod64_pow_succ (c : ZMod64 p) (n : Nat) :
    c ^ (n + 1) = c ^ n * c := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  show (c ^ (n + 1)).toNat = (c ^ n * c).toNat
  rw [show ((c ^ n * c) : ZMod64 p) = ZMod64.mul (c ^ n) c from rfl,
    ZMod64.toNat_mul]
  rw [show (c ^ (n + 1) : ZMod64 p) = ZMod64.pow c (n + 1) from rfl]
  rw [show (c ^ n : ZMod64 p) = ZMod64.pow c n from rfl]
  rw [ZMod64.toNat_pow, ZMod64.toNat_pow]
  have hc_lt : c.toNat < p := c.toNat_lt
  have hcm : c.toNat % p = c.toNat := Nat.mod_eq_of_lt hc_lt
  rw [Nat.pow_succ, Nat.mul_mod, hcm]

/-- Freshman's dream on the quotient, iterated: raising a sum to `p ^ k`
distributes additively for every `k`. -/
theorem add_pow_pPow (a b : Quotient g hmonic hg_pos) (k : Nat) :
    (a + b) ^ (p ^ k) = a ^ (p ^ k) + b ^ (p ^ k) := by
  induction k with
  | zero =>
      change (a + b) ^ (1 : Nat) = a ^ (1 : Nat) + b ^ (1 : Nat)
      rw [show (1 : Nat) = 0 + 1 from rfl, pow_succ, pow_zero, one_mul,
        pow_succ, pow_zero, one_mul, pow_succ, pow_zero, one_mul]
  | succ k ih =>
      calc (a + b) ^ (p ^ (k + 1))
          = (a + b) ^ (p ^ k * p) := by rw [Nat.pow_succ]
        _ = ((a + b) ^ (p ^ k)) ^ p := by rw [pow_mul]
        _ = (a ^ (p ^ k) + b ^ (p ^ k)) ^ p := by rw [ih]
        _ = (a ^ (p ^ k)) ^ p + (b ^ (p ^ k)) ^ p := add_pow_prime _ _
        _ = a ^ (p ^ k * p) + b ^ (p ^ k * p) := by
              rw [pow_mul, pow_mul]
        _ = a ^ (p ^ (k + 1)) + b ^ (p ^ (k + 1)) := by rw [Nat.pow_succ]

omit [ZMod64.PrimeModulus p] in
private theorem fpPoly_C_mul_C (c d : ZMod64 p) :
    (DensePoly.C c : FpPoly p) * DensePoly.C d = DensePoly.C (c * d) := by
  rw [FpPoly.C_mul_eq_scale]
  rw [show (DensePoly.C d : FpPoly p) = DensePoly.scale d (1 : FpPoly p) from
    (FpPoly.scale_one_poly d).symm]
  rw [FpPoly.scale_scale, FpPoly.scale_one_poly]

omit [ZMod64.PrimeModulus p] in
private theorem fpPoly_one_eq_C_one :
    (1 : FpPoly p) = DensePoly.C (1 : ZMod64 p) :=
  rfl

omit [ZMod64.PrimeModulus p] in
private theorem zmod64_pow_zero (c : ZMod64 p) :
    c ^ (0 : Nat) = (1 : ZMod64 p) := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  show (c ^ (0 : Nat) : ZMod64 p).toNat = (1 : ZMod64 p).toNat
  rw [show ((c ^ (0 : Nat)) : ZMod64 p) = ZMod64.pow c 0 from rfl]
  rw [ZMod64.toNat_pow]
  rw [show ((1 : ZMod64 p) : ZMod64 p) = ZMod64.one from rfl, ZMod64.toNat_one]
  simp

omit [ZMod64.PrimeModulus p] in
private theorem linearPow_C (c : ZMod64 p) (n : Nat) :
    FpPoly.linearPow (DensePoly.C c : FpPoly p) n =
      DensePoly.C (c ^ n) := by
  induction n with
  | zero =>
      rw [FpPoly.linearPow_zero, zmod64_pow_zero]
      exact fpPoly_one_eq_C_one
  | succ n ih =>
      rw [FpPoly.linearPow_succ, ih, fpPoly_C_mul_C, ← zmod64_pow_succ]

/-- `linearPow (C c) p = C c` over `F_p`: Fermat for constants in
characteristic `p`. -/
theorem linearPow_C_pow_prime (c : ZMod64 p) :
    FpPoly.linearPow (DensePoly.C c : FpPoly p) p = DensePoly.C c := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  rw [linearPow_C, ZMod64.pow_prime hp]

/-- Constants are fixed by the prime-power Frobenius on the quotient. -/
theorem reduce_C_pow_prime_eq (c : ZMod64 p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c)) ^ p =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) := by
  rw [← reduce_linearPow_eq_pow]
  rw [linearPow_C_pow_prime]

/-- Constants are fixed by every iterate of the Frobenius on the quotient. -/
theorem reduce_C_pow_pPow_eq (c : ZMod64 p) (k : Nat) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c)) ^
        (p ^ k) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) := by
  induction k with
  | zero =>
      change (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C c)) ^ (1 : Nat) = _
      rw [show (1 : Nat) = 0 + 1 from rfl, pow_succ, pow_zero, one_mul]
  | succ k ih =>
      calc (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (DensePoly.C c)) ^ (p ^ (k + 1))
          = (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (DensePoly.C c)) ^ (p ^ k * p) := by rw [Nat.pow_succ]
        _ = ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (DensePoly.C c)) ^ (p ^ k)) ^ p := by rw [pow_mul]
        _ = (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (DensePoly.C c)) ^ p := by rw [ih]
        _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (DensePoly.C c) := reduce_C_pow_prime_eq c

/-- Iterated Frobenius is the identity on `Quotient.X` powers, given a fixed
point at `Quotient.X` itself. -/
theorem X_pow_pPowN (hp_pos : 0 < p) {n : Nat}
    (hX : (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (p ^ n) =
            X (g := g) (hmonic := hmonic) (hg_pos := hg_pos))
    (m : Nat) :
    ((X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ m) ^ (p ^ n) =
      (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ m := by
  induction m with
  | zero =>
      change ((X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (0 : Nat)) ^
          (p ^ n) = _
      rw [pow_zero]
      have hpos : 0 < p ^ n := Nat.pow_pos hp_pos
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos) with ⟨k, hk⟩
      rw [hk, pow_succ]
      rw [show ((1 : Quotient g hmonic hg_pos) ^ k) = 1 by
        clear hX hk
        induction k with
        | zero => rfl
        | succ k ih => rw [pow_succ, ih, one_mul]]
      rw [one_mul]
  | succ m ih =>
      calc ((X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (m + 1)) ^
              (p ^ n)
          = ((X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ m *
              X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (p ^ n) := by
              rw [pow_succ]
        _ = ((X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ m) ^ (p ^ n) *
              (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (p ^ n) :=
              mul_pow _ _ _
        _ = X (g := g) (hmonic := hmonic) (hg_pos := hg_pos) ^ m *
              X (g := g) (hmonic := hmonic) (hg_pos := hg_pos) := by rw [ih, hX]
        _ = X (g := g) (hmonic := hmonic) (hg_pos := hg_pos) ^ (m + 1) := by
              rw [pow_succ]

/-- A monomial in the quotient equals `reduce (C c) * X^m`. -/
theorem reduce_monomial_eq (m : Nat) (c : ZMod64 p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.monomial m c) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ m := by
  -- monomial m c = C c * (DensePoly.monomial 1 1)^m at the FpPoly level
  -- equivalently, monomial m c = C c * FpPoly.X^m
  have hX_pow : FpPoly.linearPow (FpPoly.X (p := p)) m =
      DensePoly.monomial m (1 : ZMod64 p) := by
    show FpPoly.linearPow (DensePoly.monomial 1 (1 : ZMod64 p)) m =
      DensePoly.monomial m (1 : ZMod64 p)
    exact FpPoly.linearPow_monomial_one m
  have hX_quot : (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ m =
      reduce (DensePoly.monomial m (1 : ZMod64 p)) := by
    rw [show X (g := g) (hmonic := hmonic) (hg_pos := hg_pos) =
      reduce (FpPoly.X (p := p)) from rfl]
    rw [← reduce_linearPow_eq_pow]
    exact congrArg
      (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) hX_pow
  rw [hX_quot, ← reduce_mul]
  congr 1
  apply DensePoly.ext_coeff
  intro k
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  show (DensePoly.monomial m c).coeff k =
    (DensePoly.C c * DensePoly.monomial m (1 : ZMod64 p)).coeff k
  rw [DensePoly.coeff_monomial m c k]
  rw [show (DensePoly.C c * DensePoly.monomial m (1 : ZMod64 p)
    : FpPoly p) = DensePoly.scale c (DensePoly.monomial m (1 : ZMod64 p))
    from FpPoly.C_mul_eq_scale c _]
  rw [DensePoly.coeff_scale c _ k hzero]
  rw [DensePoly.coeff_monomial m (1 : ZMod64 p) k]
  by_cases hk : k = m
  · simp only [hk, if_true]
    show c = c * (1 : ZMod64 p)
    grind
  · simp only [hk, if_false]
    exact hzero.symm

private def quotMonoSum (f : FpPoly p)
    (g : FpPoly p) (hmonic : DensePoly.Monic g) (hg_pos : 0 < g.degree?.getD 0) :
    Nat → Quotient g hmonic hg_pos
  | 0 => 0
  | m + 1 =>
      quotMonoSum f g hmonic hg_pos m +
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.monomial m (f.coeff m))

private def fpPolyMonoSum (f : FpPoly p) : Nat → FpPoly p
  | 0 => 0
  | m + 1 => fpPolyMonoSum f m + DensePoly.monomial m (f.coeff m)

omit [ZMod64.PrimeModulus p] in
private theorem coeff_fpPolyMonoSum (f : FpPoly p) (m k : Nat) :
    (fpPolyMonoSum f m).coeff k = if k < m then f.coeff k else 0 := by
  induction m with
  | zero =>
      show (0 : FpPoly p).coeff k = if k < 0 then f.coeff k else 0
      rw [DensePoly.coeff_zero]
      have hk : ¬ k < 0 := Nat.not_lt_zero k
      rw [if_neg hk]
      rfl
  | succ m ih =>
      show (fpPolyMonoSum f m + DensePoly.monomial m (f.coeff m)).coeff k =
        if k < m + 1 then f.coeff k else 0
      rw [DensePoly.coeff_add_semiring]
      rw [ih]
      rw [DensePoly.coeff_monomial m (f.coeff m) k]
      by_cases hk_lt_m : k < m
      · have hk_lt_succ : k < m + 1 := Nat.lt_succ_of_lt hk_lt_m
        have hk_ne_m : k ≠ m := Nat.ne_of_lt hk_lt_m
        simp only [hk_lt_m, if_true, hk_lt_succ, hk_ne_m, if_false]
        show f.coeff k + 0 = f.coeff k
        grind
      · by_cases hk_eq_m : k = m
        · subst hk_eq_m
          have hk_lt_succ : k < k + 1 := Nat.lt_succ_self k
          have hk_lt_self : ¬ k < k := Nat.lt_irrefl k
          simp only [hk_lt_self, if_false, hk_lt_succ, if_true]
          show 0 + f.coeff k = f.coeff k
          grind
        · have hk_not_lt_succ : ¬ k < m + 1 := by omega
          simp only [hk_lt_m, hk_eq_m, hk_not_lt_succ, if_false]
          show 0 + 0 = (0 : ZMod64 p)
          grind

omit [ZMod64.PrimeModulus p] in
private theorem fpPolyMonoSum_eq_self (f : FpPoly p) (m : Nat)
    (hsize : f.size ≤ m) :
    fpPolyMonoSum f m = f := by
  apply DensePoly.ext_coeff
  intro k
  rw [coeff_fpPolyMonoSum]
  by_cases hk : k < m
  · simp [hk]
  · simp [hk]
    exact (DensePoly.coeff_eq_zero_of_size_le f (by omega)).symm

private theorem reduce_fpPolyMonoSum (f : FpPoly p) (m : Nat) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (fpPolyMonoSum f m) =
      quotMonoSum f g hmonic hg_pos m := by
  induction m with
  | zero =>
      show reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (0 : FpPoly p) =
        (0 : Quotient g hmonic hg_pos)
      rfl
  | succ m ih =>
      show reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (fpPolyMonoSum f m + DensePoly.monomial m (f.coeff m)) =
        quotMonoSum f g hmonic hg_pos m +
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (DensePoly.monomial m (f.coeff m))
      rw [reduce_add, ih]

private theorem reduce_eq_quotMonoSum (f : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
      quotMonoSum f g hmonic hg_pos f.size := by
  rw [← reduce_fpPolyMonoSum, fpPolyMonoSum_eq_self f f.size (Nat.le_refl _)]

private theorem quotMonoSum_pow_pPow_eq_self
    {n : Nat}
    (hX : (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (p ^ n) =
            X (g := g) (hmonic := hmonic) (hg_pos := hg_pos))
    (f : FpPoly p) (m : Nat) :
    (quotMonoSum f g hmonic hg_pos m) ^ (p ^ n) =
      quotMonoSum f g hmonic hg_pos m := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Hex.Nat.Prime.two_le hp)
  induction m with
  | zero =>
      show (0 : Quotient g hmonic hg_pos) ^ (p ^ n) = 0
      have hpos : 0 < p ^ n := Nat.pow_pos hp_pos
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos) with ⟨k, hk⟩
      rw [hk, pow_succ, mul_zero]
  | succ m ih =>
      show (quotMonoSum f g hmonic hg_pos m +
              reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.monomial m (f.coeff m))) ^ (p ^ n) =
        quotMonoSum f g hmonic hg_pos m +
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (DensePoly.monomial m (f.coeff m))
      rw [add_pow_pPow]
      rw [ih]
      congr 1
      rw [reduce_monomial_eq]
      rw [mul_pow]
      rw [reduce_C_pow_pPow_eq]
      rw [X_pow_pPowN hp_pos hX m]

/-- **Capstone:** if the Frobenius iterate `β ↦ β ^ (p ^ n)` fixes
`Quotient.X`, it fixes every quotient element.

The irreducibility hypothesis is recorded for downstream callers but is
not used in the proof: the X-generation argument is purely an algebra fact
about `F_p[X]/(g)` for any monic positive-degree `g`. -/
theorem pow_pPowN_eq_self_of_pow_pPowN_X_eq_X
    (_hg_irr : FpPoly.Irreducible g) {n : Nat}
    (hX : (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ (p ^ n) =
            X (g := g) (hmonic := hmonic) (hg_pos := hg_pos))
    (β : Quotient g hmonic hg_pos) :
    β ^ (p ^ n) = β := by
  -- Reduce β to its canonical representative.
  have hβ : β = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β.val :=
    (reduce_val_self β).symm
  rw [hβ]
  rw [reduce_eq_quotMonoSum]
  exact quotMonoSum_pow_pPow_eq_self hX β.val β.val.size

end Quotient
end FpPoly
end Hex
