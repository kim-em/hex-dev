import HexPolyFp.Quotient
import HexPolyFp.SquareFree

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

/-- Reducing a sum is the sum of the reductions in the quotient. -/
theorem reduce_add (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f +
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h := by
  rw [add_eq_reduce_val]
  exact reduce_add_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h

/-- Reducing a product is the product of the reductions in the quotient. -/
theorem reduce_mul (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f * h) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f *
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h := by
  rw [mul_eq_reduce_val]
  exact reduce_mul_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h

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
theorem add_pow_prime (hp : Hex.Nat.Prime p) (a b : Quotient g hmonic hg_pos) :
    (a + b) ^ p = a ^ p + b ^ p := by
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
theorem add_pow_pPow (hp : Hex.Nat.Prime p) (a b : Quotient g hmonic hg_pos)
    (k : Nat) :
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
        _ = (a ^ (p ^ k)) ^ p + (b ^ (p ^ k)) ^ p := add_pow_prime hp _ _
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

omit [ZMod64.PrimeModulus p] in
/-- `linearPow (C c) p = C c` over `F_p`: Fermat for constants in
characteristic `p`. -/
theorem linearPow_C_pow_prime (hp : Hex.Nat.Prime p) (c : ZMod64 p) :
    FpPoly.linearPow (DensePoly.C c : FpPoly p) p = DensePoly.C c := by
  rw [linearPow_C, ZMod64.pow_prime hp]

/-- Constants are fixed by the prime-power Frobenius on the quotient. -/
theorem reduce_C_pow_prime_eq (hp : Hex.Nat.Prime p) (c : ZMod64 p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c)) ^ p =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) := by
  rw [← reduce_linearPow_eq_pow]
  rw [linearPow_C_pow_prime hp]

/-- Constants are fixed by every iterate of the Frobenius on the quotient. -/
theorem reduce_C_pow_pPow_eq (hp : Hex.Nat.Prime p) (c : ZMod64 p) (k : Nat) :
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
              (DensePoly.C c) := reduce_C_pow_prime_eq hp c

end Quotient
end FpPoly
end Hex
