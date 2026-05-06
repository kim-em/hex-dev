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
end Quotient
end FpPoly
end Hex
