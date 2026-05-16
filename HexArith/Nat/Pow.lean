/-!
Mathlib-free natural-number lemmas about exponentiation, used by the
project-side polynomial divisibility chain in `HexBerlekamp.RabinSoundness`.

This module owns the Fermat-style exponent identity
`d ∣ m → (p^d - 1) ∣ (p^m - 1)` and its `(x - 1) ∣ (x^j - 1)` building
block.
-/

namespace Hex

namespace Nat

/--
Inductive content of the geometric-series identity for `1 ≤ x`: every power
`x ^ j` is one more than a multiple of `x - 1`. The witness `k` is the partial
geometric sum `1 + x + x^2 + ⋯ + x^(j-1)`.
-/
private theorem pow_eq_succ_mul_sub_one_add_one_of_one_le
    {x : Nat} (hx : 1 ≤ x) :
    ∀ j : Nat, ∃ k : Nat, x ^ j = (x - 1) * k + 1
  | 0 => ⟨0, by simp⟩
  | j + 1 => by
      obtain ⟨k, hk⟩ := pow_eq_succ_mul_sub_one_add_one_of_one_le hx j
      refine ⟨x * k + 1, ?_⟩
      rw [Nat.pow_succ, hk]
      have hxm1 : x - 1 + 1 = x := Nat.sub_add_cancel hx
      calc ((x - 1) * k + 1) * x
          = (x - 1) * k * x + 1 * x := Nat.add_mul ((x - 1) * k) 1 x
        _ = (x - 1) * (k * x) + x := by rw [Nat.mul_assoc, Nat.one_mul]
        _ = (x - 1) * (x * k) + x := by rw [Nat.mul_comm k x]
        _ = (x - 1) * (x * k) + ((x - 1) + 1) := by rw [hxm1]
        _ = (x - 1) * (x * k) + (x - 1) + 1 := by rw [Nat.add_assoc]
        _ = (x - 1) * (x * k) + (x - 1) * 1 + 1 := by rw [Nat.mul_one]
        _ = (x - 1) * (x * k + 1) + 1 := by rw [Nat.mul_add]

/--
The classical geometric-series divisibility identity at the natural-number
level: `x - 1` divides `x^j - 1` for any `x, j : Nat`. Downstream polynomial
divisibility proofs use this as a named rewrite-free bridge, without unfolding
the geometric-series witness.

Edge cases (where the implicit subtraction underflows to `0`) all reduce to
`0 ∣ 0` and require no special handling.
-/
theorem sub_one_dvd_pow_sub_one (x j : Nat) :
    x - 1 ∣ x ^ j - 1 := by
  rcases Nat.lt_or_ge x 1 with hx | hx
  · -- x = 0
    have hx0 : x = 0 := by omega
    subst hx0
    cases j with
    | zero => simp
    | succ j' => simp [Nat.pow_succ, Nat.mul_zero]
  obtain ⟨k, hk⟩ := pow_eq_succ_mul_sub_one_add_one_of_one_le hx j
  refine ⟨k, ?_⟩
  rw [hk, Nat.add_sub_cancel]

/--
Fermat-style exponent identity: if `d ∣ m`, then `p^d - 1 ∣ p^m - 1` over
`Nat`. This is the public helper used in the project-side
`xPowSubX_dvd_of_dvd` polynomial divisibility chain.
-/
theorem pow_sub_one_dvd_pow_sub_one_of_dvd
    (p : Nat) {d m : Nat} (hdvd : d ∣ m) :
    p ^ d - 1 ∣ p ^ m - 1 := by
  rcases hdvd with ⟨j, hj⟩
  subst hj
  rw [Nat.pow_mul]
  exact sub_one_dvd_pow_sub_one (p ^ d) j

end Nat

end Hex
