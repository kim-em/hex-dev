/-!
Shared `Nat`-level modular-arithmetic lemmas used by `HexArith` proofs.

Lean core already exposes the basic divisibility, mod, and gcd API; this file
collects the small bridge lemmas that core lacks but the Barrett and
Montgomery proof layers need. Today that is the single coprimality fact
that an odd modulus is coprime to every power of two — the shape required by
Montgomery inversion over `R = 2^k`.
-/
namespace Nat

/--
An odd number is coprime to every power of two. Montgomery inversion uses this
exact named bridge to discharge the `Nat.Coprime p (2 ^ k)` side condition for
the radix `R = 2^k`.
-/
theorem coprime_pow_two_of_odd {p k : Nat} (hp : p % 2 = 1) :
    Nat.Coprime p (2 ^ k) := by
  have hbase : Nat.Coprime p 2 := by
    rw [Nat.Coprime, Nat.gcd_comm p 2, Nat.gcd_rec 2 p, hp]
    rfl
  exact hbase.pow_right k

end Nat
