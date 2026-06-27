module

public import HexArith.Nat.Prime
public import HexModArith.Ring

public section

/-!
Prime-modulus theorem surface for `hex-mod-arith`.

This module packages the `ZMod64` consequences that only hold when the modulus
is prime, reusing the upstream `Hex.Nat.Prime` lemmas rather than
re-proving prime arithmetic locally.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

/-- Typeclass wrapper for the prime-modulus assumption needed by field-style
facts over `ZMod64 p`. -/
class PrimeModulus (p : Nat) : Prop where
  prime : Hex.Nat.Prime p

/-- Build the prime-modulus typeclass witness from an explicit project-local
primality proof. -/
@[expose, reducible]
def primeModulusOfPrime (hp : Hex.Nat.Prime p) : PrimeModulus p :=
  ⟨hp⟩

private theorem eq_zero_of_dvd_modulus {a : ZMod64 p} (h : p ∣ a.toNat) : a = 0 := by
  apply ext
  apply UInt64.toNat_inj.mp
  have hzero : a.toNat = 0 := Nat.eq_zero_of_dvd_of_lt h a.toNat_lt
  simpa [ZMod64.toNat_eq_val] using hzero

/--
Prime-modulus residues have no zero divisors: if `a * b = 0`, then one of the
factors is already zero.
-/
@[grind .]
theorem eq_zero_or_eq_zero_of_mul_eq_zero (hp : Hex.Nat.Prime p) {a b : ZMod64 p}
    (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have hmod : (a.toNat * b.toNat) % p = 0 := by
    simpa using congrArg ZMod64.toNat h
  have hdvd : p ∣ a.toNat * b.toNat := by
    have hdecomp := Nat.mod_add_div (a.toNat * b.toNat) p
    rw [hmod, Nat.zero_add] at hdecomp
    exact ⟨(a.toNat * b.toNat) / p, hdecomp.symm⟩
  rcases (Hex.Nat.Prime.dvd_mul hp).mp hdvd with hA | hB
  · exact Or.inl (eq_zero_of_dvd_modulus hA)
  · exact Or.inr (eq_zero_of_dvd_modulus hB)

/--
Prime-modulus residues have no zero divisors, using the ambient
`PrimeModulus` typeclass witness.
-/
@[grind .]
theorem eq_zero_or_eq_zero_of_mul_eq_zero_of_prime_modulus [PrimeModulus p]
    {a b : ZMod64 p} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  eq_zero_or_eq_zero_of_mul_eq_zero (PrimeModulus.prime (p := p)) h

/-- Nonzero residues modulo a prime have multiplicative inverses. -/
@[grind =]
theorem inv_mul_eq_one_of_prime (hp : Hex.Nat.Prime p) {a : ZMod64 p}
    (ha : a ≠ 0) : ZMod64.inv a * a = 1 := by
  apply ext
  apply UInt64.toNat_inj.mp
  let aval := a.toNat
  have haval : aval = a.toNat := rfl
  have hnotdvd : ¬ p ∣ aval := by
    intro hdiv
    exact ha (eq_zero_of_dvd_modulus (by simpa [haval] using hdiv))
  have hcop : Nat.Coprime aval p := (Hex.Nat.Prime.coprime_of_not_dvd hp hnotdvd).symm
  change (ZMod64.mul (ZMod64.inv a) a).toNat = (1 : ZMod64 p).toNat
  rw [ZMod64.inv_mul_eq_one a (by simpa [haval] using hcop)]
  exact ZMod64.toNat_one.symm

/--
Nonzero residues modulo an ambient prime modulus have multiplicative inverses.
-/
@[grind =]
theorem inv_mul_eq_one_of_ne_zero [PrimeModulus p] {a : ZMod64 p}
    (ha : a ≠ 0) : ZMod64.inv a * a = 1 :=
  inv_mul_eq_one_of_prime (PrimeModulus.prime (p := p)) ha

/-- Symmetric form of `inv_mul_eq_one_of_prime`: `a * a⁻¹ = 1`. -/
@[grind =]
theorem mul_inv_eq_one_of_prime (hp : Hex.Nat.Prime p) {a : ZMod64 p}
    (ha : a ≠ 0) : a * ZMod64.inv a = 1 := by
  have h := inv_mul_eq_one_of_prime hp ha
  grind

/-- Symmetric form of `inv_mul_eq_one_of_ne_zero`: `a * a⁻¹ = 1`. -/
@[grind =]
theorem mul_inv_eq_one_of_ne_zero [PrimeModulus p] {a : ZMod64 p}
    (ha : a ≠ 0) : a * ZMod64.inv a = 1 :=
  mul_inv_eq_one_of_prime (PrimeModulus.prime (p := p)) ha

/--
Fermat's little theorem for `ZMod64`: raising a residue mod a prime `p` to the
`p`th power returns the original residue.
-/
theorem pow_prime (hp : Hex.Nat.Prime p) (a : ZMod64 p) : a ^ p = a := by
  apply ext
  apply UInt64.toNat_inj.mp
  have hpow : (a ^ p).toNat = a.toNat := by
    calc
      (a ^ p).toNat = a.toNat ^ p % p := toNat_pow a p
      _ = a.toNat % p := Hex.Nat.pow_prime_mod hp a.toNat
      _ = a.toNat := Nat.mod_eq_of_lt a.toNat_lt
  simpa [ZMod64.toNat_eq_val] using hpow

/--
Fermat's little theorem for an ambient prime modulus.
-/
@[simp, grind =] theorem pow_prime_of_prime_modulus [PrimeModulus p] (a : ZMod64 p) :
    a ^ p = a :=
  pow_prime (PrimeModulus.prime (p := p)) a

end ZMod64

end Hex
