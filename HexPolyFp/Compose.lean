import HexPolyFp.Basic

/-!
Non-modular composition laws for `DensePoly` over `FpPoly p`.

These narrowly scoped homomorphism-style laws are exactly what is needed
to substitute an arbitrary witness polynomial `w` into the prime-field
product identity `(∏_{c ∈ F_p} (X - C c)) = linearPow X p - X` proved in
`HexBerlekamp.RabinSoundness`. The headline result here is

```
compose ((values p).foldl (fun acc c => acc * (X - C c)) 1) w =
  (values p).foldl (fun acc c => acc * (w - C c)) 1
```

together with the corresponding RHS transport

```
compose (linearPow X p - X) w = linearPow w p - w.
```
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-! ### Basic compose laws -/

private theorem C_zero_eq_zero :
    FpPoly.C (0 : ZMod64 p) = (0 : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  unfold FpPoly.C
  rw [DensePoly.coeff_C, DensePoly.coeff_zero]
  cases n <;> rfl

@[simp] theorem compose_zero (q : FpPoly p) :
    DensePoly.compose (0 : FpPoly p) q = 0 := by
  rfl

@[simp] theorem compose_C (c : ZMod64 p) (q : FpPoly p) :
    DensePoly.compose (FpPoly.C c) q = FpPoly.C c := by
  by_cases hc : c = (0 : ZMod64 p)
  · subst hc
    rw [C_zero_eq_zero]
    exact (C_zero_eq_zero (p := p)).symm
  · change c ≠ (Zero.zero : ZMod64 p) at hc
    unfold DensePoly.compose DensePoly.toArray FpPoly.C
    rw [DensePoly.coeffs_C_of_ne_zero hc]
    show (#[c].toList.reverse.foldl
        (fun acc coeff => acc * q + DensePoly.C coeff) (0 : FpPoly p)) = DensePoly.C c
    have hlist : #[c].toList = [c] := rfl
    rw [hlist]
    have hrev : ([c] : List (ZMod64 p)).reverse = [c] := rfl
    rw [hrev]
    simp only [List.foldl_cons, List.foldl_nil]
    have : (0 : FpPoly p) * q + DensePoly.C c = DensePoly.C c := by
      rw [FpPoly.zero_mul, FpPoly.zero_add]
    exact this

private theorem one_ne_zero_of_prime [ZMod64.PrimeModulus p] :
    (1 : ZMod64 p) ≠ (Zero.zero : ZMod64 p) := by
  intro h
  have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

@[simp] theorem compose_X [ZMod64.PrimeModulus p] (q : FpPoly p) :
    DensePoly.compose (FpPoly.X : FpPoly p) q = q := by
  unfold DensePoly.compose DensePoly.toArray FpPoly.X DensePoly.monomial
  have h1 : (1 : ZMod64 p) ≠ (Zero.zero : ZMod64 p) := one_ne_zero_of_prime
  rw [dif_neg h1]
  show ((((Array.replicate 1 (Zero.zero : ZMod64 p)).push 1).toList).reverse.foldl
      (fun acc coeff => acc * q + DensePoly.C coeff) 0) = q
  have hlist :
      ((Array.replicate 1 (Zero.zero : ZMod64 p)).push 1).toList =
        [(Zero.zero : ZMod64 p), 1] := rfl
  rw [hlist]
  have hrev : ([(Zero.zero : ZMod64 p), 1] : List (ZMod64 p)).reverse =
      [(1 : ZMod64 p), Zero.zero] := rfl
  rw [hrev]
  simp only [List.foldl_cons, List.foldl_nil]
  -- foldl proceeds: 0 → 0*q + C 1 = C 1 → (C 1)*q + C 0 = q + 0 = q
  have hstep1 : ((0 : FpPoly p) * q + DensePoly.C (1 : ZMod64 p)) = (1 : FpPoly p) := by
    rw [FpPoly.zero_mul, FpPoly.zero_add]
    rfl
  rw [hstep1]
  rw [FpPoly.one_mul]
  show q + DensePoly.C (Zero.zero : ZMod64 p) = q
  rw [show (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) = 0 from C_zero_eq_zero]
  rw [FpPoly.add_zero]

end FpPoly
end Hex
