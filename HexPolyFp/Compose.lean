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
  have hstep1 : ((0 : FpPoly p) * q + DensePoly.C (1 : ZMod64 p)) = (1 : FpPoly p) := by
    rw [FpPoly.zero_mul, FpPoly.zero_add]
    rfl
  rw [hstep1]
  rw [FpPoly.one_mul]
  show q + DensePoly.C (Zero.zero : ZMod64 p) = q
  rw [show (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) = 0 from C_zero_eq_zero]
  rw [FpPoly.add_zero]

theorem compose_one [ZMod64.PrimeModulus p] (q : FpPoly p) :
    DensePoly.compose (1 : FpPoly p) q = 1 := by
  change DensePoly.compose (DensePoly.C (1 : ZMod64 p)) q = DensePoly.C 1
  exact compose_C 1 q

/-! ### Compose-as-sum characterization

The Horner-form `DensePoly.compose` evaluates to the explicit sum
`∑_i C (f.coeff i) * linearPow q i`. This characterization is proved by
mirroring the `evalScalarCoeffList` / `evalCoeffPowerSumFrom`
infrastructure used by scalar evaluation, but with `ZMod64` replaced by
`FpPoly` and `(* x)` replaced by `(* q)`.
-/

/-- Polynomial-valued counterpart to `evalScalarCoeffList`. -/
private def composeScalarCoeffList :
    List (ZMod64 p) → FpPoly p → FpPoly p
  | [], _ => 0
  | c :: cs, q => DensePoly.C c + q * composeScalarCoeffList cs q

/-- Polynomial-valued counterpart to `evalCoeffPowerSumFrom`. -/
private def composeCoeffPowerSumFrom :
    List (ZMod64 p) → Nat → FpPoly p → FpPoly p
  | [], _, _ => 0
  | c :: cs, base, q =>
      DensePoly.C c * linearPow q base + composeCoeffPowerSumFrom cs (base + 1) q

private theorem mul_composeCoeffPowerSumFrom_eq_succ (q : FpPoly p) :
    ∀ cs base,
      q * composeCoeffPowerSumFrom cs base q =
        composeCoeffPowerSumFrom cs (base + 1) q
  | [], _ => by
      simp [composeCoeffPowerSumFrom, FpPoly.mul_zero]
  | c :: cs, base => by
      simp only [composeCoeffPowerSumFrom]
      rw [FpPoly.left_distrib]
      rw [mul_composeCoeffPowerSumFrom_eq_succ q cs (base + 1)]
      congr 1
      -- q * (C c * linearPow q base) = C c * linearPow q (base + 1)
      rw [← FpPoly.mul_assoc]
      rw [FpPoly.mul_comm q (DensePoly.C c)]
      rw [FpPoly.mul_assoc]
      congr 1
      change q * linearPow q base = linearPow q (base + 1)
      rw [linearPow_succ_left]

private theorem composeScalarCoeffList_eq_powerSumFrom_zero (q : FpPoly p) :
    ∀ cs,
      composeScalarCoeffList cs q = composeCoeffPowerSumFrom cs 0 q
  | [] => by
      simp [composeScalarCoeffList, composeCoeffPowerSumFrom]
  | c :: cs => by
      simp only [composeScalarCoeffList, composeCoeffPowerSumFrom]
      rw [composeScalarCoeffList_eq_powerSumFrom_zero q cs]
      rw [mul_composeCoeffPowerSumFrom_eq_succ q cs 0]
      congr 1
      -- C c = C c * linearPow q 0
      change DensePoly.C c = DensePoly.C c * 1
      rw [FpPoly.mul_one]

private theorem foldl_compose_reverse_eq_composeScalarCoeffList (q : FpPoly p) :
    ∀ cs,
      cs.reverse.foldl (fun acc c => acc * q + DensePoly.C c) (0 : FpPoly p) =
        composeScalarCoeffList cs q
  | [] => rfl
  | c :: cs => by
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_compose_reverse_eq_composeScalarCoeffList q cs]
      simp only [composeScalarCoeffList]
      -- composeScalarCoeffList cs q * q + C c = C c + q * composeScalarCoeffList cs q
      rw [FpPoly.add_comm]
      rw [FpPoly.mul_comm q]

/-- `DensePoly.compose` agrees with the iterative power-sum form. -/
private theorem compose_eq_powerSum (f q : FpPoly p) :
    DensePoly.compose f q = composeCoeffPowerSumFrom f.toArray.toList 0 q := by
  unfold DensePoly.compose
  rw [foldl_compose_reverse_eq_composeScalarCoeffList q f.toArray.toList]
  exact composeScalarCoeffList_eq_powerSumFrom_zero q f.toArray.toList

/-- `DensePoly.compose f q` agrees with the iterative Horner form. -/
theorem compose_eq_composeScalarCoeffList (f q : FpPoly p) :
    DensePoly.compose f q = composeScalarCoeffList f.toArray.toList q := by
  unfold DensePoly.compose
  exact foldl_compose_reverse_eq_composeScalarCoeffList q f.toArray.toList

/-! ### Constant-polynomial homomorphism laws

Small `C` homomorphism laws for `+`, `-`, `*` and `Neg` are needed to
manipulate the coefficients of products like `f * (X - C c)`.
-/

private theorem zmod64_add_zero_zero_local :
    (0 : ZMod64 p) + 0 = 0 := by grind

private theorem zmod64_sub_zero_zero_local :
    (0 : ZMod64 p) - 0 = 0 := by grind

theorem C_add_eq (a b : ZMod64 p) :
    (DensePoly.C (a + b) : FpPoly p) = DensePoly.C a + DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_local,
    DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      exact zmod64_add_zero_zero_local.symm

theorem C_sub_eq (a b : ZMod64 p) :
    (DensePoly.C (a - b) : FpPoly p) = DensePoly.C a - DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_sub _ _ _ zmod64_sub_zero_zero_local,
    DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      exact zmod64_sub_zero_zero_local.symm

theorem C_mul_C_eq (a b : ZMod64 p) :
    (DensePoly.C (a * b) : FpPoly p) = DensePoly.C a * DensePoly.C b := by
  rw [FpPoly.C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  have hzero : a * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero a
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => simp
  | succ n =>
      simp
      exact hzero

/-! ### Compose of `monomial k 1` and `linearPow X k`

The composition `compose (linearPow X k) w = linearPow w k` follows by
unfolding `linearPow X k` to `monomial k 1` and then reading off the
explicit coefficient list `[0, …, 0, 1]` through the Horner power-sum
form.
-/

private theorem composeCoeffPowerSumFrom_replicate_zero_append_one
    [ZMod64.PrimeModulus p] (w : FpPoly p) :
    ∀ (k base : Nat),
      composeCoeffPowerSumFrom
        ((List.replicate k (Zero.zero : ZMod64 p)) ++ [(1 : ZMod64 p)]) base w =
          linearPow w (base + k)
  | 0, base => by
      simp only [List.replicate, List.nil_append]
      show DensePoly.C (1 : ZMod64 p) * linearPow w base +
          composeCoeffPowerSumFrom [] (base + 1) w = linearPow w (base + 0)
      change (1 : FpPoly p) * linearPow w base + 0 = linearPow w (base + 0)
      rw [FpPoly.one_mul, FpPoly.add_zero, Nat.add_zero]
  | k + 1, base => by
      simp only [List.replicate, List.cons_append]
      show DensePoly.C (Zero.zero : ZMod64 p) * linearPow w base +
          composeCoeffPowerSumFrom
            (List.replicate k (Zero.zero : ZMod64 p) ++ [(1 : ZMod64 p)]) (base + 1) w =
          linearPow w (base + (k + 1))
      have hCz : (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) = 0 := C_zero_eq_zero
      rw [hCz, FpPoly.zero_mul, FpPoly.zero_add]
      rw [composeCoeffPowerSumFrom_replicate_zero_append_one w k (base + 1)]
      congr 1
      omega

private theorem monomial_one_toArray_toList_eq
    [ZMod64.PrimeModulus p] (k : Nat) :
    (DensePoly.monomial k (1 : ZMod64 p) : FpPoly p).toArray.toList =
      List.replicate k (Zero.zero : ZMod64 p) ++ [(1 : ZMod64 p)] := by
  have h1 : (1 : ZMod64 p) ≠ (Zero.zero : ZMod64 p) := one_ne_zero_of_prime
  show ((DensePoly.monomial k (1 : ZMod64 p) : FpPoly p).coeffs.toList :
    List (ZMod64 p)) = _
  unfold DensePoly.monomial
  rw [dif_neg h1]
  show ((Array.replicate k (Zero.zero : ZMod64 p)).push (1 : ZMod64 p)).toList =
    List.replicate k (Zero.zero : ZMod64 p) ++ [(1 : ZMod64 p)]
  rw [Array.toList_push, Array.toList_replicate]

private theorem compose_monomial_k_one_eq
    [ZMod64.PrimeModulus p] (w : FpPoly p) (k : Nat) :
    DensePoly.compose
        ((DensePoly.monomial k (1 : ZMod64 p)) : FpPoly p) w =
      linearPow w k := by
  rw [compose_eq_powerSum, monomial_one_toArray_toList_eq,
    composeCoeffPowerSumFrom_replicate_zero_append_one]
  rw [Nat.zero_add]

/-- `compose (linearPow X k) w = linearPow w k`. -/
theorem compose_linearPow_X
    [ZMod64.PrimeModulus p] (w : FpPoly p) (k : Nat) :
    DensePoly.compose (FpPoly.linearPow FpPoly.X k) w = FpPoly.linearPow w k := by
  show DensePoly.compose
    (FpPoly.linearPow (DensePoly.monomial 1 (1 : ZMod64 p) : FpPoly p) k) w = _
  rw [linearPow_monomial_one]
  exact compose_monomial_k_one_eq w k

end FpPoly
end Hex
