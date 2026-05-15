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

/-! ### Substitution into `a * (X - C c)`

Substituting `w` into `a * (X - FpPoly.C c)` yields
`compose a w * (w - FpPoly.C c)`. The proof goes through a list-level
coefficient model: `mulXSubCList c cs` is the coefficient list of
`(ofCoeffs cs.toArray) * (X - C c)`, and `composeScalarCoeffList`
distributes over that list operation in the obvious way.
-/

/-- Auxiliary recursion: the list-level coefficient form of
`(ofCoeffs cs.toArray) * (X - C c) + C prev`. -/
private def mulXSubCListAux (c : ZMod64 p) :
    ZMod64 p → List (ZMod64 p) → List (ZMod64 p)
  | prev, [] => [prev]
  | prev, x :: xs => (prev - c * x) :: mulXSubCListAux c x xs

/-- Coefficient list of `(ofCoeffs cs.toArray) * (X - C c)`. -/
private def mulXSubCList (c : ZMod64 p) (cs : List (ZMod64 p)) : List (ZMod64 p) :=
  mulXSubCListAux c 0 cs

private theorem fp_C_zero :
    (FpPoly.C (0 : ZMod64 p) : FpPoly p) = 0 := C_zero_eq_zero

/-- `composeScalarCoeffList` ignores trailing zeros. -/
private theorem composeScalarCoeffList_trim
    [ZMod64.PrimeModulus p] (q : FpPoly p) :
    ∀ cs : List (ZMod64 p),
      composeScalarCoeffList (DensePoly.trimTrailingZerosList cs) q =
        composeScalarCoeffList cs q
  | [] => by
      simp [DensePoly.trimTrailingZerosList]
  | c :: cs => by
      unfold DensePoly.trimTrailingZerosList
      by_cases htrim :
          DensePoly.trimTrailingZerosList cs = [] ∧ c = (Zero.zero : ZMod64 p)
      · rw [if_pos htrim]
        have htail : DensePoly.trimTrailingZerosList cs = [] := htrim.1
        have hc : c = (Zero.zero : ZMod64 p) := htrim.2
        have hih := composeScalarCoeffList_trim q cs
        rw [htail] at hih
        -- hih : composeScalarCoeffList [] q = composeScalarCoeffList cs q
        -- Goal: composeScalarCoeffList [] q = composeScalarCoeffList (c :: cs) q
        --     = DensePoly.C c + q * composeScalarCoeffList cs q
        --     = DensePoly.C 0 + q * composeScalarCoeffList cs q  (using hc)
        --     = 0 + q * 0  (via hih)
        --     = 0
        -- And LHS = composeScalarCoeffList [] q = 0.
        rw [hc]
        simp only [composeScalarCoeffList]
        rw [← hih]
        change composeScalarCoeffList [] q =
          (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) +
            q * composeScalarCoeffList [] q
        simp only [composeScalarCoeffList]
        rw [show (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) = 0 from
          fp_C_zero]
        rw [FpPoly.mul_zero, FpPoly.zero_add]
      · rw [if_neg htrim]
        simp only [composeScalarCoeffList]
        rw [composeScalarCoeffList_trim q cs]

/-- `compose` on a polynomial built from a raw coefficient list agrees with
`composeScalarCoeffList` on that list, even if the list has trailing zeros. -/
private theorem compose_ofCoeffs_eq_composeScalarCoeffList
    [ZMod64.PrimeModulus p] (cs : List (ZMod64 p)) (q : FpPoly p) :
    DensePoly.compose (DensePoly.ofCoeffs cs.toArray : FpPoly p) q =
      composeScalarCoeffList cs q := by
  rw [compose_eq_composeScalarCoeffList]
  have htoArray :
      (DensePoly.ofCoeffs cs.toArray : FpPoly p).toArray.toList =
        DensePoly.trimTrailingZerosList cs := by
    show (DensePoly.trimTrailingZeros cs.toArray).toList =
      DensePoly.trimTrailingZerosList cs
    simp [DensePoly.trimTrailingZeros]
  rw [htoArray, composeScalarCoeffList_trim]

/-- Generic add-comm-monoid rearrangement: `A + B + (C + D) = D + B + C + A`. -/
private theorem fp_add_acm_rearrange
    (A B C D : FpPoly p) :
    A + B + (C + D) = D + B + C + A := by
  -- LHS = A + B + C + D (after collapsing the inner parens via ← add_assoc).
  rw [← FpPoly.add_assoc (A + B) C D]
  -- RHS = D + B + C + A.
  -- Strategy: rewrite RHS via add_assoc to D + (B + C + A), then show A + B + C + D = D + (B + C + A)
  -- by adding D and then commuting.
  rw [FpPoly.add_assoc D B C]
  rw [FpPoly.add_assoc D (B + C) A]
  -- Now goal: A + B + C + D = D + (B + C + A)
  -- LHS = A + B + C + D, swap A and D via comm of the full sum.
  rw [FpPoly.add_comm A B]
  rw [FpPoly.add_assoc B A C]
  rw [FpPoly.add_comm A C]
  rw [← FpPoly.add_assoc B C A]
  -- Now goal: B + C + A + D = D + (B + C + A)
  rw [FpPoly.add_comm (B + C + A) D]

/-- Polynomial commutative-ring rearrangement used in the inductive step of
`composeScalarCoeffList_mulXSubCListAux`. -/
private theorem alg_compose_step
    (cprev ccx cx w s : FpPoly p) :
    cprev - ccx * cx + w * (s * (w - ccx) + cx) =
      (cx + w * s) * (w - ccx) + cprev := by
  rw [FpPoly.left_distrib w (s * (w - ccx)) cx]
  rw [← FpPoly.mul_assoc w s (w - ccx)]
  rw [FpPoly.right_distrib cx (w * s) (w - ccx)]
  have hcx_sub :
      cx * (w - ccx) = cx * w - cx * ccx := by
    -- Use mul_comm to commute the multiplications, then existing neg_mul_right_poly.
    rw [FpPoly.mul_comm cx (w - ccx)]
    rw [FpPoly.mul_comm cx w]
    rw [FpPoly.mul_comm cx ccx]
    -- Goal: (w - ccx) * cx = w * cx - ccx * cx
    rw [sub_eq_add_neg, sub_eq_add_neg, FpPoly.right_distrib]
    congr 1
    -- Goal: (-ccx) * cx = -(ccx * cx)
    rw [show (-ccx : FpPoly p) = 0 - ccx from (zero_sub _).symm]
    rw [show (-(ccx * cx) : FpPoly p) = 0 - ccx * cx from (zero_sub _).symm]
    -- Goal: (0 - ccx) * cx = 0 - ccx * cx
    exact DensePoly.neg_mul_right_poly ccx cx
  rw [hcx_sub]
  rw [FpPoly.mul_comm cx w]
  rw [FpPoly.mul_comm cx ccx]
  rw [sub_eq_add_neg cprev (ccx * cx)]
  rw [sub_eq_add_neg (w * cx) (ccx * cx)]
  -- Goal:
  --   cprev + -(ccx * cx) + (w * s * (w - ccx) + w * cx) =
  --   (w * cx + -(ccx * cx) + w * s * (w - ccx)) + cprev
  exact fp_add_acm_rearrange cprev (-(ccx * cx))
    (w * s * (w - ccx)) (w * cx)

/-- The list-level recurrence: `composeScalarCoeffList (mulXSubCListAux c prev cs) w`
collapses to `composeScalarCoeffList cs w * (w - C c) + C prev`. -/
private theorem composeScalarCoeffList_mulXSubCListAux
    [ZMod64.PrimeModulus p] (c : ZMod64 p) (w : FpPoly p) :
    ∀ (prev : ZMod64 p) (cs : List (ZMod64 p)),
      composeScalarCoeffList (mulXSubCListAux c prev cs) w =
        composeScalarCoeffList cs w * (w - FpPoly.C c) + FpPoly.C prev
  | prev, [] => by
      simp only [mulXSubCListAux, composeScalarCoeffList]
      -- Goal: DensePoly.C prev + w * 0 = 0 * (w - C c) + C prev
      rw [FpPoly.mul_zero, FpPoly.zero_mul]
      rw [FpPoly.add_zero, FpPoly.zero_add]
      rfl
  | prev, x :: xs => by
      simp only [mulXSubCListAux, composeScalarCoeffList]
      rw [composeScalarCoeffList_mulXSubCListAux c w x xs]
      rw [C_sub_eq, C_mul_C_eq]
      -- Goal:
      --   DensePoly.C prev - DensePoly.C c * DensePoly.C x +
      --     w * (S * (w - C c) + C x) =
      --   (C x + w * S) * (w - C c) + C prev
      -- where S := composeScalarCoeffList xs w.
      exact alg_compose_step (FpPoly.C prev) (FpPoly.C c) (FpPoly.C x) w
        (composeScalarCoeffList xs w)

/-- The specialised list-level recurrence with `prev = 0`. -/
private theorem composeScalarCoeffList_mulXSubCList
    [ZMod64.PrimeModulus p] (c : ZMod64 p) (w : FpPoly p) (cs : List (ZMod64 p)) :
    composeScalarCoeffList (mulXSubCList c cs) w =
      composeScalarCoeffList cs w * (w - FpPoly.C c) := by
  unfold mulXSubCList
  rw [composeScalarCoeffList_mulXSubCListAux c w 0 cs]
  rw [fp_C_zero, FpPoly.add_zero]

private theorem toArray_toList_getD_eq_coeff
    (f : FpPoly p) (n : Nat) :
    f.toArray.toList.getD n (0 : ZMod64 p) = f.coeff n := by
  show f.coeffs.toList.getD n (0 : ZMod64 p) = f.coeffs.getD n (Zero.zero : ZMod64 p)
  rw [Array.getD_eq_getD_getElem?]
  change f.coeffs.toList[n]?.getD (0 : ZMod64 p) =
    f.coeffs[n]?.getD (Zero.zero : ZMod64 p)
  rw [Array.getElem?_toList]
  rfl

private theorem array_getD_eq_list_getD
    (arr : Array (ZMod64 p)) (n : Nat) :
    arr.getD n (Zero.zero : ZMod64 p) = arr.toList.getD n (0 : ZMod64 p) := by
  rw [Array.getD_eq_getD_getElem?]
  change arr[n]?.getD (Zero.zero : ZMod64 p) = arr.toList[n]?.getD (0 : ZMod64 p)
  rw [Array.getElem?_toList]
  rfl

/-- `mulXSubCListAux`'s `getD` form: combines the prev with the off-by-one
shifted coefficient list. -/
private theorem mulXSubCListAux_getD (c : ZMod64 p) :
    ∀ (prev : ZMod64 p) (cs : List (ZMod64 p)) (n : Nat),
      (mulXSubCListAux c prev cs).getD n (0 : ZMod64 p) =
        (if n = 0 then prev else cs.getD (n - 1) (0 : ZMod64 p)) -
          c * cs.getD n (0 : ZMod64 p)
  | prev, [], 0 => by
      simp only [mulXSubCListAux, List.getD_cons_zero]
      show prev = (if 0 = 0 then prev else ([] : List (ZMod64 p)).getD (0 - 1) 0) -
        c * ([] : List (ZMod64 p)).getD 0 0
      simp
      have : c * (0 : ZMod64 p) = 0 := by grind
      grind
  | prev, [], n + 1 => by
      simp only [mulXSubCListAux]
      show ([prev] : List (ZMod64 p)).getD (n + 1) 0 =
        (if n + 1 = 0 then prev else ([] : List (ZMod64 p)).getD ((n + 1) - 1) 0) -
          c * ([] : List (ZMod64 p)).getD (n + 1) 0
      simp [List.getD]
      have : c * (0 : ZMod64 p) = 0 := by grind
      grind
  | prev, x :: xs, 0 => by
      simp only [mulXSubCListAux, List.getD_cons_zero]
      rfl
  | prev, x :: xs, n + 1 => by
      simp only [mulXSubCListAux]
      rw [List.getD_cons_succ]
      have hih := mulXSubCListAux_getD c x xs n
      rw [hih]
      cases n with
      | zero =>
          simp [List.getD]
      | succ n =>
          simp [List.getD]

private theorem mulXSubCList_getD (c : ZMod64 p) (cs : List (ZMod64 p)) (n : Nat) :
    (mulXSubCList c cs).getD n (0 : ZMod64 p) =
      (if n = 0 then (0 : ZMod64 p) else cs.getD (n - 1) 0) -
        c * cs.getD n 0 := by
  unfold mulXSubCList
  rw [mulXSubCListAux_getD c 0 cs n]

/-- The polynomial-level equality matching `mulXSubCList` to the
coefficient list of `a * (X - C c)`. -/
private theorem mul_X_sub_C_eq_ofCoeffs_mulXSubCList
    (a : FpPoly p) (c : ZMod64 p) :
    a * (FpPoly.X - FpPoly.C c) =
      DensePoly.ofCoeffs (mulXSubCList c a.toArray.toList).toArray := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : ZMod64 p) - 0 = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + 0 = 0 := by grind
  have hzero_mul_c : c * (0 : ZMod64 p) = 0 := by grind
  -- LHS computation
  have hLHS : (a * (FpPoly.X - FpPoly.C c)).coeff n =
      (if n = 0 then (0 : ZMod64 p) else a.coeff (n - 1)) - c * a.coeff n := by
    rw [FpPoly.mul_comm a (FpPoly.X - FpPoly.C c)]
    have hneg_mul : (-(FpPoly.C c) : FpPoly p) * a = -(FpPoly.C c * a) := by
      show (0 - FpPoly.C c) * a = 0 - FpPoly.C c * a
      exact DensePoly.neg_mul_right_poly (FpPoly.C c) a
    rw [sub_eq_add_neg, right_distrib]
    rw [DensePoly.coeff_add _ _ _ hzero_add]
    rw [hneg_mul]
    rw [DensePoly.coeff_neg _ _ hzero_sub]
    rw [show FpPoly.X = (DensePoly.monomial 1 (1 : ZMod64 p) : FpPoly p) from rfl]
    rw [coeff_monomial_mul]
    have hCmul : FpPoly.C c * a = DensePoly.scale c a := FpPoly.C_mul_eq_scale c a
    rw [hCmul]
    rw [DensePoly.coeff_scale _ _ _ hzero_mul_c]
    cases n with
    | zero =>
        simp; grind
    | succ n =>
        simp; grind
  rw [hLHS]
  -- RHS computation
  rw [DensePoly.coeff_ofCoeffs]
  rw [array_getD_eq_list_getD]
  rw [mulXSubCList_getD]
  rw [toArray_toList_getD_eq_coeff a n]
  -- Replace cs.getD (n-1) 0 with a.coeff (n-1)
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_sub_one]
      rw [toArray_toList_getD_eq_coeff a n]

theorem compose_mul_X_sub_C [ZMod64.PrimeModulus p]
    (a : FpPoly p) (c : ZMod64 p) (w : FpPoly p) :
    DensePoly.compose (a * (FpPoly.X - FpPoly.C c)) w =
      DensePoly.compose a w * (w - FpPoly.C c) := by
  rw [mul_X_sub_C_eq_ofCoeffs_mulXSubCList]
  rw [compose_ofCoeffs_eq_composeScalarCoeffList]
  rw [composeScalarCoeffList_mulXSubCList]
  rw [compose_eq_composeScalarCoeffList]

/-! ### foldl transport for the prime-field linear product

The product `xs.foldl (fun acc c => acc * (X - C c)) init` substituted at
`w` reduces to the same foldl with each `X` replaced by `w`.
-/

theorem compose_foldl_X_sub_C [ZMod64.PrimeModulus p]
    (xs : List (ZMod64 p)) (init w : FpPoly p) :
    DensePoly.compose
      (xs.foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) init) w =
      xs.foldl (fun acc c => acc * (w - FpPoly.C c))
        (DensePoly.compose init w) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (init * (FpPoly.X - FpPoly.C x))]
      rw [compose_mul_X_sub_C init x w]

/-- Specialisation to the canonical prime-field linear product starting from
`init = 1`: substituting `w` into the variable form gives the witness form. -/
theorem compose_primeFieldLinearProduct [ZMod64.PrimeModulus p]
    (w : FpPoly p) :
    DensePoly.compose
      ((ZMod64.values p).foldl
        (fun acc c => acc * (FpPoly.X - FpPoly.C c)) 1) w =
      (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1 := by
  rw [compose_foldl_X_sub_C]
  rw [compose_one]

end FpPoly
end Hex
