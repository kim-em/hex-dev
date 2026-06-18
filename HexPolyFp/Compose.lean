import HexPolyFp.Basic
import HexPolyFp.SquareFree
import HexPolyFp.QuotientFrobenius

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

@[simp, grind =] theorem compose_zero (q : FpPoly p) :
    DensePoly.compose (0 : FpPoly p) q = 0 := by
  rfl

@[simp, grind =] theorem compose_C (c : ZMod64 p) (q : FpPoly p) :
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

@[simp, grind =] theorem compose_X [ZMod64.PrimeModulus p] (q : FpPoly p) :
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

/-- Composing the constant polynomial `1` with any `q` yields `1`: the
multiplicative identity of `FpPoly` is fixed by substitution. This is the
base case for composing an iterated product of linear factors (see
`compose_primeFieldLinearProduct`). -/
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
      DensePoly.composeScalarCoeffList cs q = composeCoeffPowerSumFrom cs 0 q
  | [] => by
      simp [DensePoly.composeScalarCoeffList, composeCoeffPowerSumFrom]
  | c :: cs => by
      simp only [DensePoly.composeScalarCoeffList, composeCoeffPowerSumFrom]
      rw [composeScalarCoeffList_eq_powerSumFrom_zero q cs]
      rw [mul_composeCoeffPowerSumFrom_eq_succ q cs 0]
      congr 1
      -- C c = C c * linearPow q 0
      change DensePoly.C c = DensePoly.C c * 1
      rw [FpPoly.mul_one]

/-- `DensePoly.compose` agrees with the iterative power-sum form. -/
private theorem compose_eq_powerSum (f q : FpPoly p) :
    DensePoly.compose f q = composeCoeffPowerSumFrom f.toArray.toList 0 q := by
  rw [DensePoly.compose_eq_composeScalarCoeffList_of_step f q]
  · exact composeScalarCoeffList_eq_powerSumFrom_zero q f.toArray.toList
  · intro acc c
    rw [FpPoly.add_comm, FpPoly.mul_comm q acc]

/-- `DensePoly.compose f q` agrees with the iterative Horner form. -/
theorem compose_eq_composeScalarCoeffList (f q : FpPoly p) :
    DensePoly.compose f q = DensePoly.composeScalarCoeffList f.toArray.toList q := by
  apply DensePoly.compose_eq_composeScalarCoeffList_of_step
  intro acc c
  rw [FpPoly.add_comm, FpPoly.mul_comm q acc]

/-! ### Constant-polynomial homomorphism laws

Small `C` homomorphism laws for `+`, `-`, `*` and `Neg` are needed to
manipulate the coefficients of products like `f * (X - C c)`.
-/

theorem C_add_eq (a b : ZMod64 p) :
    (DensePoly.C (a + b) : FpPoly p) = DensePoly.C a + DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_add_semiring,
    DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      exact (by grind : (0 : ZMod64 p) + 0 = 0).symm

/-- The constant embedding `C` turns a difference of scalars into a
difference of constant polynomials. Used to push coefficient subtractions
through products such as `f * (X - C c)`. -/
theorem C_sub_eq (a b : ZMod64 p) :
    (DensePoly.C (a - b) : FpPoly p) = DensePoly.C a - DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_sub_ring,
    DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      exact (by grind : (0 : ZMod64 p) - 0 = 0).symm

/-- The constant embedding `C` turns a product of scalars into a product
of constant polynomials. Used to normalise constant coefficients when
expanding products of linear factors. -/
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

/-! ### Coefficient-indexed power-sum form

A coefficient-indexed analogue of `composeCoeffPowerSumFrom`, mirroring
`evalCoeffPowerSumUpTo` from `HexPolyFp/Basic.lean`. The size-bounded form
`compose_eq_coeff_power_sum_upTo_bound` lets us express
`compose (f - h) w` and `compose f w - compose h w` over a single
shared coefficient bound, which is the key ingredient for
`compose_sub` distributivity. -/

/-- Recursive sum form of compose. The compose-power-sum
`Σ_{k=base}^{base+n-1} C(coeff k) · linearPow w k` recursively builds up
the polynomial substitution: each step adds a single
`C(coeff base) · linearPow w base` term and recurses with `base + 1`.
This shape is matched by Berlekamp's matrix-action sum after replacing
`linearPow w` with the reduced `powModMonic` columns. -/
def composeCoeffPowerSumUpTo
    (coeff : Nat → ZMod64 p) :
    Nat → Nat → FpPoly p → FpPoly p
  | 0, _, _ => 0
  | n + 1, base, w =>
      DensePoly.C (coeff base) * linearPow w base +
        composeCoeffPowerSumUpTo coeff n (base + 1) w

private theorem composePower_eq_linearPow (w : FpPoly p) :
    ∀ k, DensePoly.composePower w k = linearPow w k
  | 0 => rfl
  | k + 1 => by
      simp only [DensePoly.composePower]
      rw [composePower_eq_linearPow w k]
      rw [linearPow_succ_left]

/-- The local `FpPoly` power-sum accumulator built from `linearPow` agrees
with the shared `DensePoly.composeCoeffPowerSumUpTo`. Callers use this to
transfer the explicit compose-as-sum characterization onto the `DensePoly`
API that downstream files import. -/
theorem composeCoeffPowerSumUpTo_eq_core
    (coeff : Nat → ZMod64 p) :
    ∀ n base w,
      composeCoeffPowerSumUpTo coeff n base w =
        DensePoly.composeCoeffPowerSumUpTo coeff n base w
  | 0, _, _ => rfl
  | n + 1, base, w => by
      simp only [composeCoeffPowerSumUpTo, DensePoly.composeCoeffPowerSumUpTo]
      rw [composePower_eq_linearPow]
      rw [composeCoeffPowerSumUpTo_eq_core coeff n (base + 1) w]

/-- The list-fed accumulator `composeCoeffPowerSumFrom` over the coefficient
slice `[coeff base, …, coeff (base + n - 1)]` agrees with the index-fed
`composeCoeffPowerSumUpTo coeff n base w`. This bridges the two power-sum
representations so the explicit list form can be rewritten into the bounded
indexed form used by the extension and subtraction lemmas. -/
private theorem composeCoeffPowerSumFrom_range_eq_upTo
    (coeff : Nat → ZMod64 p) (w : FpPoly p) :
    ∀ n base,
      composeCoeffPowerSumFrom ((List.range n).map (fun i => coeff (base + i))) base w =
        composeCoeffPowerSumUpTo coeff n base w
  | 0, base => by
      simp [composeCoeffPowerSumFrom, composeCoeffPowerSumUpTo]
  | n + 1, base => by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      simp only [composeCoeffPowerSumFrom, composeCoeffPowerSumUpTo]
      congr 1
      simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using composeCoeffPowerSumFrom_range_eq_upTo coeff w n (base + 1)

/-- `compose f w` equals the bounded accumulator `composeCoeffPowerSumUpTo`
run up to exactly `f.size` with `f`'s coefficients. This is the base
characterization of composition as a power sum, from which the
extend-past-the-bound variant `compose_eq_coeff_power_sum_upTo_bound` follows. -/
private theorem compose_eq_coeff_power_sum_upTo_size (f w : FpPoly p) :
    DensePoly.compose f w =
      composeCoeffPowerSumUpTo (fun i => f.coeff i) f.size 0 w := by
  rw [compose_eq_powerSum]
  rw [DensePoly.toArray_toList_eq_coeff_range]
  simpa using composeCoeffPowerSumFrom_range_eq_upTo (fun i => f.coeff i) w f.size 0

/-- Single-step extension invariance: when the next coefficient
`coeff (base + n)` is zero, growing the accumulator's bound from `n` to `n + 1`
leaves its value unchanged, since the appended term contributes `C 0 * wⁱ = 0`.
This is the inductive step behind the multi-step `_le_extend_base` lemma. -/
private theorem composeCoeffPowerSumUpTo_succ_of_next_zero
    (coeff : Nat → ZMod64 p) (w : FpPoly p) :
    ∀ n base,
      coeff (base + n) = 0 →
        composeCoeffPowerSumUpTo coeff n base w =
          composeCoeffPowerSumUpTo coeff (n + 1) base w
  | 0, base, hzero => by
      have hz : coeff base = 0 := by simpa using hzero
      show (0 : FpPoly p) =
        DensePoly.C (coeff base) * linearPow w base +
          composeCoeffPowerSumUpTo coeff 0 (base + 1) w
      rw [hz]
      rw [show (DensePoly.C (0 : ZMod64 p) : FpPoly p) = 0 from C_zero_eq_zero]
      rw [FpPoly.zero_mul]
      show (0 : FpPoly p) = 0 + composeCoeffPowerSumUpTo coeff 0 (base + 1) w
      rw [FpPoly.zero_add]
      rfl
  | n + 1, base, hzero => by
      simp only [composeCoeffPowerSumUpTo]
      rw [composeCoeffPowerSumUpTo_succ_of_next_zero coeff w n (base + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzero)]
      simp only [composeCoeffPowerSumUpTo]

/-- Multi-step extension invariance (general base): if every coefficient from
index `base + bound` onward vanishes, then running the accumulator up to
`bound + extra` gives the same value as running it up to `bound`, for any
`extra`. Proved by iterating `_succ_of_next_zero`. -/
private theorem composeCoeffPowerSumUpTo_le_extend_base
    (coeff : Nat → ZMod64 p) (w : FpPoly p) {base bound : Nat}
    (hzero : ∀ i, base + bound ≤ i → coeff i = 0) :
    ∀ extra,
      composeCoeffPowerSumUpTo coeff bound base w =
        composeCoeffPowerSumUpTo coeff (bound + extra) base w
  | 0 => by
      simp
  | extra + 1 => by
      rw [composeCoeffPowerSumUpTo_le_extend_base coeff w hzero extra]
      rw [Nat.add_succ]
      exact composeCoeffPowerSumUpTo_succ_of_next_zero
        coeff w (bound + extra) base (hzero (base + (bound + extra)) (by omega))

/-- The `base = 0` specialization of `_le_extend_base`: when all coefficients
at indices `≥ bound` vanish, the accumulator's value is unchanged by extending
its bound to `bound + extra`. This is the form consumed by
`compose_eq_coeff_power_sum_upTo_bound`. -/
private theorem composeCoeffPowerSumUpTo_le_extend
    (coeff : Nat → ZMod64 p) (w : FpPoly p) {bound : Nat}
    (hzero : ∀ i, bound ≤ i → coeff i = 0) :
    ∀ extra,
      composeCoeffPowerSumUpTo coeff bound 0 w =
        composeCoeffPowerSumUpTo coeff (bound + extra) 0 w := by
  intro extra
  exact composeCoeffPowerSumUpTo_le_extend_base
    coeff w (base := 0) (bound := bound) (by simpa using hzero) extra

/-- `compose f w` equals `composeCoeffPowerSumUpTo` evaluated up to any
upper bound that is at least `f.size`. Out-of-range coefficients of `f`
vanish, so the recursion safely extends past `f.size`. -/
theorem compose_eq_coeff_power_sum_upTo_bound (f w : FpPoly p)
    {bound : Nat} (hbound : f.size ≤ bound) :
    DensePoly.compose f w =
      composeCoeffPowerSumUpTo (fun i => f.coeff i) bound 0 w := by
  rw [compose_eq_coeff_power_sum_upTo_size]
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hbound
  exact composeCoeffPowerSumUpTo_le_extend
    (fun i => f.coeff i) w
    (fun i hi => DensePoly.coeff_eq_zero_of_size_le f hi) extra

/-! ### Distributivity of compose over subtraction

The rearrangement
`(C a - C b) * w^k + (S_a - S_b) = (C a * w^k + S_a) - (C b * w^k + S_b)`
is the key ring step. We prove it via the coefficient-level argument:
the multiplication `(a - b) * c = a*c - b*c` follows from `right_distrib`
and `DensePoly.neg_mul_right_poly`; the residual identity
`(x - y) + (u - v) = (x + u) - (y + v)` reduces to a pointwise ZMod64
identity through `DensePoly.ext_coeff`. -/

private theorem fp_sub_mul_right
    (a b c : FpPoly p) :
    (a - b) * c = a * c - b * c := by
  rw [FpPoly.sub_eq_add_neg a b]
  rw [FpPoly.right_distrib]
  rw [FpPoly.sub_eq_add_neg (a * c) (b * c)]
  congr 1
  show ((0 - b : FpPoly p) * c) = 0 - b * c
  exact DensePoly.neg_mul_right_poly b c

private theorem fp_add_sub_add_sub
    (x y u v : FpPoly p) :
    (x - y) + (u - v) = (x + u) - (y + v) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  grind

/-- The accumulator is additive under coefficient subtraction: running
`composeCoeffPowerSumUpTo` with the pointwise difference `f.coeff i - h.coeff i`
equals the difference of the two separate accumulators. This linearity step
feeds the `compose_sub` distributivity theorem. -/
private theorem composeCoeffPowerSumUpTo_sub
    (f h w : FpPoly p) :
    ∀ n base,
      composeCoeffPowerSumUpTo (fun i => f.coeff i - h.coeff i) n base w =
        composeCoeffPowerSumUpTo (fun i => f.coeff i) n base w -
          composeCoeffPowerSumUpTo (fun i => h.coeff i) n base w
  | 0, _ => by
      simp [composeCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [composeCoeffPowerSumUpTo]
      rw [composeCoeffPowerSumUpTo_sub f h w n (base + 1)]
      rw [C_sub_eq]
      rw [fp_sub_mul_right (DensePoly.C (f.coeff base))
        (DensePoly.C (h.coeff base)) (linearPow w base)]
      exact fp_add_sub_add_sub
        (DensePoly.C (f.coeff base) * linearPow w base)
        (DensePoly.C (h.coeff base) * linearPow w base)
        (composeCoeffPowerSumUpTo (fun i => f.coeff i) n (base + 1) w)
        (composeCoeffPowerSumUpTo (fun i => h.coeff i) n (base + 1) w)

private theorem fp_size_le_of_coeff_eq_zero_from
    (f : FpPoly p) (bound : Nat)
    (hzero : ∀ i, bound ≤ i → f.coeff i = 0) :
    f.size ≤ bound := by
  by_cases hle : f.size ≤ bound
  · exact hle
  · have hgt : bound < f.size := Nat.lt_of_not_ge hle
    have hpos : 0 < f.size := by omega
    have htop_zero : f.coeff (f.size - 1) = 0 := hzero (f.size - 1) (by omega)
    exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f hpos htop_zero)

private theorem fp_size_sub_le
    (f h : FpPoly p) :
    (f - h).size ≤ max f.size h.size := by
  apply fp_size_le_of_coeff_eq_zero_from
  intro i hi
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_eq_zero_of_size_le f
      (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
    DensePoly.coeff_eq_zero_of_size_le h
      (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
  exact (by grind : (0 : ZMod64 p) - 0 = 0)

/-- `compose` distributes over subtraction. -/
theorem compose_sub [ZMod64.PrimeModulus p] (f h w : FpPoly p) :
    DensePoly.compose (f - h) w = DensePoly.compose f w - DensePoly.compose h w := by
  let bound := max f.size h.size
  rw [compose_eq_coeff_power_sum_upTo_bound (f - h) w (bound := bound)
      (fp_size_sub_le f h)]
  rw [compose_eq_coeff_power_sum_upTo_bound f w (bound := bound)
      (Nat.le_max_left f.size h.size)]
  rw [compose_eq_coeff_power_sum_upTo_bound h w (bound := bound)
      (Nat.le_max_right f.size h.size)]
  have hcoeff :
      (fun i => (f - h).coeff i) =
        (fun i => f.coeff i - h.coeff i) := by
    funext i
    rw [DensePoly.coeff_sub_ring]
  rw [hcoeff]
  exact composeCoeffPowerSumUpTo_sub f h w bound 0

/-- Narrow specialisation needed by the witness-substitution caller:
substituting `w` for `X` in `a - X` yields `compose a w - w`. -/
theorem compose_sub_X [ZMod64.PrimeModulus p] (a w : FpPoly p) :
    DensePoly.compose (a - FpPoly.X) w = DensePoly.compose a w - w := by
  rw [compose_sub]
  rw [compose_X]

/-- The headline `linearPow X k - X` substitution: substituting `w`
for `X` in `linearPow X k - X` yields `linearPow w k - w`. -/
theorem compose_linearPow_X_sub_X
    [ZMod64.PrimeModulus p] (w : FpPoly p) (k : Nat) :
    DensePoly.compose (FpPoly.linearPow FpPoly.X k - FpPoly.X) w =
      FpPoly.linearPow w k - w := by
  rw [compose_sub]
  rw [compose_linearPow_X, compose_X]

/-! ### Substitution into `a * (X - C c)`

Substituting `w` into `a * (X - FpPoly.C c)` yields
`compose a w * (w - FpPoly.C c)`. The proof goes through a list-level
coefficient model: `mulXSubCList c cs` is the coefficient list of
`(ofCoeffs cs.toArray) * (X - C c)`, and `DensePoly.composeScalarCoeffList`
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

/-- `DensePoly.composeScalarCoeffList` ignores trailing zeros. -/
private theorem composeScalarCoeffList_trim
    [ZMod64.PrimeModulus p] (q : FpPoly p) :
    ∀ cs : List (ZMod64 p),
      DensePoly.composeScalarCoeffList (DensePoly.trimTrailingZerosList cs) q =
        DensePoly.composeScalarCoeffList cs q
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
        -- hih : DensePoly.composeScalarCoeffList [] q = DensePoly.composeScalarCoeffList cs q
        -- Goal: DensePoly.composeScalarCoeffList [] q = DensePoly.composeScalarCoeffList (c :: cs) q
        --     = DensePoly.C c + q * DensePoly.composeScalarCoeffList cs q
        --     = DensePoly.C 0 + q * DensePoly.composeScalarCoeffList cs q  (using hc)
        --     = 0 + q * 0  (via hih)
        --     = 0
        -- And LHS = DensePoly.composeScalarCoeffList [] q = 0.
        rw [hc]
        simp only [DensePoly.composeScalarCoeffList]
        rw [← hih]
        change DensePoly.composeScalarCoeffList [] q =
          (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) +
            q * DensePoly.composeScalarCoeffList [] q
        simp only [DensePoly.composeScalarCoeffList]
        rw [show (DensePoly.C (Zero.zero : ZMod64 p) : FpPoly p) = 0 from
          fp_C_zero]
        rw [FpPoly.mul_zero, FpPoly.zero_add]
      · rw [if_neg htrim]
        simp only [DensePoly.composeScalarCoeffList]
        rw [composeScalarCoeffList_trim q cs]

/-- `compose` on a polynomial built from a raw coefficient list agrees with
`DensePoly.composeScalarCoeffList` on that list, even if the list has trailing zeros. -/
private theorem compose_ofCoeffs_eq_composeScalarCoeffList
    [ZMod64.PrimeModulus p] (cs : List (ZMod64 p)) (q : FpPoly p) :
    DensePoly.compose (DensePoly.ofCoeffs cs.toArray : FpPoly p) q =
      DensePoly.composeScalarCoeffList cs q := by
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

/-- The list-level recurrence: `DensePoly.composeScalarCoeffList (mulXSubCListAux c prev cs) w`
collapses to `DensePoly.composeScalarCoeffList cs w * (w - C c) + C prev`. -/
private theorem composeScalarCoeffList_mulXSubCListAux
    [ZMod64.PrimeModulus p] (c : ZMod64 p) (w : FpPoly p) :
    ∀ (prev : ZMod64 p) (cs : List (ZMod64 p)),
      DensePoly.composeScalarCoeffList (mulXSubCListAux c prev cs) w =
        DensePoly.composeScalarCoeffList cs w * (w - FpPoly.C c) + FpPoly.C prev
  | prev, [] => by
      simp only [mulXSubCListAux, DensePoly.composeScalarCoeffList]
      -- Goal: DensePoly.C prev + w * 0 = 0 * (w - C c) + C prev
      rw [FpPoly.mul_zero, FpPoly.zero_mul]
      rw [FpPoly.add_zero, FpPoly.zero_add]
      rfl
  | prev, x :: xs => by
      simp only [mulXSubCListAux, DensePoly.composeScalarCoeffList]
      rw [composeScalarCoeffList_mulXSubCListAux c w x xs]
      rw [C_sub_eq, C_mul_C_eq]
      -- Goal:
      --   DensePoly.C prev - DensePoly.C c * DensePoly.C x +
      --     w * (S * (w - C c) + C x) =
      --   (C x + w * S) * (w - C c) + C prev
      -- where S := DensePoly.composeScalarCoeffList xs w.
      exact alg_compose_step (FpPoly.C prev) (FpPoly.C c) (FpPoly.C x) w
        (DensePoly.composeScalarCoeffList xs w)

/-- The specialised list-level recurrence with `prev = 0`. -/
private theorem composeScalarCoeffList_mulXSubCList
    [ZMod64.PrimeModulus p] (c : ZMod64 p) (w : FpPoly p) (cs : List (ZMod64 p)) :
    DensePoly.composeScalarCoeffList (mulXSubCList c cs) w =
      DensePoly.composeScalarCoeffList cs w * (w - FpPoly.C c) := by
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
  have hzero_mul_c : c * (0 : ZMod64 p) = 0 := by grind
  -- LHS computation
  have hLHS : (a * (FpPoly.X - FpPoly.C c)).coeff n =
      (if n = 0 then (0 : ZMod64 p) else a.coeff (n - 1)) - c * a.coeff n := by
    rw [FpPoly.mul_comm a (FpPoly.X - FpPoly.C c)]
    have hneg_mul : (-(FpPoly.C c) : FpPoly p) * a = -(FpPoly.C c * a) := by
      show (0 - FpPoly.C c) * a = 0 - FpPoly.C c * a
      exact DensePoly.neg_mul_right_poly (FpPoly.C c) a
    rw [sub_eq_add_neg, right_distrib]
    rw [DensePoly.coeff_add_semiring]
    rw [hneg_mul]
    rw [DensePoly.coeff_neg_ring]
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

/-- Composition distributes over multiplication by a linear factor:
substituting `w` into `a * (X - C c)` gives `(compose a w) * (w - C c)`.
This is the inductive step for composing an iterated product of linear
factors `∏ (X - C cᵢ)` (see `compose_foldl_X_sub_C`). -/
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

/-! ### Compose-form Frobenius

The substitution identity `compose w (linearPow X p) = linearPow w p` over
`F_p` packages Freshman's dream applied to a polynomial: viewing
`w = ∑_i a_i X^i`, the right-hand side equals `∑_i a_i X^(p·i)` (using
Fermat for the constants), which is exactly the left-hand side after
unfolding the compose power-sum form. This is the foundational identity
that the Berlekamp matrix correspondence uses to read each column of
`berlekampMatrix` as `coeffVector f (linearPow X (p·j) mod f)`. -/

private theorem linearPow_linearPow_mul (a : FpPoly p) (m : Nat) :
    ∀ n, FpPoly.linearPow (FpPoly.linearPow a m) n = FpPoly.linearPow a (m * n)
  | 0 => by
      rw [Nat.mul_zero]
      rfl
  | n + 1 => by
      rw [FpPoly.linearPow_succ, linearPow_linearPow_mul a m n,
        Nat.mul_succ, FpPoly.linearPow_add]

/-- A strictly positive power of the zero polynomial is zero. This
discharges the vanishing-coefficient case when substituting into the
compose power-sum form for the Frobenius identity. -/
theorem linearPow_zero_of_pos (n : Nat) (hn : 0 < n) :
    FpPoly.linearPow (0 : FpPoly p) n = 0 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [FpPoly.linearPow_succ]
      exact FpPoly.mul_zero (FpPoly.linearPow (0 : FpPoly p) k)

private theorem composeCoeffPowerSumUpTo_subst_linearPow_X
    [ZMod64.PrimeModulus p] (coeff : Nat → ZMod64 p) :
    ∀ n base,
      composeCoeffPowerSumUpTo coeff n base
          (FpPoly.linearPow FpPoly.X p) =
        FpPoly.linearPow
          (composeCoeffPowerSumUpTo coeff n base FpPoly.X) p
  | 0, _ => by
      have hp_pos : 0 < p := by
        have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
        omega
      simp only [composeCoeffPowerSumUpTo]
      exact (linearPow_zero_of_pos p hp_pos).symm
  | n + 1, base => by
      simp only [composeCoeffPowerSumUpTo]
      rw [composeCoeffPowerSumUpTo_subst_linearPow_X coeff n (base + 1)]
      rw [FpPoly.linearPow_add_prime (ZMod64.PrimeModulus.prime (p := p))]
      rw [FpPoly.linearPow_mul_base]
      rw [Quotient.linearPow_C_pow_prime]
      rw [linearPow_linearPow_mul FpPoly.X base p]
      rw [linearPow_linearPow_mul FpPoly.X p base]
      rw [Nat.mul_comm base p]

private theorem composeCoeffPowerSumUpTo_X_coeff
    [ZMod64.PrimeModulus p] (coeff : Nat → ZMod64 p) :
    ∀ n base k,
      (composeCoeffPowerSumUpTo coeff n base FpPoly.X).coeff k =
        if base ≤ k ∧ k < base + n then coeff k else (Zero.zero : ZMod64 p)
  | 0, base, k => by
      simp only [composeCoeffPowerSumUpTo]
      rw [DensePoly.coeff_zero]
      have hneg : ¬ (base ≤ k ∧ k < base + 0) := by intro ⟨_, h⟩; omega
      rw [if_neg hneg]
      rfl
  | n + 1, base, k => by
      simp only [composeCoeffPowerSumUpTo]
      rw [DensePoly.coeff_add_semiring]
      rw [composeCoeffPowerSumUpTo_X_coeff coeff n (base + 1) k]
      rw [show FpPoly.linearPow (FpPoly.X : FpPoly p) base
              = DensePoly.monomial base (1 : ZMod64 p) from
              FpPoly.linearPow_monomial_one base]
      rw [show (DensePoly.C (coeff base) : FpPoly p) *
              DensePoly.monomial base (1 : ZMod64 p)
              = DensePoly.scale (coeff base)
                  (DensePoly.monomial base (1 : ZMod64 p)) from
              FpPoly.C_mul_eq_scale (coeff base)
                (DensePoly.monomial base (1 : ZMod64 p))]
      have hzz : (Zero.zero : ZMod64 p) = (0 : ZMod64 p) := rfl
      have hmul_zero : coeff base * (Zero.zero : ZMod64 p) = Zero.zero := by
        rw [hzz]; grind
      rw [DensePoly.coeff_scale _ _ _ hmul_zero]
      rw [DensePoly.coeff_monomial]
      have hzz_add : (Zero.zero : ZMod64 p) + Zero.zero = Zero.zero := by
        grind
      by_cases hk_base : k = base
      · rw [if_pos hk_base]
        have hneg' : ¬ (base + 1 ≤ k ∧ k < base + 1 + n) := by
          intro ⟨h, _⟩; omega
        rw [if_neg hneg']
        have hpos : base ≤ k ∧ k < base + (n + 1) := by
          refine ⟨?_, ?_⟩ <;> omega
        rw [if_pos hpos]
        have hmul_one : coeff base * (1 : ZMod64 p) = coeff k := by
          rw [hk_base]; grind
        rw [hmul_one]
        show coeff k + (Zero.zero : ZMod64 p) = coeff k
        rw [hzz]; grind
      · rw [if_neg hk_base]
        rw [hmul_zero]
        by_cases hkb : base ≤ k
        · have hk1 : base + 1 ≤ k := by omega
          by_cases hcond : k < base + (n + 1)
          · have hcond' : k < base + 1 + n := by omega
            rw [if_pos ⟨hk1, hcond'⟩, if_pos ⟨hkb, hcond⟩]
            rw [hzz]; grind
          · rw [if_neg (fun ⟨_, h⟩ => hcond (by omega))]
            rw [if_neg (fun ⟨_, h⟩ => hcond h)]
            exact hzz_add
        · have hk1 : ¬ (base + 1 ≤ k) := by omega
          rw [if_neg (fun ⟨h, _⟩ => hk1 h)]
          rw [if_neg (fun ⟨h, _⟩ => hkb h)]
          exact hzz_add

private theorem composeCoeffPowerSumUpTo_self_X_eq_self
    [ZMod64.PrimeModulus p] (w : FpPoly p) :
    composeCoeffPowerSumUpTo (fun i => w.coeff i) w.size 0 FpPoly.X = w := by
  apply DensePoly.ext_coeff
  intro k
  rw [composeCoeffPowerSumUpTo_X_coeff (fun i => w.coeff i) w.size 0 k]
  by_cases hk : k < w.size
  · simp [hk]
  · have hk' : w.size ≤ k := Nat.le_of_not_gt hk
    rw [if_neg (by intro ⟨_, h⟩; omega : ¬ (0 ≤ k ∧ k < 0 + w.size))]
    exact (DensePoly.coeff_eq_zero_of_size_le w hk').symm

/-- Compose-form Frobenius: substituting `linearPow X p` for `X` in `w`
yields `linearPow w p`, over `F_p`. This is Freshman's dream packaged
through the polynomial composition surface: viewed as
`w = ∑_i a_i X^i`, the right-hand side equals `∑_i a_i X^(p·i)`. -/
theorem compose_w_linearPow_X [ZMod64.PrimeModulus p] (w : FpPoly p) :
    DensePoly.compose w (FpPoly.linearPow FpPoly.X p) =
      FpPoly.linearPow w p := by
  rw [compose_eq_coeff_power_sum_upTo_size w (FpPoly.linearPow FpPoly.X p)]
  rw [composeCoeffPowerSumUpTo_subst_linearPow_X (fun i => w.coeff i) w.size 0]
  rw [composeCoeffPowerSumUpTo_self_X_eq_self w]

end FpPoly
end Hex
