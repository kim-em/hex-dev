/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public meta import HexPoly.Dense

public section

/-!
Fraction-free polynomial pseudo-division.

For `n = degree f`, `m = degree g`, `d = n - m + 1`, and `b = lc(g)`,
`pseudoDivMod` computes the coefficients of the usual pseudo-division loop
directly.  It first builds `b^0, ..., b^d`, then the successive cancelled
leading coefficients

```
a_i = b^i * f[n-i]
      - sum (a_j * b^(i-1-j) * g[m+j-i]),
```

where `max(0, i-m) <= j < i`.  The quotient coefficients are
`q[k] = a_(d-1-k) * b^k`; the low `m` coefficients of
`b^d*f - q*g` are the remainder.  This dynamic coefficient recurrence avoids
materializing and rescaling the full quotient and remainder at every
elimination step.  Its nested folds have `O(d*m)` summands and it uses
`O(d+m)` coefficient storage.

The fixed `b^d` factor is built into both output formulas.  Consequently the
residual scaling required when cancellation drops the degree by more than one
is automatic rather than a special loop case.

The function is total.  A zero divisor is a junk input and returns `(0, f)`.
An already-smaller dividend also returns `(0, f)`; this agrees with ordinary
division, although the fixed-exponent pseudo-division contract is stated only
for the degree-ordered case.
-/
namespace Hex.DensePoly

universe u v w

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Build `N` successive array entries, allowing each entry to inspect the
prefix built so far. -/
private def pushBuild {A : Type v} (N : Nat) (init : Array A)
    (step : Array A → Nat → A) : Array A :=
  (Array.range N).foldl (fun acc i => acc.push (step acc i)) init

/--
Polynomial pseudo-division without coefficient division.

For `g != 0` and `g.degree? <= f.degree?`, let
`d = f.degree - g.degree + 1`.  Over a commutative ring its result `(q, r)`
satisfies

```
lc(g) ^ (f.degree - g.degree + 1) * f = q * g + r
```

with `r.degree? < g.degree?`.  The implementation asks only for the concrete
operations it executes; algebraic laws belong to the correctness theorems.
Its nested array folds have `O(d*m)` summands, matching the
pseudo-division complexity contract.

For the two inputs outside that contract, behavior is deliberately simple and
stable: `pseudoDivMod f 0 = (0, f)`, and if `f` is already smaller than a
nonzero `g`, then `pseudoDivMod f g = (0, f)`.
-/
@[expose]
def pseudoDivMod [One R] [Add R] [Sub R] [Mul R]
    (f g : DensePoly R) : DensePoly R × DensePoly R :=
  if g.isZero then
    (0, f)
  else if f.size < g.size then
    (0, f)
  else
    let n := f.size - 1
    let m := g.size - 1
    let d := f.size - g.size + 1
    let b := g.leadingCoeff
    let powers :=
      (Array.range d).foldl
        (fun powers _ =>
          powers.push (powers.getD (powers.size - 1) 1 * b))
        #[1]
    let active :=
      (Array.range d).foldl
        (fun active i =>
          let first := i - m
          let correction :=
            (Array.range (i - first)).foldl
              (fun acc offset =>
                let j := first + offset
                acc + active.getD j 0 * powers.getD (i - 1 - j) 0 *
                  g.coeff (m + j - i))
              0
          active.push (powers.getD i 0 * f.coeff (n - i) - correction))
        #[]
    let quotient :=
      (Array.range d).foldl
        (fun coeffs k =>
          coeffs.push (active.getD (d - 1 - k) 0 * powers.getD k 0))
        #[]
    let remainder :=
      (Array.range m).foldl
        (fun coeffs t =>
          let correction :=
            (Array.range (min (t + 1) d)).foldl
              (fun acc k =>
                acc + quotient.getD k 0 * g.coeff (t - k))
              0
          coeffs.push (powers.getD d 0 * f.coeff t - correction))
        #[]
    (ofCoeffs quotient, ofCoeffs remainder)

/-- A zero divisor takes the documented junk branch and leaves the dividend unchanged. -/
@[simp, grind =]
theorem pseudoDivMod_zero_right [One R] [Add R] [Sub R] [Mul R] (f : DensePoly R) :
    pseudoDivMod f 0 = (0, f) := by
  rfl

/-- If the dividend is already smaller, pseudo-division is ordinary division by inspection. -/
theorem pseudoDivMod_of_size_lt [One R] [Add R] [Sub R] [Mul R]
    (f g : DensePoly R) (h : f.size < g.size) :
    pseudoDivMod f g = (0, f) := by
  have hg : g.isZero = false :=
    (isZero_eq_false_iff g).2 (by omega)
  simp [pseudoDivMod, hg, h]

/-- A fold that appends one value per input has the expected output size. -/
private theorem size_foldl_push {A : Type v} {B : Type w}
    (xs : Array A) (init : Array B)
    (f : A → B) :
    (xs.foldl (fun acc x => acc.push (f x)) init).size = init.size + xs.size := by
  rw [Array.foldl_push_eq_append (stop := xs.size) rfl]
  simp

/-- A dependent push build exposes its final append at a successor bound. -/
private theorem pushBuild_succ {A : Type v} (N : Nat) (init : Array A)
    (step : Array A → Nat → A) :
    pushBuild (N + 1) init step =
      (pushBuild N init step).push (step (pushBuild N init step) N) := by
  simp [pushBuild, Array.range_succ]

/-- A dependent push build appends exactly one entry per iteration. -/
private theorem pushBuild_size {A : Type v} (N : Nat) (init : Array A)
    (step : Array A → Nat → A) :
    (pushBuild N init step).size = init.size + N := by
  induction N with
  | zero =>
      rw [pushBuild,
        Array.range_eq_empty_iff.mpr rfl, Array.foldl_empty]
      omega
  | succ N ih =>
      rw [pushBuild_succ, Array.size_push, ih]
      omega

/-- Reading an entry appended by a dependent push build recovers the step
that created it. -/
private theorem pushBuild_getD {A : Type v}
    (N k : Nat) (init : Array A) (step : Array A → Nat → A)
    (fallback : A) (hk : k < N) :
    (pushBuild N init step).getD (init.size + k) fallback =
      step (pushBuild k init step) k := by
  induction N generalizing k with
  | zero => omega
  | succ N ih =>
      rw [pushBuild_succ]
      by_cases hkn : k = N
      · subst k
        have hsize : init.size + N = (pushBuild N init step).size := by
          rw [pushBuild_size]
        have hidx : init.size + N <
            ((pushBuild N init step).push
              (step (pushBuild N init step) N)).size := by
          rw [Array.size_push, pushBuild_size]
          omega
        rw [← Array.getElem_eq_getD fallback (h := hidx)]
        simpa only [hsize] using
          (Array.getElem_push_eq
            (xs := pushBuild N init step)
            (x := step (pushBuild N init step) N))
      · have hkN : k < N := by omega
        have hidxOld : init.size + k < (pushBuild N init step).size := by
          rw [pushBuild_size]
          omega
        have hidxNew : init.size + k <
            ((pushBuild N init step).push
              (step (pushBuild N init step) N)).size := by
          rw [Array.size_push, pushBuild_size]
          omega
        rw [← Array.getElem_eq_getD fallback (h := hidxNew),
          Array.getElem_push_lt hidxOld,
          Array.getElem_eq_getD fallback]
        exact ih k hkN

/-- Once an appended entry exists, extending a dependent push build leaves
that entry unchanged. -/
private theorem pushBuild_getD_stable {A : Type v}
    (N t k : Nat) (init : Array A) (step : Array A → Nat → A)
    (fallback : A) (hk : k < t) (ht : t ≤ N) :
    (pushBuild N init step).getD (init.size + k) fallback =
      (pushBuild t init step).getD (init.size + k) fallback := by
  rw [pushBuild_getD N k init step fallback (by omega),
    pushBuild_getD t k init step fallback hk]

/-- Appending leaves every existing `getD` entry unchanged. -/
private theorem getD_push_lt {A : Type v} (xs : Array A) (x fallback : A)
    (i : Nat) (hi : i < xs.size) :
    (xs.push x).getD i fallback = xs.getD i fallback := by
  have hi' : i < (xs.push x).size := by
    rw [Array.size_push]
    omega
  rw [← Array.getElem_eq_getD fallback (h := hi'),
    Array.getElem_push_lt hi, Array.getElem_eq_getD fallback]

/-- The final `getD` entry of a push is the appended value. -/
private theorem getD_push_eq {A : Type v} (xs : Array A) (x fallback : A) :
    (xs.push x).getD xs.size fallback = x := by
  have hi : xs.size < (xs.push x).size := by
    rw [Array.size_push]
    omega
  rw [← Array.getElem_eq_getD fallback (h := hi),
    Array.getElem_push_eq]

/-- The fallback of `getD` is irrelevant at an in-bounds index. -/
private theorem getD_fallback_eq {A : Type v} (xs : Array A)
    (i : Nat) (a b : A) (hi : i < xs.size) :
    xs.getD i a = xs.getD i b := by
  rw [← Array.getElem_eq_getD a (h := hi),
    Array.getElem_eq_getD b]

/-- The pseudo-division power table contains the expected consecutive powers
of the divisor's leading coefficient. -/
private theorem pseudoPowers_spec {S : Type u} [Lean.Grind.CommRing S]
    (b : S) (d : Nat) :
    let powers :=
      pushBuild d #[1] fun powers _ =>
        powers.getD (powers.size - 1) 1 * b
    powers.size = d + 1 ∧
      ∀ k, k ≤ d → powers.getD k 0 = b ^ k := by
  let step : Array S → Nat → S := fun powers _ =>
    powers.getD (powers.size - 1) 1 * b
  change
    (pushBuild d #[1] step).size = d + 1 ∧
      ∀ k, k ≤ d → (pushBuild d #[1] step).getD k 0 = b ^ k
  induction d with
  | zero =>
      constructor
      · rw [pushBuild_size]
        rfl
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        have hzero : pushBuild 0 #[1] step = #[1] := by
          rw [pushBuild, Array.range_eq_empty_iff.mpr rfl,
            Array.foldl_empty]
        rw [hzero]
        simp [Array.getD_eq_getD_getElem?,
          Lean.Grind.Semiring.pow_zero]
  | succ d ih =>
      constructor
      · rw [pushBuild_size]
        simp only [Array.size_singleton]
        omega
      · intro k hk
        rw [pushBuild_succ]
        by_cases hkd : k ≤ d
        · have hbound : k < (pushBuild d #[1] step).size := by
            rw [pushBuild_size]
            simp only [Array.size_singleton]
            omega
          rw [getD_push_lt _ _ _ _ hbound]
          exact ih.2 k hkd
        · have hkEq : k = d + 1 := by omega
          subst k
          have hnew :
              ((pushBuild d #[1] step).push
                (step (pushBuild d #[1] step) d)).getD (d + 1) 0 =
                step (pushBuild d #[1] step) d := by
            rw [show d + 1 = (pushBuild d #[1] step).size from ih.1.symm,
              getD_push_eq]
          rw [hnew]
          dsimp only [step]
          have hlast : (pushBuild d #[1] step).size - 1 = d := by
            rw [pushBuild_size]
            simp only [Array.size_singleton]
            omega
          rw [hlast]
          have hbound : d < (pushBuild d #[1] step).size := by
            rw [pushBuild_size]
            simp only [Array.size_singleton]
            omega
          rw [getD_fallback_eq _ _ 1 0 hbound, ih.2 d (by omega),
            Lean.Grind.Semiring.pow_succ]

/-- Coefficients of the raw pseudo-quotient are the reversed active
coefficients with their residual leading-coefficient scaling. -/
private theorem pseudoQuotient_coeff {S : Type u} [Zero S] [DecidableEq S]
    [Mul S] (active powers : Array S) (d k : Nat) :
    let quotient :=
      pushBuild d #[] fun _ k =>
        active.getD (d - 1 - k) 0 * powers.getD k 0
    (ofCoeffs quotient).coeff k =
      if k < d then
        active.getD (d - 1 - k) 0 * powers.getD k 0
      else 0 := by
  let step : Array S → Nat → S := fun _ k =>
    active.getD (d - 1 - k) 0 * powers.getD k 0
  change
    (ofCoeffs (pushBuild d #[] step)).coeff k =
      if k < d then
        active.getD (d - 1 - k) 0 * powers.getD k 0
      else 0
  rw [coeff_ofCoeffs]
  by_cases hk : k < d
  · rw [if_pos hk]
    have hget := pushBuild_getD d k #[] step (Zero.zero : S) hk
    simpa only [Array.size_empty, Nat.zero_add] using hget
  · rw [if_neg hk]
    have hsize : (pushBuild d #[] step).size ≤ k := by
      rw [pushBuild_size]
      simp only [Array.size_empty]
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsize]
    rfl

/-- Coefficients of the pseudo-remainder are the low coefficients of the
scaled dividend minus the bounded quotient-divisor convolution. -/
private theorem pseudoRemainder_coeff {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (f g : DensePoly S) (powers quotient : Array S)
    (d m t : Nat) :
    let q := ofCoeffs quotient
    let remainder :=
      pushBuild m #[] fun _ t =>
        let correction :=
          (Array.range (min (t + 1) d)).foldl
            (fun acc k =>
              acc + quotient.getD k (Zero.zero : S) * g.coeff (t - k))
            0
        powers.getD d 0 * f.coeff t - correction
    (ofCoeffs remainder).coeff t =
      if t < m then
        powers.getD d 0 * f.coeff t -
          (Array.range (min (t + 1) d)).foldl
            (fun acc k => acc + q.coeff k * g.coeff (t - k)) 0
      else 0 := by
  let step : Array S → Nat → S := fun _ t =>
    let correction :=
      (Array.range (min (t + 1) d)).foldl
        (fun acc k =>
          acc + quotient.getD k (Zero.zero : S) * g.coeff (t - k))
        0
    powers.getD d 0 * f.coeff t - correction
  change
    (ofCoeffs (pushBuild m #[] step)).coeff t =
      if t < m then
        powers.getD d 0 * f.coeff t -
          (Array.range (min (t + 1) d)).foldl
            (fun acc k =>
              acc + (ofCoeffs quotient).coeff k * g.coeff (t - k)) 0
      else 0
  rw [coeff_ofCoeffs]
  by_cases ht : t < m
  · rw [if_pos ht]
    dsimp only [step]
    have hget := pushBuild_getD m t #[] step (Zero.zero : S) ht
    dsimp only [step] at hget
    simpa only [Array.size_empty, Nat.zero_add, coeff_ofCoeffs] using hget
  · rw [if_neg ht]
    have hsize : (pushBuild m #[] step).size ≤ t := by
      rw [pushBuild_size]
      simp only [Array.size_empty]
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsize]
    rfl

/-- The contribution of the left coefficient `i` to product degree `t`. -/
private def diagonalTerm {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t i : Nat) : S :=
  if t < i then 0 else p.coeff i * q.coeff (t - i)

/-- The contribution of `i` while the inner multiplication fold is restricted
to the first `m` coefficients of the right factor. -/
private def boundedTerm {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t i m : Nat) : S :=
  if t < i then 0
  else if t - i < m then p.coeff i * q.coeff (t - i) else 0

/-- One inner schoolbook fold adds its bounded diagonal contribution. -/
private theorem fold_step_bounded {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t i m : Nat) (acc : S) :
    (List.range m).foldl (mulCoeffStep p q t i) acc =
      acc + boundedTerm p q t i m := by
  induction m generalizing acc with
  | zero =>
      simp [boundedTerm]
      exact (Lean.Grind.Semiring.add_zero acc).symm
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold mulCoeffStep boundedTerm
      by_cases hlt : t < i
      · have hne : i + m ≠ t := by omega
        simp [hlt, hne]
      · by_cases hm : t - i < m
        · have hne : i + m ≠ t := by omega
          simp [hlt, hm, hne]
          rw [if_pos (by omega)]
        · by_cases heq : i + m = t
          · have hsub : t - i = m := by omega
            simp [hlt, heq, hsub]
            rw [Lean.Grind.Semiring.add_zero]
          · have hm' : ¬ t - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- The complete inner schoolbook fold adds the full diagonal contribution. -/
private theorem fold_step_diagonal {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t i : Nat) (acc : S) :
    (List.range q.size).foldl (mulCoeffStep p q t i) acc =
      acc + diagonalTerm p q t i := by
  rw [fold_step_bounded]
  unfold boundedTerm diagonalTerm
  by_cases hlt : t < i
  · simp [hlt]
  · by_cases hbound : t - i < q.size
    · simp [hlt, hbound]
    · have hcoeff : q.coeff (t - i) = 0 :=
        coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hbound)
      simp [hlt, hbound, hcoeff]
      rw [Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]

/-- Replacing each inner multiplication fold by its diagonal contribution
preserves an arbitrary outer fold. -/
private theorem fold_outer_diagonal {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t : Nat)
    (xs : List Nat) (acc : S) :
    xs.foldl
        (fun coeff i =>
          (List.range q.size).foldl (mulCoeffStep p q t i) coeff)
        acc =
      xs.foldl (fun coeff i => coeff + diagonalTerm p q t i) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [fold_step_diagonal]
      exact ih (acc + diagonalTerm p q t i)

/-- The executable multiplication coefficient sum is its diagonal fold. -/
private theorem mulCoeffSum_diagonal {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t : Nat) :
    mulCoeffSum p q t =
      (List.range p.size).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 := by
  unfold mulCoeffSum
  exact fold_outer_diagonal p q t (List.range p.size) 0

/-- A diagonal contribution vanishes past the stored left support. -/
private theorem diagonal_zero_size {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t i : Nat)
    (hi : p.size ≤ i) : diagonalTerm p q t i = 0 := by
  unfold diagonalTerm
  by_cases hti : t < i
  · rw [if_pos hti]
  · rw [if_neg hti, coeff_eq_zero_of_size_le p hi]
    change (0 : S) * q.coeff (t - i) = 0
    rw [Lean.Grind.Semiring.zero_mul]

/-- A diagonal contribution vanishes past the target degree. -/
private theorem diagonal_zero_degree {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (t i : Nat) (hi : t < i) :
    diagonalTerm p q t i = 0 := by
  simp [diagonalTerm, hi]

/-- Extending a diagonal fold past the left support changes nothing. -/
private theorem diagonal_extend {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t d : Nat) :
    (List.range (p.size + d)).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 =
      (List.range p.size).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, diagonal_zero_size p q t (p.size + d) (by omega),
        Lean.Grind.Semiring.add_zero]

/-- A diagonal fold may be evaluated at any bound containing the left
support. -/
private theorem diagonal_bound {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t bound : Nat)
    (hp : p.size ≤ bound) :
    (List.range p.size).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 =
      (List.range bound).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 := by
  have hbound : p.size + (bound - p.size) = bound := by omega
  rw [← hbound]
  exact (diagonal_extend p q t (bound - p.size)).symm

/-- Extending the canonical degree fold changes nothing because all new
diagonal terms vanish. -/
private theorem diagonal_truncate {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t d : Nat) :
    (List.range (t + 1 + d)).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 =
      (List.range (t + 1)).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, diagonal_zero_degree p q t (t + 1 + d) (by omega),
        Lean.Grind.Semiring.add_zero]

/-- A diagonal fold over an ambient support bound truncates to the smaller of
that bound and the target degree range. -/
private theorem diagonal_min {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t bound : Nat) :
    (List.range bound).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 =
      (List.range (min (t + 1) bound)).foldl
        (fun acc i => acc + diagonalTerm p q t i) 0 := by
  by_cases hbound : bound ≤ t + 1
  · rw [Nat.min_eq_right hbound]
  · have hsum : t + 1 + (bound - (t + 1)) = bound := by omega
    rw [Nat.min_eq_left (by omega), ← hsum]
    exact diagonal_truncate p q t (bound - (t + 1))

/-- Pointwise-equal range-fold steps give equal accumulated results. -/
private theorem range_foldl_eq {A : Type v} (N : Nat)
    (f g : A → Nat → A) (init : A)
    (h : ∀ acc i, i < N → f acc i = g acc i) :
    (List.range N).foldl f init = (List.range N).foldl g init := by
  induction N generalizing init with
  | zero => rfl
  | succ N ih =>
      rw [List.range_succ]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (init := init) (fun acc i hi => h acc i (by omega))]
      exact h ((List.range N).foldl g init) N (by omega)

/-- The product coefficient is the bounded convolution used by the
pseudo-remainder builder. -/
private theorem coeff_mul_bounded {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] (p q : DensePoly S) (t bound : Nat)
    (hp : p.size ≤ bound) :
    (p * q).coeff t =
      (Array.range (min (t + 1) bound)).foldl
        (fun acc k => acc + p.coeff k * q.coeff (t - k)) 0 := by
  rw [coeff_mul, mulCoeffSum_diagonal, diagonal_bound p q t bound hp,
    diagonal_min]
  rw [← Array.foldl_toList]
  simp only [Array.toList_range]
  apply range_foldl_eq
  intro acc i hi
  unfold diagonalTerm
  rw [if_neg (by
    have himin : i < min (t + 1) bound := hi
    omega)]

/-- Pseudo-division reconstructs the fixed leading-coefficient multiple of the dividend.

This theorem deliberately uses a fresh coefficient type: an ambient `Zero`
instance is not necessarily coherent with the zero supplied by
`Lean.Grind.CommRing`. -/
theorem pseudoDivMod_reconstruct_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (f g : DensePoly S) (hg : g ≠ 0) (hfg : g.size ≤ f.size) :
    scale (g.leadingCoeff ^ (f.size - g.size + 1)) f =
      (pseudoDivMod f g).1 * g + (pseudoDivMod f g).2 := by
  sorry

/-- The quotient array is structurally bounded by the number of
pseudo-division rounds. This bound does not use reconstruction correctness. -/
theorem pseudoDivMod_quotient_size_le_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (f g : DensePoly S) (hg : g ≠ 0) (hfg : g.size ≤ f.size) :
    (pseudoDivMod f g).1.size ≤ f.size - g.size + 1 := by
  have hgpos : 0 < g.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hg
    apply ext_coeff
    intro i
    rw [coeff_zero]
    exact coeff_eq_zero_of_size_le g (by omega)
  have hgzero : g.isZero = false := (isZero_eq_false_iff g).2 hgpos
  simp only [pseudoDivMod, hgzero, Bool.false_eq_true, ↓reduceIte,
    Nat.not_lt_of_ge hfg]
  exact Nat.le_trans (size_ofCoeffs_le _) (by
    rw [size_foldl_push]
    simp only [Array.size_empty, Array.size_range]
    omega)

/-- The remainder array is structurally shorter than every nonzero divisor.
This follows from the output fold's iteration count and does not constrain the
computed coefficient values; reconstruction supplies the algebraic content. -/
theorem pseudoDivMod_remainder_lt_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (f g : DensePoly S) (hg : g ≠ 0) :
    (pseudoDivMod f g).2.size < g.size := by
  by_cases hlt : f.size < g.size
  · rw [pseudoDivMod_of_size_lt f g hlt]
    exact hlt
  · have hfg : g.size ≤ f.size := by omega
    have hgpos : 0 < g.size := by
      apply Nat.pos_of_ne_zero
      intro hsize
      apply hg
      apply ext_coeff
      intro i
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le g (by omega)
    have hgzero : g.isZero = false := (isZero_eq_false_iff g).2 hgpos
    simp only [pseudoDivMod, hgzero, Bool.false_eq_true, ↓reduceIte,
      Nat.not_lt_of_ge hfg]
    exact Nat.lt_of_le_of_lt (size_ofCoeffs_le _) (by
      rw [size_foldl_push]
      simp only [Array.size_empty, Array.size_range]
      omega)

/-! Small compiled regressions for the pseudo-division loop. -/

-- `4 * (X^2 + 1) = (2*X - 1) * (2*X + 1) + 5`.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 0, 1] : List Int))
        (ofList ([1, 2] : List Int))
    qr.1.toArray.toList = [-1, 2] ∧ qr.2.toArray.toList = [5]

-- Monic pseudo-division specializes to ordinary monic division.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 0, 1] : List Int))
        (ofList ([1, 1] : List Int))
    qr.1.toArray.toList = [-1, 1] ∧ qr.2.toArray.toList = [2]

-- Early cancellation still scales the quotient for every unused round.
#guard
    let qr := pseudoDivMod
        (ofList ([0, 0, 1] : List Int))
        (ofList ([0, 2] : List Int))
    qr.1.toArray.toList = [0, 2] ∧ qr.2.toArray.toList = []

-- A degree drop greater than one retains the residual leading-coefficient scaling.
-- `4*X^3 = (2*X)*(2*X^2 + 1) - 2*X`.
#guard
    let qr := pseudoDivMod
        (ofList ([0, 0, 0, 1] : List Int))
        (ofList ([1, 0, 2] : List Int))
    qr.1.toArray.toList = [0, 2] ∧ qr.2.toArray.toList = [0, -2]

-- Division by a constant uses all `degree(f) + 1` scaling rounds.
-- `27*(X^2 + 1) = (9*X^2 + 9)*3`.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 0, 1] : List Int))
        (ofList ([3] : List Int))
    qr.1.toArray.toList = [9, 0, 9] ∧ qr.2.toArray.toList = []

-- Equal-degree inputs take one round: `2*(X + 1) = 2*X + 3 - 1`.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 1] : List Int))
        (ofList ([3, 2] : List Int))
    qr.1.toArray.toList = [1] ∧ qr.2.toArray.toList = [-1]

-- An already-smaller dividend is returned unchanged as the remainder.
#guard
    let qr := pseudoDivMod
        (ofList ([3] : List Int))
        (ofList ([1, 1] : List Int))
    qr.1.toArray.toList = [] ∧ qr.2.toArray.toList = [3]

-- The zero dividend takes the smaller-degree branch for a nonconstant divisor.
#guard
    let qr := pseudoDivMod 0 (ofList ([1, 1] : List Int))
    qr.1.toArray.toList = ([] : List Int) ∧ qr.2.toArray.toList = []

-- The documented zero-divisor junk case is total and leaves the dividend alone.
#guard
    let qr := pseudoDivMod (ofList ([1, 0, 1] : List Int)) 0
    qr.1.toArray.toList = ([] : List Int) ∧ qr.2.toArray.toList = [1, 0, 1]

end Hex.DensePoly
