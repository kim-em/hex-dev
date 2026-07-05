/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Grind.Ring.Basic
public import Init.Data.List.Lemmas
public import HexPoly.Operations
public import HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.DivGcd

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Diagonal multiplication-coefficient convolution and the commutative-ring
operations on `DensePoly`: distributivity, associativity, the derivative
Leibniz rule, and monomial multiplication.
-/
namespace Hex

universe u

namespace DensePoly

/-- The `i`-th summand of the degree-`n` convolution diagonal of `p * q`,
`p.coeff i * q.coeff (n - i)`, zeroed once the degree guard `n < i` fires;
the single-index term that `mulCoeffSum` is reorganised into. -/
@[expose]
def diagonalMulCoeffTerm {S : Type _} [Zero S] [DecidableEq S] [Mul S]
    (p q : DensePoly S) (n i : Nat) : S :=
  if n < i then 0 else p.coeff i * q.coeff (n - i)

/-- Like `diagonalMulCoeffTerm`, but additionally zeroed once the partner index
`n - i` reaches the cutoff `m`; the partial value of the inner schoolbook fold
restricted to `List.range m`. -/
private def boundedDiagonalMulCoeffTerm {S : Type _} [Zero S] [DecidableEq S] [Mul S]
    (p q : DensePoly S) (n i m : Nat) : S :=
  if n < i then 0 else if n - i < m then p.coeff i * q.coeff (n - i) else 0

/-- Folding `mulCoeffStep` over `List.range m` accumulates exactly
`acc + boundedDiagonalMulCoeffTerm p q n i m`, identifying one truncated inner
schoolbook fold with its bounded diagonal term. -/
private theorem fold_mulCoeffStep_eq_bounded_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i m : Nat) (acc : S) :
    (List.range m).foldl (mulCoeffStep p q n i) acc =
      acc + boundedDiagonalMulCoeffTerm p q n i m := by
  induction m generalizing acc with
  | zero =>
      simp [boundedDiagonalMulCoeffTerm]
      grind
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold mulCoeffStep boundedDiagonalMulCoeffTerm
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
            grind
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- Folding `mulCoeffStep` over the full `List.range q.size` yields
`acc + diagonalMulCoeffTerm p q n i`, since coefficients past `q.size` vanish;
the unbounded specialisation of `fold_mulCoeffStep_eq_bounded_diagonal`. -/
private theorem fold_mulCoeffStep_eq_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (acc : S) :
    (List.range q.size).foldl (mulCoeffStep p q n i) acc =
      acc + diagonalMulCoeffTerm p q n i := by
  rw [fold_mulCoeffStep_eq_bounded_diagonal]
  unfold boundedDiagonalMulCoeffTerm diagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
  · by_cases hbound : n - i < q.size
    · simp [hlt, hbound]
    · have hcoeff : q.coeff (n - i) = 0 :=
        coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hbound)
      simp [hlt, hbound, hcoeff]
      grind

/-- Rewrites the outer schoolbook fold, where each index `i` runs an inner
`mulCoeffStep` fold, into the pointwise diagonal fold adding
`diagonalMulCoeffTerm p q n i` at each step. -/
private theorem fold_mulCoeff_outer_eq_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) (xs : List Nat) (acc : S) :
    xs.foldl (fun coeff i => (List.range q.size).foldl (mulCoeffStep p q n i) coeff) acc =
      xs.foldl (fun coeff i => coeff + diagonalMulCoeffTerm p q n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [fold_mulCoeffStep_eq_diagonal]
      exact ih (acc + diagonalMulCoeffTerm p q n i)

/-- The schoolbook coefficient `mulCoeffSum p q n` equals the diagonal sum
`Σ_{i < p.size} diagonalMulCoeffTerm p q n i`; the bridge from the executable
loop order to the convolution form used in the ring-law proofs. -/
theorem mulCoeffSum_eq_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    mulCoeffSum p q n =
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  unfold mulCoeffSum
  exact fold_mulCoeff_outer_eq_diagonal p q n (List.range p.size) 0

/-- A diagonal term vanishes once `p.size ≤ i`, because `p.coeff i = 0` past the
support of `p`; lets diagonal sums ignore indices beyond `p`'s degree. -/
private theorem diagonalMulCoeffTerm_eq_zero_of_size_le {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (hi : p.size ≤ i) :
    diagonalMulCoeffTerm p q n i = 0 := by
  unfold diagonalMulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : p.coeff i = 0 := coeff_eq_zero_of_size_le p hi
    simp [hn, hcoeff]
    grind

/-- Extending the diagonal-sum range from `p.size` to `p.size + d` adds only
zero terms, so the sum is unchanged; the range-extension invariance backing
`diagonalSum_eq_bound`. -/
private theorem fold_diagonal_extend {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n d : Nat) :
    (List.range (p.size + d)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : diagonalMulCoeffTerm p q n (p.size + d) = 0 :=
        diagonalMulCoeffTerm_eq_zero_of_size_le p q n (p.size + d) (by omega)
      simp [hterm]
      grind

/-- The diagonal sum over `List.range p.size` equals the sum over any larger
range `m ≥ p.size`; lets callers normalise the upper bound to a common value. -/
private theorem diagonalSum_eq_bound {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n m : Nat) (hm : p.size ≤ m) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range m).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  have hm' : p.size + (m - p.size) = m := by omega
  rw [← hm']
  exact (fold_diagonal_extend p q n (m - p.size)).symm

/-- A diagonal term vanishes when `n < i`, the degree guard built into
`diagonalMulCoeffTerm`; lets diagonal sums be truncated at degree `n`. -/
private theorem diagonalMulCoeffTerm_eq_zero_of_degree_lt {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (hi : n < i) :
    diagonalMulCoeffTerm p q n i = 0 := by
  simp [diagonalMulCoeffTerm, hi]

/-- Extending the diagonal-sum range past `n + 1` adds only zero terms, since
every index `> n` contributes `0`, so the sum equals the one over
`List.range (n + 1)`; the degree-side truncation invariance. -/
private theorem fold_diagonal_truncate_degree {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n d : Nat) :
    (List.range (n + 1 + d)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : diagonalMulCoeffTerm p q n (n + 1 + d) = 0 :=
        diagonalMulCoeffTerm_eq_zero_of_degree_lt p q n (n + 1 + d) (by omega)
      simp [hterm]
      grind

/-- The diagonal sum over `List.range p.size` equals the sum over
`List.range (n + 1)`; the canonical degree-`n` truncation of the convolution,
independent of `p.size`. -/
private theorem diagonalSum_eq_degree_bound {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  by_cases hsize : p.size ≤ n + 1
  · exact diagonalSum_eq_bound p q n (n + 1) hsize
  · have hsize' : n + 1 + (p.size - (n + 1)) = p.size := by omega
    rw [← hsize']
    exact fold_diagonal_truncate_degree p q n (p.size - (n + 1))

/-- Folding `(· + ·)` from the seed `a + b` factors the right summand back out:
`foldl (+) (a + b) = foldl (+) a + b`; a Mathlib-free associativity/commutativity
shim over `Lean.Grind.CommRing`. -/
private theorem fold_add_right_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List S) (a b : S) :
    xs.foldl (fun acc x => acc + x) (a + b) =
      xs.foldl (fun acc x => acc + x) a + b := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + x = (a + x) + b := by grind
      rw [hacc]
      exact ih (a + x)

/-- Summing a list with `foldl (· + ·)` is invariant under `List.reverse`; lets a
diagonal sum be reindexed by reversing the index list. -/
private theorem fold_add_reverse_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List S) (a : S) :
    xs.reverse.foldl (fun acc x => acc + x) a =
      xs.foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, fold_add_right_commring xs a x]

/-- `(List.range (n + 1)).reverse = (List.range (n + 1)).map (fun i => n - i)`; the
index reflection `i ↦ n - i` underlying the convolution commutativity reindexing. -/
private theorem range_succ_reverse_eq_map_sub (n : Nat) :
    (List.range (n + 1)).reverse = (List.range (n + 1)).map (fun i => n - i) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.length_reverse] at hleft hright
    rw [List.getElem_reverse]
    simp [List.getElem_map, List.getElem_range]

/-- Under the reflection `i ↦ n - i` (for `i < n + 1`), the diagonal term of
`p, q` becomes that of `q, p`:
`diagonalMulCoeffTerm p q n (n - i) = diagonalMulCoeffTerm q p n i`; the pointwise
core of convolution commutativity. -/
private theorem diagonalMulCoeffTerm_comm_reindex {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (hi : i < n + 1) :
    diagonalMulCoeffTerm p q n (n - i) = diagonalMulCoeffTerm q p n i := by
  have hile : i ≤ n := by omega
  have hleft : ¬ n < n - i := by omega
  have hright : ¬ n < i := by omega
  simp [diagonalMulCoeffTerm, hleft, hright, Nat.sub_sub_self hile]
  grind

/-- Pointwise application of `diagonalMulCoeffTerm_comm_reindex` across a fold over
indices all `< n + 1`, swapping each reflected `p, q` term for the matching
`q, p` term; the list-level step toward `fold_diagonal_comm`. -/
private theorem fold_diagonal_comm_reindex_list {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) (xs : List Nat)
    (hxs : ∀ i, i ∈ xs → i < n + 1) (acc : S) :
    xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p q n (n - i)) acc =
      xs.foldl (fun acc i => acc + diagonalMulCoeffTerm q p n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : i < n + 1 := hxs i (by simp)
      rw [diagonalMulCoeffTerm_comm_reindex p q n i hi]
      exact ih (by
        intro j hj
        exact hxs j (by simp [hj])) (acc + diagonalMulCoeffTerm q p n i)

/-- The degree-`n` diagonal sum is symmetric in its factors:
`Σ diagonalMulCoeffTerm p q n i = Σ diagonalMulCoeffTerm q p n i`; the
commutativity of the convolution coefficient, proved by reversal-reindexing. -/
private theorem fold_diagonal_comm {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm q p n i) 0 := by
  have hrev :
      (List.range (n + 1)).reverse.foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
        (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
    simpa [List.foldl_map, ← List.map_reverse] using
      fold_add_reverse_commring (S := S)
        ((List.range (n + 1)).map (fun i => diagonalMulCoeffTerm p q n i)) 0
  rw [← hrev, range_succ_reverse_eq_map_sub, List.foldl_map]
  exact fold_diagonal_comm_reindex_list p q n (List.range (n + 1)) (by
    intro i hi
    exact List.mem_range.mp hi) 0

/-- Negating the right factor negates the diagonal term:
`diagonalMulCoeffTerm p (0 - q) n i = 0 - diagonalMulCoeffTerm p q n i`. -/
private theorem diagonalMulCoeffTerm_neg_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) :
    diagonalMulCoeffTerm p (0 - q) n i = 0 - diagonalMulCoeffTerm p q n i := by
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  unfold diagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
    grind
  · rw [coeff_sub 0 q (n - i) hzero_sub, coeff_zero]
    simp [hlt]
    grind

/-- List-level form of `diagonalSum_neg_right`: folding the negated-right diagonal
terms over `xs` from `acc` equals `acc - (fold of the positive terms from 0)`; the
induction backing the closed negation law. -/
private theorem diagonalSum_neg_right_aux {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) (xs : List Nat) (acc : S) :
    xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p (0 - q) n i) acc =
      acc - xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [diagonalMulCoeffTerm_neg_right, ih]
      have htail :=
        fold_add_right_commring (S := S)
          (xs.map (fun i => diagonalMulCoeffTerm p q n i)) 0 (diagonalMulCoeffTerm p q n i)
      simp [List.foldl_map] at htail
      rw [htail]
      grind

/-- Negating the right factor negates the whole degree-`n` diagonal sum:
`Σ diagonalMulCoeffTerm p (0 - q) n i = 0 - Σ diagonalMulCoeffTerm p q n i`; the
coefficient-level negation law feeding `mul_sub_zero_comm`. -/
private theorem diagonalSum_neg_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p (0 - q) n i) 0 =
      0 -
        (List.range (n + 1)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  exact diagonalSum_neg_right_aux p q n (List.range (n + 1)) 0

/-- Pull a zero-based negation out of a product and commute the factors:
`p * (0 - q) = 0 - q * p`. A Mathlib-free `DensePoly` ring shim (the type
carries only `Lean.Grind.CommRing`, so `neg_mul`/`mul_comm` are unavailable). -/
theorem mul_sub_zero_comm {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p * (0 - q) = 0 - q * p := by
  apply ext_coeff
  intro n
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_mul, coeff_sub 0 (q * p) n hzero_sub, coeff_zero, coeff_mul,
    mulCoeffSum_eq_diagonal p (0 - q) n, mulCoeffSum_eq_diagonal q p n,
    diagonalSum_eq_degree_bound p (0 - q) n, diagonalSum_eq_degree_bound q p n,
    diagonalSum_neg_right p q n, fold_diagonal_comm p q n]

/-- Commutativity of `DensePoly` multiplication. Hand-proved because `DensePoly`
carries only `Lean.Grind.CommRing`, not Mathlib's `CommRing`, so `mul_comm`
is unavailable. -/
theorem mul_comm_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p * q = q * p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul, mulCoeffSum_eq_diagonal p q n, mulCoeffSum_eq_diagonal q p n,
    diagonalSum_eq_degree_bound p q n, diagonalSum_eq_degree_bound q p n, fold_diagonal_comm p q n]

/-- Cancellation rearrangement `(x + y) - (z + x) = y + (0 - z)`, used to
simplify mixed add/sub combinations arising in the Euclidean update steps. -/
theorem add_sub_add_swap {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (x y z : DensePoly S) :
    (x + y) - (z + x) = y + (0 - z) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_sub (x + y) (z + x) n hzero_sub, coeff_add x y n hzero_add, coeff_add z x n hzero_add,
    coeff_add y (0 - z) n hzero_add, coeff_sub 0 z n hzero_sub, coeff_zero]
  grind

/-- Cancellation rearrangement `(x + y) - (x + z) = y + (0 - z)`. -/
theorem add_sub_add_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (x y z : DensePoly S) :
    (x + y) - (x + z) = y + (0 - z) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_sub (x + y) (x + z) n hzero_sub, coeff_add x y n hzero_add, coeff_add x z n hzero_add,
    coeff_add y (0 - z) n hzero_add, coeff_sub 0 z n hzero_sub, coeff_zero]
  grind

/-- Commutativity of `DensePoly` addition (the Mathlib-free `add_comm`). -/
theorem add_comm_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p + q = q + p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p q n hzero_add, coeff_add q p n hzero_add]
  grind

/-- Associativity of `DensePoly` addition (the Mathlib-free `add_assoc`). -/
theorem add_assoc_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    p + q + r = p + (q + r) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add (p + q) r n hzero_add, coeff_add p q n hzero_add, coeff_add p (q + r) n hzero_add,
    coeff_add q r n hzero_add]
  grind

/-- Right identity for polynomial addition over a commutative ring: `p + 0 = p`.
A `grind` normalization lemma so downstream proofs cancel trailing zero summands. -/
@[grind =] theorem add_zero_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p 0 n hzero_add, coeff_zero]
  grind

/-- Rewrite a `DensePoly` subtraction as addition of the zero-based negation:
`p - q = p + (0 - q)`. -/
theorem sub_eq_add_neg_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p - q = p + (0 - q) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_sub p q n hzero_sub, coeff_add p (0 - q) n hzero_add,
    coeff_sub 0 q n hzero_sub, coeff_zero]
  grind

private theorem diagonalMulCoeffTerm_one_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) (n i : Nat) :
    diagonalMulCoeffTerm p 1 n i = if i = n then p.coeff n else 0 := by
  unfold diagonalMulCoeffTerm
  by_cases hlt : n < i
  · have hne : i ≠ n := by omega
    simp [hlt, hne]
  · by_cases hin : i = n
    · subst i
      have hone : (1 : DensePoly S).coeff 0 = (1 : S) := by
        change (C (1 : S)).coeff 0 = (1 : S)
        simp [coeff_C]
      simp [hone]
      exact Lean.Grind.Semiring.mul_one (p.coeff n)
    · have hsub_pos : n - i ≠ 0 := by omega
      have hone : (1 : DensePoly S).coeff (n - i) = (0 : S) := by
        change (C (1 : S)).coeff (n - i) = (0 : S)
        simp [coeff_C, hsub_pos]
        rfl
      simp [hlt, hin, hone]
      grind

private theorem fold_single_index {S : Type _}
    [Lean.Grind.CommRing S] (n m : Nat) (x : S) :
    (List.range m).foldl (fun acc i => acc + if i = n then x else 0) 0 =
      if n < m then x else 0 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      by_cases hn : n < m
      · have hne : m ≠ n := by omega
        simp [hn, hne]
        grind
      · by_cases hmn : m = n
        · subst n
          simp
          grind
        · have hn_succ : ¬ n < m + 1 := by omega
          simp [hn, hn_succ, hmn]
          grind

private theorem fold_diagonal_one_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p 1 n i) 0 =
      p.coeff n := by
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p 1 n i) acc =
        xs.foldl (fun acc i => acc + if i = n then p.coeff n else 0) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [diagonalMulCoeffTerm_one_right p n i]
        exact ih (acc + if i = n then p.coeff n else 0)
  rw [show
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p 1 n i) 0 =
        (List.range p.size).foldl (fun acc i => acc + if i = n then p.coeff n else 0) 0 by
    exact hfold (List.range p.size) 0]
  rw [fold_single_index]
  by_cases hn : n < p.size
  · simp [hn]
  · have hcoeff : p.coeff n = 0 := coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hn)
    simp [hn, hcoeff]

private theorem diagonalMulCoeffTerm_add_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n i : Nat) :
    diagonalMulCoeffTerm p (q + r) n i =
      diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i := by
  unfold diagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
    grind
  · have hzero_add : (0 : S) + (0 : S) = 0 := by grind
    rw [coeff_add q r (n - i) hzero_add]
    simp [hlt]
    grind

private theorem fold_add_pair_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f g : Nat → S) (a b : S) :
    xs.foldl (fun acc i => acc + (f i + g i)) (a + b) =
      xs.foldl (fun acc i => acc + f i) a +
        xs.foldl (fun acc i => acc + g i) b := by
  induction xs generalizing a b with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + (f i + g i) = (a + f i) + (b + g i) := by grind
      rw [hacc]
      exact ih (a + f i) (b + g i)

/-- Pull the initial accumulator out of an additive fold. -/
private theorem fold_add_acc_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f : Nat → S) (acc : S) :
    xs.foldl (fun acc i => acc + f i) acc =
      acc + xs.foldl (fun acc i => acc + f i) 0 := by
  have h :=
    fold_add_right_commring (S := S) (xs.map f) 0 acc
  simp [List.foldl_map] at h
  rw [← show (0 : S) + acc = acc by grind, h]
  grind

/-- Flatten a nested additive fold over a mapped list of rows. -/
private theorem fold_add_nested_map_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (row : Nat → List Nat) (F : Nat → Nat → S) (acc : S) :
    xs.foldl
        (fun acc i => acc + (row i).foldl (fun acc j => acc + F i j) 0)
        acc =
      xs.foldl
        (fun acc i => (row i).foldl (fun acc j => acc + F i j) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [← fold_add_acc_commring (row i) (F i) acc]
      exact ih ((row i).foldl (fun acc j => acc + F i j) acc)

/-- Extending a bounded row by one appends exactly the new boundary term. -/
private theorem triangular_row_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n j : Nat) (hj : j < n + 1) :
    (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0 =
      (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0 +
        F j (n + 1 - j) := by
  have hlen : n + 1 - j + 1 = (n - j + 1) + 1 := by omega
  rw [hlen, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hidx : n - j + 1 = n + 1 - j := by omega
  rw [hidx]

/-- The first `n + 1` rows of the larger triangle split into the old triangle
plus the new diagonal boundary. -/
private theorem triangular_prefix_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc j =>
          acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
        0 =
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0)
          0 +
        (List.range (n + 1)).foldl
          (fun acc j => acc + F j (n + 1 - j)) 0 := by
  let oldRow := fun j =>
    (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0
  let newTerm := fun j => F j (n + 1 - j)
  have hfold :
      ∀ (xs : List Nat),
        (∀ j, j ∈ xs → j < n + 1) →
        ∀ acc : S,
        xs.foldl
            (fun acc j =>
              acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
            acc =
          xs.foldl (fun acc j => acc + (oldRow j + newTerm j)) acc := by
    intro xs
    induction xs with
    | nil =>
        intro _hxs acc
        rfl
    | cons j xs ih =>
        intro hxs acc
        simp only [List.foldl_cons]
        rw [triangular_row_succ_commring F n j (hxs j (by simp))]
        exact ih (by
          intro k hk
          exact hxs k (by simp [hk])) (acc + (oldRow j + newTerm j))
  rw [hfold (List.range (n + 1)) (by
    intro j hj
    exact List.mem_range.mp hj) 0]
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  calc
    (List.range (n + 1)).foldl (fun acc j => acc + (oldRow j + newTerm j)) 0 =
        (List.range (n + 1)).foldl (fun acc j => acc + (oldRow j + newTerm j)) (0 + 0) := by
          rw [hzero_add]
    _ =
        (List.range (n + 1)).foldl (fun acc j => acc + oldRow j) 0 +
          (List.range (n + 1)).foldl (fun acc j => acc + newTerm j) 0 := by
        exact fold_add_pair_commring (S := S) (List.range (n + 1)) oldRow newTerm 0 0

/-- Advancing the total-degree triangular enumeration appends the new diagonal. -/
private theorem triangular_total_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1 + 1)).foldl
        (fun acc i =>
          acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
        0 =
      (List.range (n + 1)).foldl
          (fun acc i =>
            acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
          0 +
        (List.range (n + 1 + 1)).foldl
          (fun acc j => acc + F j (n + 1 - j)) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← List.range_succ]

/-- Advancing the first-coordinate triangular enumeration appends the last singleton row. -/
private theorem triangular_first_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1 + 1)).foldl
        (fun acc j =>
          acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
        0 =
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
          0 +
        F (n + 1) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hidx : n + 1 - (n + 1) = 0 := by omega
  simp [hidx]
  grind

/-- The new diagonal splits into the old rows' boundary plus the last corner. -/
private theorem triangular_boundary_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1 + 1)).foldl
        (fun acc j => acc + F j (n + 1 - j)) 0 =
      (List.range (n + 1)).foldl
          (fun acc j => acc + F j (n + 1 - j)) 0 +
        F (n + 1) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hidx : n + 1 - (n + 1) = 0 := by omega
  rw [hidx]

/-- The row-major triangular fold over total degree reindexed by first coordinate.

This is the generic finite reindexing behind convolution associativity:
`i` is the total degree, `j` the first coordinate, and `i - j` the second
coordinate.  The right-hand side enumerates the same finite triangle by
choosing the first coordinate first.
-/
private theorem triangular_fold_reindex_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
        0 =
      (List.range (n + 1)).foldl
        (fun acc j =>
          acc + (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0)
        0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [triangular_total_succ_commring F n, triangular_first_succ_commring F n, ih,
        triangular_prefix_succ_commring F n, triangular_boundary_succ_commring F n]
      grind

private theorem fold_diagonal_add_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p (q + r) n i) 0 =
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 +
        (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p r n i) 0 := by
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p (q + r) n i) acc =
        xs.foldl
          (fun acc i => acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i))
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [diagonalMulCoeffTerm_add_right p q r n i]
        exact ih (acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i))
  rw [hfold (List.range p.size) 0]
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  calc
    (List.range p.size).foldl
        (fun acc i => acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i)) 0 =
        (List.range p.size).foldl
          (fun acc i => acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i))
          (0 + 0) := by rw [hzero_add]
    _ =
        (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 +
          (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p r n i) 0 := by
        exact
          fold_add_pair_commring (S := S) (List.range p.size)
            (fun i => diagonalMulCoeffTerm p q n i)
            (fun i => diagonalMulCoeffTerm p r n i) 0 0

private theorem fold_add_congr {S : Type _} [Add S]
    (xs : List Nat) (f g : Nat → S)
    (hfg : ∀ i, i ∈ xs → f i = g i) (acc : S) :
    xs.foldl (fun acc i => acc + f i) acc =
      xs.foldl (fun acc i => acc + g i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hfg i (by simp)]
      exact ih
        (by
          intro j hj
          exact hfg j (by simp [hj]))
        (acc + g i)

/-- Distribute right multiplication by a constant through an additive fold. -/
private theorem fold_add_mul_right_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f : Nat → S) (c : S) :
    xs.foldl (fun acc i => acc + f i) 0 * c =
      xs.foldl (fun acc i => acc + f i * c) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hzero_f : (0 : S) + f i = f i := by grind
      have hzero_fc : (0 : S) + f i * c = f i * c := by grind
      rw [hzero_f, hzero_fc, fold_add_acc_commring xs f (f i),
        fold_add_acc_commring xs (fun i => f i * c) (f i * c), ← ih]
      grind

/-- Distribute left multiplication by a constant through an additive fold. -/
private theorem fold_add_mul_left_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f : Nat → S) (c : S) :
    c * xs.foldl (fun acc i => acc + f i) 0 =
      xs.foldl (fun acc i => acc + c * f i) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hzero_f : (0 : S) + f i = f i := by grind
      have hzero_cf : (0 : S) + c * f i = c * f i := by grind
      rw [hzero_f, hzero_cf, fold_add_acc_commring xs f (f i),
        fold_add_acc_commring xs (fun i => c * f i) (c * f i), ← ih]
      grind

private theorem rat_fold_add_range_succ (A : Nat → Rat) (m : Nat) :
    (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl (fun acc i => acc + A i) 0 + A m := by
  rw [List.range_succ, List.foldl_append]
  simp

private theorem rat_weighted_diagonal_fold_aux
    (A : Nat → Rat) (m : Nat) :
    ((m : Nat) : Rat) *
        (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl
          (fun acc i => acc + ((i + 1 : Nat) : Rat) * A (i + 1)) 0 +
        (List.range m).foldl
          (fun acc i => acc + ((m - i : Nat) : Rat) * A i) 0 := by
  induction m with
  | zero =>
      simp
      grind
  | succ m ih =>
      rw [rat_fold_add_range_succ A (m + 1)]
      have hsplit :
          (((m + 1 : Nat) : Rat) *
              ((List.range (m + 1)).foldl (fun acc i => acc + A i) 0 + A (m + 1))) =
            ((m : Nat) : Rat) *
                (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              ((m + 1 : Nat) : Rat) * A (m + 1) := by
        have hnat : ((m + 1 : Nat) : Rat) = ((m : Nat) : Rat) + 1 := by
          simp
        rw [hnat]
        grind
      rw [hsplit, ih]
      rw [rat_fold_add_range_succ
        (fun i => ((i + 1 : Nat) : Rat) * A (i + 1)) m]
      rw [rat_fold_add_range_succ
        (fun i => ((m + 1 - i : Nat) : Rat) * A i) m]
      rw [rat_fold_add_range_succ A m]
      have htail : ((m + 1 - m : Nat) : Rat) * A m = A m := by
        simp
      rw [htail]
      have hcoeff :
          (List.range m).foldl
              (fun acc i => acc + ((m - i : Nat) : Rat) * A i) 0 +
            (List.range m).foldl (fun acc i => acc + A i) 0 =
          (List.range m).foldl
              (fun acc i => acc + ((m + 1 - i : Nat) : Rat) * A i) 0 := by
        rw [← fold_add_pair_commring (S := Rat) (List.range m)
          (fun i => ((m - i : Nat) : Rat) * A i) (fun i => A i) 0 0]
        rw [show (0 : Rat) + 0 = 0 by grind]
        apply fold_add_congr
        intro i hi
        have hi' : i < m := List.mem_range.mp hi
        have hnat : ((m + 1 - i : Nat) : Rat) =
            ((m - i : Nat) : Rat) + 1 := by
          have h : m + 1 - i = m - i + 1 := by omega
          rw [h]
          simp
        rw [hnat]
        grind
      rw [← hcoeff]
      grind

private theorem rat_weighted_diagonal_fold
    (A : Nat → Rat) (n : Nat) :
    ((n + 1 : Nat) : Rat) *
        (List.range (n + 2)).foldl (fun acc i => acc + A i) 0 =
      (List.range (n + 1)).foldl
          (fun acc i => acc + ((i + 1 : Nat) : Rat) * A (i + 1)) 0 +
        (List.range (n + 1)).foldl
          (fun acc i => acc + ((n - i + 1 : Nat) : Rat) * A i) 0 := by
  have h := rat_weighted_diagonal_fold_aux A (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at h
  exact h.trans (by
    congr 1
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hidx : n + 1 - i = n - i + 1 := by omega
    rw [hidx])

private theorem rat_coeff_derivative_generic (p : DensePoly Rat) (n : Nat) :
    (derivative p).coeff n = ((n + 1 : Nat) : Rat) * p.coeff (n + 1) := by
  unfold derivative
  rw [coeff_ofCoeffs_list]
  change
    ((List.range (p.size - 1)).map
        (fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1))).getD n 0 =
      ((n + 1 : Nat) : Rat) * p.coeff (n + 1)
  by_cases hn : n < p.size - 1
  · simp [hn, List.getD]
  · have hp : p.size ≤ n + 1 := by omega
    have hcoeff : p.coeff (n + 1) = 0 :=
      coeff_eq_zero_of_size_le p hp
    simp [hn, List.getD, hcoeff]

/-- Rational-coefficient specialization of `mulCoeffSum_derivative_product_rule`:
the `(n+1)` scaling factor is cast into `Rat`. -/
theorem rat_mulCoeffSum_derivative_product_rule
    (p q : DensePoly Rat) (n : Nat) :
    ((n + 1 : Nat) : Rat) * mulCoeffSum p q (n + 1) =
      mulCoeffSum (derivative p) q n + mulCoeffSum p (derivative q) n := by
  rw [mulCoeffSum_eq_diagonal p q (n + 1), diagonalSum_eq_degree_bound p q (n + 1),
    mulCoeffSum_eq_diagonal (derivative p) q n, diagonalSum_eq_degree_bound (derivative p) q n,
    mulCoeffSum_eq_diagonal p (derivative q) n, diagonalSum_eq_degree_bound p (derivative q) n]
  have hleft :
      (List.range (n + 2)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm p q (n + 1) i) 0 =
        (List.range (n + 2)).foldl
          (fun acc i => acc + p.coeff i * q.coeff (n + 1 - i)) 0 := by
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 2 := List.mem_range.mp hi
    have hnot : ¬ n + 1 < i := by omega
    simp [diagonalMulCoeffTerm, hnot]
  rw [hleft, rat_weighted_diagonal_fold (fun i => p.coeff i * q.coeff (n + 1 - i)) n]
  congr 1
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, rat_coeff_derivative_generic p i]
    have hidx : n - i = n + 1 - (i + 1) := by omega
    rw [hidx]
    grind
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, rat_coeff_derivative_generic q (n - i)]
    have hidx : n - i + 1 = n + 1 - i := by omega
    rw [hidx]
    grind

section CommRingDerivative

variable {S : Type _} [Lean.Grind.CommRing S]

attribute [local instance 1100] Lean.Grind.Semiring.natCast

private theorem fold_add_range_succ_commring (A : Nat → S) (m : Nat) :
    (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl (fun acc i => acc + A i) 0 + A m := by
  rw [List.range_succ, List.foldl_append]
  simp

private theorem weighted_diagonal_fold_aux_commring
    (A : Nat → S) (m : Nat) :
    ((m : Nat) : S) *
        (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl
          (fun acc i => acc + ((i + 1 : Nat) : S) * A (i + 1)) 0 +
        (List.range m).foldl
          (fun acc i => acc + ((m - i : Nat) : S) * A i) 0 := by
  induction m with
  | zero =>
      simp
      have h0 : ((0 : Nat) : S) = 0 := Lean.Grind.Semiring.natCast_zero
      grind
  | succ m ih =>
      rw [fold_add_range_succ_commring A (m + 1)]
      have hsplit :
          (((m + 1 : Nat) : S) *
              ((List.range (m + 1)).foldl (fun acc i => acc + A i) 0 + A (m + 1))) =
            ((m : Nat) : S) *
                (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              ((m + 1 : Nat) : S) * A (m + 1) := by
        rw [Lean.Grind.Semiring.natCast_succ]
        grind
      rw [hsplit, ih]
      rw [fold_add_range_succ_commring
        (fun i => ((i + 1 : Nat) : S) * A (i + 1)) m]
      rw [fold_add_range_succ_commring
        (fun i => ((m + 1 - i : Nat) : S) * A i) m]
      rw [fold_add_range_succ_commring A m]
      have htail : ((m + 1 - m : Nat) : S) * A m = A m := by
        have hsub : m + 1 - m = 1 := by omega
        rw [hsub, Lean.Grind.Semiring.natCast_one]
        grind
      rw [htail]
      have hcoeff :
          (List.range m).foldl
              (fun acc i => acc + ((m - i : Nat) : S) * A i) 0 +
            (List.range m).foldl (fun acc i => acc + A i) 0 =
          (List.range m).foldl
              (fun acc i => acc + ((m + 1 - i : Nat) : S) * A i) 0 := by
        rw [← fold_add_pair_commring (S := S) (List.range m)
          (fun i => ((m - i : Nat) : S) * A i) (fun i => A i) 0 0]
        rw [show (0 : S) + 0 = 0 by grind]
        apply fold_add_congr
        intro i hi
        have hi' : i < m := List.mem_range.mp hi
        have hnat : ((m + 1 - i : Nat) : S) =
            ((m - i : Nat) : S) + 1 := by
          have h : m + 1 - i = m - i + 1 := by omega
          rw [h, Lean.Grind.Semiring.natCast_succ]
        rw [hnat]
        grind
      rw [← hcoeff]
      grind

private theorem weighted_diagonal_fold_commring
    (A : Nat → S) (n : Nat) :
    ((n + 1 : Nat) : S) *
        (List.range (n + 2)).foldl (fun acc i => acc + A i) 0 =
      (List.range (n + 1)).foldl
          (fun acc i => acc + ((i + 1 : Nat) : S) * A (i + 1)) 0 +
        (List.range (n + 1)).foldl
          (fun acc i => acc + ((n - i + 1 : Nat) : S) * A i) 0 := by
  have h := weighted_diagonal_fold_aux_commring A (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at h
  exact h.trans (by
    congr 1
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hidx : n + 1 - i = n - i + 1 := by omega
    rw [hidx])

/-- Coefficient-level product rule: `(n+1)` times the order-`(n+1)` product
coefficient sum equals the sum of the two derivative product coefficient sums.
This is the per-coefficient identity underlying `derivative_mul`. -/
theorem mulCoeffSum_derivative_product_rule [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    ((n + 1 : Nat) : S) * mulCoeffSum p q (n + 1) =
      mulCoeffSum (derivative p) q n + mulCoeffSum p (derivative q) n := by
  rw [mulCoeffSum_eq_diagonal p q (n + 1), diagonalSum_eq_degree_bound p q (n + 1),
    mulCoeffSum_eq_diagonal (derivative p) q n, diagonalSum_eq_degree_bound (derivative p) q n,
    mulCoeffSum_eq_diagonal p (derivative q) n, diagonalSum_eq_degree_bound p (derivative q) n]
  have hleft :
      (List.range (n + 2)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm p q (n + 1) i) 0 =
        (List.range (n + 2)).foldl
          (fun acc i => acc + p.coeff i * q.coeff (n + 1 - i)) 0 := by
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 2 := List.mem_range.mp hi
    have hnot : ¬ n + 1 < i := by omega
    simp [diagonalMulCoeffTerm, hnot]
  rw [hleft, weighted_diagonal_fold_commring (fun i => p.coeff i * q.coeff (n + 1 - i)) n]
  congr 1
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, coeff_derivative_semiring p i]
    have hidx : n - i = n + 1 - (i + 1) := by omega
    rw [hidx]
    grind
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, coeff_derivative_semiring q (n - i)]
    have hidx : n - i + 1 = n + 1 - i := by omega
    rw [hidx]
    grind

/-- Leibniz product rule for the formal `DensePoly` derivative:
`derivative (p * q) = derivative p * q + p * derivative q`. -/
theorem derivative_mul [DecidableEq S]
    (p q : DensePoly S) :
    derivative (p * q) =
      derivative p * q + p * derivative q := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_derivative_semiring, coeff_mul p q (n + 1)]
  rw [coeff_add (derivative p * q) (p * derivative q) n
    (Lean.Grind.Semiring.add_zero (0 : S))]
  rw [coeff_mul (derivative p) q n, coeff_mul p (derivative q) n]
  exact mulCoeffSum_derivative_product_rule p q n

end CommRingDerivative

private theorem diagonal_mul_left_expand {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n i : Nat) (hi : i < n + 1) :
    diagonalMulCoeffTerm (p * q) r n i =
      (List.range (i + 1)).foldl
        (fun acc j => acc + (p.coeff j * q.coeff (i - j)) * r.coeff (n - i)) 0 := by
  have hnot : ¬ n < i := by omega
  simp [diagonalMulCoeffTerm, hnot]
  rw [coeff_mul, mulCoeffSum_eq_diagonal p q i, diagonalSum_eq_degree_bound p q i]
  calc
    (List.range (i + 1)).foldl (fun acc j => acc + diagonalMulCoeffTerm p q i j) 0 *
        r.coeff (n - i) =
        (List.range (i + 1)).foldl
          (fun acc j => acc + diagonalMulCoeffTerm p q i j * r.coeff (n - i)) 0 := by
      exact fold_add_mul_right_commring
        (S := S) (List.range (i + 1))
        (fun j => diagonalMulCoeffTerm p q i j) (r.coeff (n - i))
    _ =
        (List.range (i + 1)).foldl
          (fun acc j => acc + (p.coeff j * q.coeff (i - j)) * r.coeff (n - i)) 0 := by
      apply fold_add_congr
      intro j hj
      have hjlt : j < i + 1 := List.mem_range.mp hj
      have hnotji : ¬ i < j := by omega
      simp [diagonalMulCoeffTerm, hnotji]

private theorem diagonal_mul_right_expand {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n j : Nat) (hj : j < n + 1) :
    diagonalMulCoeffTerm p (q * r) n j =
      (List.range (n - j + 1)).foldl
        (fun acc k => acc + p.coeff j * (q.coeff k * r.coeff (n - j - k))) 0 := by
  have hnot : ¬ n < j := by omega
  simp [diagonalMulCoeffTerm, hnot]
  rw [coeff_mul, mulCoeffSum_eq_diagonal q r (n - j), diagonalSum_eq_degree_bound q r (n - j)]
  calc
    p.coeff j *
        (List.range (n - j + 1)).foldl
          (fun acc k => acc + diagonalMulCoeffTerm q r (n - j) k) 0 =
        (List.range (n - j + 1)).foldl
          (fun acc k => acc + p.coeff j * diagonalMulCoeffTerm q r (n - j) k) 0 := by
      exact fold_add_mul_left_commring
        (S := S) (List.range (n - j + 1))
        (fun k => diagonalMulCoeffTerm q r (n - j) k) (p.coeff j)
    _ =
        (List.range (n - j + 1)).foldl
          (fun acc k => acc + p.coeff j * (q.coeff k * r.coeff (n - j - k))) 0 := by
      apply fold_add_congr
      intro k hk
      have hklt : k < n - j + 1 := List.mem_range.mp hk
      have hnotkn : ¬ n - j < k := by omega
      simp [diagonalMulCoeffTerm, hnotkn]

private theorem fold_diagonal_mul_assoc {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n : Nat) :
    (List.range (p * q).size).foldl
        (fun acc i => acc + diagonalMulCoeffTerm (p * q) r n i) 0 =
      (List.range p.size).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p (q * r) n i) 0 := by
  rw [diagonalSum_eq_degree_bound (p * q) r n, diagonalSum_eq_degree_bound p (q * r) n]
  let F : Nat → Nat → S := fun j k => p.coeff j * q.coeff k * r.coeff (n - (j + k))
  have hleft :
      (List.range (n + 1)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm (p * q) r n i) 0 =
        (List.range (n + 1)).foldl
          (fun acc i =>
            acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
          0 := by
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    rw [diagonal_mul_left_expand p q r n i hi']
    apply fold_add_congr
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp hj
    simp [F]
    have hidx : n - i = n - (j + (i - j)) := by omega
    rw [hidx]
  have hright :
      (List.range (n + 1)).foldl
          (fun acc j => acc + diagonalMulCoeffTerm p (q * r) n j) 0 =
        (List.range (n + 1)).foldl
          (fun acc j =>
            acc + (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0)
          0 := by
    apply fold_add_congr
    intro j hj
    have hj' : j < n + 1 := List.mem_range.mp hj
    rw [diagonal_mul_right_expand p q r n j hj']
    apply fold_add_congr
    intro k hk
    have hk' : k < n - j + 1 := List.mem_range.mp hk
    simp [F]
    have hidx : n - (j + k) = n - j - k := by omega
    rw [hidx]
    grind
  rw [hleft, hright]
  exact triangular_fold_reindex_commring F n

/-- Associativity of `DensePoly` multiplication (the Mathlib-free `mul_assoc`). -/
theorem mul_assoc_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    (p * q) * r = p * (q * r) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul, mulCoeffSum_eq_diagonal (p * q) r n,
    mulCoeffSum_eq_diagonal p (q * r) n]
  exact fold_diagonal_mul_assoc p q r n

/-- Left distributivity for `DensePoly`: `p * (q + r) = p * q + p * r`. -/
theorem mul_add_right_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    p * (q + r) = p * q + p * r := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_mul, coeff_add (p * q) (p * r) n hzero_add, coeff_mul, coeff_mul,
    mulCoeffSum_eq_diagonal p (q + r) n,
    mulCoeffSum_eq_diagonal p q n, mulCoeffSum_eq_diagonal p r n]
  exact fold_diagonal_add_right p q r n

/-- Right distributivity for `DensePoly`: `(p + q) * r = p * r + q * r`. -/
theorem mul_add_left_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    (p + q) * r = p * r + q * r := by
  rw [mul_comm_poly (p + q) r, mul_add_right_poly r p q,
    mul_comm_poly r p, mul_comm_poly r q]

/-- Right identity for polynomial multiplication over a commutative ring:
`p * 1 = p`. A `grind` normalization lemma; the Bézout and division routines
cancel multiplications by the unit polynomial through it. -/
@[grind =] theorem mul_one_right_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p * 1 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal]
  exact fold_diagonal_one_right p n

/-- `DensePoly S` is a multiplicative monoid: these `Std` instances let the
shared `List.foldl_mul_*` algebra (and core's `List.foldl_assoc`) apply to
fold-products of polynomials such as `FpPoly`/`ZPoly`. -/
instance instAssociativeMulDensePoly {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] :
    Std.Associative (· * · : DensePoly S → DensePoly S → DensePoly S) :=
  ⟨mul_assoc_poly⟩

instance instLawfulIdentityMulDensePoly {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] :
    Std.LawfulIdentity (· * · : DensePoly S → DensePoly S → DensePoly S) 1 where
  left_id p := (mul_comm_poly 1 p).trans (mul_one_right_poly p)
  right_id := mul_one_right_poly

/-- Product of two monomials: `xⁱ * cⱼ * xʲ = cᵢcⱼ * xⁱ⁺ʲ`. -/
theorem monomial_mul_monomial {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (m k : Nat) (c d : S) :
    (monomial m c) * (monomial k d) = monomial (m + k) (c * d) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound, coeff_monomial]
  have hterm : ∀ i,
      diagonalMulCoeffTerm (monomial m c) (monomial k d) n i =
        if i = m ∧ n = m + k then c * d else 0 := by
    intro i
    unfold diagonalMulCoeffTerm
    rw [coeff_monomial, coeff_monomial]
    by_cases hni : n < i
    · have hcond : ¬ (i = m ∧ n = m + k) := by
        intro ⟨h1, h2⟩; omega
      rw [if_pos hni, if_neg hcond]
    · have hile : i ≤ n := Nat.le_of_not_gt hni
      rw [if_neg hni]
      by_cases him : i = m
      · subst i
        rw [if_pos rfl]
        by_cases hnmk : n - m = k
        · have hn : n = m + k := by omega
          rw [if_pos hnmk]
          simp [hn]
        · have hn : n ≠ m + k := by omega
          rw [if_neg hnmk]
          have hcond : ¬ (m = m ∧ n = m + k) := fun ⟨_, h⟩ => hn h
          rw [if_neg hcond]
          -- c * Zero.zero = 0.
          show c * (Zero.zero : S) = 0
          have : (Zero.zero : S) = 0 := rfl
          rw [this]
          grind
      · rw [if_neg him]
        have hcond : ¬ (i = m ∧ n = m + k) := fun ⟨h, _⟩ => him h
        rw [if_neg hcond]
        -- Zero.zero * anything = 0.
        exact Lean.Grind.Semiring.zero_mul _
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i =>
          acc + diagonalMulCoeffTerm (monomial m c) (monomial k d) n i) acc =
        xs.foldl (fun acc i =>
          acc + if i = m ∧ n = m + k then c * d else 0) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [hterm i]
        exact ih _
  rw [hfold (List.range (n + 1)) 0]
  by_cases hnmk : n = m + k
  · have hsimp : ∀ i,
        (if i = m ∧ n = m + k then c * d else 0) =
          (if i = m then c * d else 0) := fun i => by simp [hnmk]
    have hfold2 : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i => acc + if i = m ∧ n = m + k then c * d else 0) acc =
          xs.foldl (fun acc i => acc + if i = m then c * d else 0) acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          rw [hsimp i]
          exact ih _
    rw [hfold2 (List.range (n + 1)) 0, fold_single_index]
    have hm_lt : m < n + 1 := by omega
    rw [if_pos hm_lt, if_pos hnmk]
  · have hzero_fold : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i => acc + if i = m ∧ n = m + k then c * d else 0) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hcond : ¬ (i = m ∧ n = m + k) := fun ⟨_, h⟩ => hnmk h
          rw [if_neg hcond, show acc + (0 : S) = acc by grind]
          exact ih _
    rw [hzero_fold, if_neg hnmk]
    rfl

end DensePoly
end Hex
