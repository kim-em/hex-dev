/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportPolynomial

public section

namespace Hex.RealClosure.Transport

/-- A fold transports from identities at its actual finite sequence of
accumulators; no law at unrelated source states is assumed. -/
theorem foldl_read {A : Type u} {E : Type v} {K : Type w}
    (read : E → K) (step : E → A → E) (target : K → A → K)
    (xs : List A) (initial : E)
    (steps : ∀ (i : Nat) (hi : i < xs.length),
      read (step ((xs.take i).foldl step initial) xs[i]) =
        target (read ((xs.take i).foldl step initial)) xs[i]) :
    read (xs.foldl step initial) = xs.foldl target (read initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    have first := steps 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at first
    have tail : ∀ (i : Nat) (hi : i < xs.length),
        read (step ((xs.take i).foldl step (step initial x)) xs[i]) =
          target (read ((xs.take i).foldl step (step initial x))) xs[i] := by
      intro i hi
      have next := steps (i + 1) (by simp; omega)
      simpa only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] using next
    rw [List.foldl_cons, List.foldl_cons, ih (step initial x) tail, first]

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [Add E] [Mul E]
variable [Zero K] [DecidableEq K] [Add K] [Mul K]

/-- The accumulator for coefficient `n` immediately before schoolbook
multiplication processes the pair `(i,j)`. It uses the native coefficient step. -/
@[expose] def productPrefix (p q : Hex.DensePoly E) (n i j : Nat) : E :=
  ((List.range q.size).take j).foldl (Hex.DensePoly.mulCoeffStep p q n i)
    (((List.range p.size).take i).foldl
      (fun acc row => (List.range q.size).foldl (Hex.DensePoly.mulCoeffStep p q n row) acc) 0)

/-- The actual schoolbook coefficient fold transports from finitely many
products and additions at the accumulators reached by the native loop. -/
theorem product_coeff (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (first : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (second : 0 < q.size → read (q.coeff (q.size - 1)) ≠ 0)
    (products : ∀ i < p.size, ∀ j < q.size,
      read (p.coeff i * q.coeff j) = read (p.coeff i) * read (q.coeff j))
    (sums : ∀ i < p.size, ∀ j < q.size,
      read (productPrefix p q (i + j) i j + p.coeff i * q.coeff j) =
        read (productPrefix p q (i + j) i j) + read (p.coeff i * q.coeff j)) (n : Nat) :
    read (Hex.DensePoly.mulCoeffSum p q n) =
      Hex.DensePoly.mulCoeffSum (polynomial read p) (polynomial read q) n := by
  have initial : read (Zero.zero : E) = (Zero.zero : K) := zero
  rw [Hex.DensePoly.mulCoeffSum, Hex.DensePoly.mulCoeffSum,
    polynomial_size read zero p first, polynomial_size read zero q second]
  have mapped := foldl_read read
    (fun acc row => (List.range q.size).foldl (Hex.DensePoly.mulCoeffStep p q n row) acc)
    (fun acc row => (List.range q.size).foldl
      (Hex.DensePoly.mulCoeffStep (polynomial read p) (polynomial read q) n row) acc)
    (List.range p.size) (Zero.zero : E) (by
      intro i hi
      have bound : i < p.size := by simpa only [List.length_range] using hi
      simp only [List.getElem_range]
      apply foldl_read
      intro j hj
      have bound' : j < q.size := by simpa only [List.length_range] using hj
      simp only [List.getElem_range]
      change read (Hex.DensePoly.mulCoeffStep p q n i (productPrefix p q n i j) j) =
        Hex.DensePoly.mulCoeffStep (polynomial read p) (polynomial read q) n i
          (read (productPrefix p q n i j)) j
      by_cases equal : i + j = n
      · simp only [Hex.DensePoly.mulCoeffStep, ite_eq_left equal, polynomial_coeff read zero]
        subst n
        rw [sums i bound j bound', products i bound j bound']
      · simp only [Hex.DensePoly.mulCoeffStep, ite_eq_right equal])
  rw [initial] at mapped
  exact mapped

/-- Polynomial multiplication transports the finite scalar work of the
executable schoolbook loop, including each actual accumulation. -/
theorem polynomial_mul (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (first : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (second : 0 < q.size → read (q.coeff (q.size - 1)) ≠ 0)
    (products : ∀ i < p.size, ∀ j < q.size,
      read (p.coeff i * q.coeff j) = read (p.coeff i) * read (q.coeff j))
    (sums : ∀ i < p.size, ∀ j < q.size,
      read (productPrefix p q (i + j) i j + p.coeff i * q.coeff j) =
        read (productPrefix p q (i + j) i j) + read (p.coeff i * q.coeff j)) :
    polynomial read (p * q) = polynomial read p * polynomial read q := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [polynomial_coeff read zero, Hex.DensePoly.coeff_mul, Hex.DensePoly.coeff_mul]
  exact product_coeff read zero p q first second products sums n

/-- The accumulator reached after the first `i` steps of native Horner
evaluation, in the executable's descending coefficient order. -/
@[expose] def hornerPrefix (p : Hex.DensePoly E) (x : E) (i : Nat) : E :=
  (p.toArray.toList.reverse.take i).foldl (fun acc coeff => acc * x + coeff) 0

/-- Horner evaluation transports from scalar identities at the finite sequence
of accumulators actually reached by the executable. -/
theorem polynomial_eval (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E) (x : E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (products : ∀ i < p.size,
      read (hornerPrefix p x i * x) = read (hornerPrefix p x i) * read x)
    (sums : ∀ i < p.size,
      read (hornerPrefix p x i * x + p.coeff (p.size - 1 - i)) =
        read (hornerPrefix p x i * x) + read (p.coeff (p.size - 1 - i))) :
    read (p.eval x) = (polynomial read p).eval (read x) := by
  have initial : read (Zero.zero : E) = (Zero.zero : K) := zero
  rw [Hex.DensePoly.eval_eq_evalImpl, Hex.DensePoly.eval_eq_evalImpl,
    Hex.DensePoly.evalImpl, Hex.DensePoly.evalImpl,
    polynomial_array read zero p leading, ← Array.foldr_toList, ← Array.foldr_toList,
    Array.toList_map, List.foldr_eq_foldl_reverse, List.foldr_eq_foldl_reverse,
    ← List.map_reverse, List.foldl_map]
  have mapped := foldl_read read (fun acc coeff => acc * x + coeff)
    (fun acc coeff => acc * read x + read coeff) p.toArray.toList.reverse
    (Zero.zero : E) (by
      intro i hi
      have bound : i < p.size := by simpa only [List.length_reverse,
        Array.length_toList, Hex.DensePoly.toArray_size] using hi
      rw [List.getElem_reverse]
      simp only [Array.length_toList, Hex.DensePoly.toArray_size, Array.getElem_toList]
      rw [Array.getElem_eq_getD (h := by simp only [Hex.DensePoly.toArray_size]; omega)
        (Zero.zero : E)]
      change read (hornerPrefix p x i * x + p.coeff (p.size - 1 - i)) =
        read (hornerPrefix p x i) * read x + read (p.coeff (p.size - 1 - i))
      rw [sums i bound, products i bound])
  rw [initial] at mapped
  exact mapped

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.product_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.product_coeff

/-- info: 'Hex.RealClosure.Transport.polynomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_mul

/-- info: 'Hex.RealClosure.Transport.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_eval

/-- info: 'Hex.RealClosure.Transport.foldl_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.foldl_read
