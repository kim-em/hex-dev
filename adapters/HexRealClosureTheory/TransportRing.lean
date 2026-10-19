/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportProduct

public section

namespace Hex.RealClosure.Transport.Ring

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [Add E] [Mul E]
variable [CommRing K] [DecidableEq K]

omit [CommRing K] [DecidableEq K] in
/-- Extending a range fold by steps that leave its accumulator unchanged
preserves its value. This applies to target coefficients trimmed by normalization. -/
private theorem range_fold (step : K → Nat → K) (bound m : Nat) (le : bound ≤ m)
    (fixed : ∀ acc i, bound ≤ i → step acc i = acc) (initial : K) :
    (List.range m).foldl step initial = (List.range bound).foldl step initial := by
  induction m with
  | zero =>
    have empty : bound = 0 := by omega
    subst bound
    rfl
  | succ m ih =>
    by_cases last : bound = m + 1
    · rw [last]
    · have earlier : bound ≤ m := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        fixed _ m earlier]
      exact ih earlier

/-- Interpret the actual schoolbook fold, keeping its source loop bounds.
Only the finite products and sums at reached source accumulators are needed. -/
theorem product_coeff (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (products : ∀ i < p.size, ∀ j < q.size,
      read (p.coeff i * q.coeff j) = read (p.coeff i) * read (q.coeff j))
    (sums : ∀ i < p.size, ∀ j < q.size,
      read (productPrefix p q (i + j) i j + p.coeff i * q.coeff j) =
        read (productPrefix p q (i + j) i j) + read (p.coeff i * q.coeff j)) (n : Nat) :
    read (Hex.DensePoly.mulCoeffSum p q n) =
      Hex.DensePoly.mulCoeffSum (polynomial read p) (polynomial read q) n := by
  have initial : read (Zero.zero : E) = (0 : K) := zero
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
  have psize : (polynomial read p).size ≤ p.size := by
    simpa only [polynomial, Array.size_map, Hex.DensePoly.toArray_size] using
      Hex.DensePoly.size_ofCoeffs_le (p.toArray.map read)
  have qsize : (polynomial read q).size ≤ q.size := by
    simpa only [polynomial, Array.size_map, Hex.DensePoly.toArray_size] using
      Hex.DensePoly.size_ofCoeffs_le (q.toArray.map read)
  have inner i acc :
      (List.range q.size).foldl
        (Hex.DensePoly.mulCoeffStep (polynomial read p) (polynomial read q) n i) acc =
      (List.range (polynomial read q).size).foldl
        (Hex.DensePoly.mulCoeffStep (polynomial read p) (polynomial read q) n i) acc := by
    apply range_fold _ _ _ qsize
    intro acc j hj
    simp only [Hex.DensePoly.mulCoeffStep,
      Hex.DensePoly.coeff_eq_zero_of_size_le (polynomial read q) hj]
    change (if i + j = n then acc + (polynomial read p).coeff i * (0 : K) else acc) = acc
    simp only [mul_zero, add_zero, ite_self]
  have outer : (List.range p.size).foldl
      (fun acc i => (List.range (polynomial read q).size).foldl
        (Hex.DensePoly.mulCoeffStep (polynomial read p) (polynomial read q) n i) acc) 0 =
      Hex.DensePoly.mulCoeffSum (polynomial read p) (polynomial read q) n := by
    rw [Hex.DensePoly.mulCoeffSum]
    apply range_fold _ _ _ psize
    intro acc i hi
    have fixed : ∀ acc j,
        Hex.DensePoly.mulCoeffStep (polynomial read p) (polynomial read q) n i acc j = acc := by
      intro acc j
      simp only [Hex.DensePoly.mulCoeffStep,
        Hex.DensePoly.coeff_eq_zero_of_size_le (polynomial read p) hi]
      change (if i + j = n then acc + (0 : K) * (polynomial read q).coeff j else acc) = acc
      simp only [zero_mul, add_zero, ite_self]
    exact range_fold _ 0 _ (Nat.zero_le _) (fun acc j _ => fixed acc j) acc
  change read (Hex.DensePoly.mulCoeffSum p q n) = _ at mapped
  simp_rw [inner] at mapped
  exact mapped.trans outer

/-- Target ring laws absorb coefficients trimmed by interpretation. Products
may lose degree or become zero; no source or intermediate leading guards are needed. -/
theorem polynomial_mul (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (products : ∀ i < p.size, ∀ j < q.size,
      read (p.coeff i * q.coeff j) = read (p.coeff i) * read (q.coeff j))
    (sums : ∀ i < p.size, ∀ j < q.size,
      read (productPrefix p q (i + j) i j + p.coeff i * q.coeff j) =
        read (productPrefix p q (i + j) i j) + read (p.coeff i * q.coeff j)) :
    polynomial read (p * q) = polynomial read p * polynomial read q := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [polynomial_coeff read zero, Hex.DensePoly.coeff_mul, Hex.DensePoly.coeff_mul]
  exact product_coeff read zero p q products sums n

omit [DecidableEq E] [Add E] [Mul E] [CommRing K] [DecidableEq K] in
private theorem array_getD {n : Nat} (f : Fin n → E) (i : Nat) :
    (Array.ofFn f).getD i (Zero.zero : E) =
      if h : i < n then f ⟨i, h⟩ else (Zero.zero : E) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : i < n
  · rw [dite_eq_left h, dite_eq_left h]; rfl
  · rw [dite_eq_right h, dite_eq_right h]; rfl

omit [Mul E] in
/-- Target zero laws retain addition even when input or result arrays shrink. -/
theorem polynomial_add (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (sums : ∀ i < max p.size q.size,
      read (p.coeff i + q.coeff i) = read (p.coeff i) + read (q.coeff i)) :
    polynomial read (p + q) = polynomial read p + polynomial read q := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff read zero]
  change read ((Hex.DensePoly.add p q).coeff i) = _
  rw [Hex.DensePoly.add_eq_addImpl, Hex.DensePoly.addImpl, Hex.DensePoly.coeff_ofCoeffs,
    array_getD, Hex.DensePoly.coeff_add _ _ i (by exact add_zero (0 : K)),
    polynomial_coeff read zero, polynomial_coeff read zero]
  by_cases bound : i < max p.size q.size
  · rw [dite_eq_left bound]
    exact sums i bound
  · rw [dite_eq_right bound,
      Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega),
      Hex.DensePoly.coeff_eq_zero_of_size_le q (by omega)]
    change read (0 : E) = read (0 : E) + read (0 : E)
    rw [zero, add_zero]

omit [Add E] [Mul E] in
/-- Target zero laws retain subtraction without guards on operand degrees. -/
theorem polynomial_sub [Sub E] (read : E → K) (zero : read 0 = 0) (p q : Hex.DensePoly E)
    (differences : ∀ i < max p.size q.size,
      read (p.coeff i - q.coeff i) = read (p.coeff i) - read (q.coeff i)) :
    polynomial read (p - q) = polynomial read p - polynomial read q := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff read zero]
  change read ((Hex.DensePoly.sub p q).coeff i) = _
  rw [Hex.DensePoly.sub_eq_subImpl, Hex.DensePoly.subImpl, Hex.DensePoly.coeff_ofCoeffs,
    array_getD, Hex.DensePoly.coeff_sub _ _ i (by exact sub_self (0 : K)),
    polynomial_coeff read zero, polynomial_coeff read zero]
  by_cases bound : i < max p.size q.size
  · rw [dite_eq_left bound]
    exact differences i bound
  · rw [dite_eq_right bound,
      Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega),
      Hex.DensePoly.coeff_eq_zero_of_size_le q (by omega)]
    change read (0 : E) = read (0 : E) - read (0 : E)
    rw [zero, sub_self]

omit [Add E] in
/-- Target zero multiplication permits any input leading coefficient to vanish. -/
theorem polynomial_scale (read : E → K) (zero : read 0 = 0) (scalar : E) (p : Hex.DensePoly E)
    (products : ∀ i < p.size,
      read (scalar * p.coeff i) = read scalar * read (p.coeff i)) :
    polynomial read (Hex.DensePoly.scale scalar p) =
      Hex.DensePoly.scale (read scalar) (polynomial read p) := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff read zero, Hex.DensePoly.scale_eq_scaleImpl, Hex.DensePoly.scaleImpl,
    Hex.DensePoly.coeff_ofCoeffs, Hex.DensePoly.coeff_scale _ _ i (by exact mul_zero _),
    polynomial_coeff read zero, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases bound : i < p.toArray.size
  · rw [Array.getElem?_eq_getElem bound]
    simp only [Option.map_some, Option.getD_some]
    rw [Array.getElem_eq_getD (h := bound) (Zero.zero : E)]
    change read (scalar * p.coeff i) = read scalar * read (p.coeff i)
    exact products i (by simpa using bound)
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt bound)]
    simp only [Option.map_none, Option.getD_none]
    rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (by simpa using Nat.le_of_not_gt bound)]
    change read (0 : E) = read scalar * read (0 : E)
    rw [zero, mul_zero]

omit [Add E] in
/-- Differentiation commutes without retaining the source coefficient length. -/
theorem polynomial_derivative [NatCast E] (read : E → K) (zero : read 0 = 0)
    (p : Hex.DensePoly E) (products : ∀ i < p.size - 1,
      read (((i + 1 : Nat) : E) * p.coeff (i + 1)) =
        ((i + 1 : Nat) : K) * read (p.coeff (i + 1))) :
    polynomial read p.derivative = (polynomial read p).derivative := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff read zero, Hex.DensePoly.derivative_eq_derivativeImpl,
    Hex.DensePoly.derivativeImpl, Hex.DensePoly.coeff_ofCoeffs, array_getD,
    Hex.DensePoly.coeff_derivative _ i (by exact mul_zero _), polynomial_coeff read zero]
  by_cases bound : i < p.size - 1
  · rw [dite_eq_left bound]
    exact products i bound
  · rw [dite_eq_right bound, Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)]
    change read (0 : E) = ((i + 1 : Nat) : K) * read (0 : E)
    rw [zero, mul_zero]

/-- Removing trailing zero coefficients leaves target Horner evaluation unchanged. -/
private theorem foldr_trim (cs : List K) (x : K) :
    (Hex.DensePoly.trimTrailingZerosList cs).foldr (fun c acc => acc * x + c) (Zero.zero : K) =
      cs.foldr (fun c acc => acc * x + c) (Zero.zero : K) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases empty : Hex.DensePoly.trimTrailingZerosList cs = [] ∧ c = (Zero.zero : K)
    · have tail : cs.foldr (fun c acc => acc * x + c) (Zero.zero : K) = (Zero.zero : K) := by
        rw [← ih, empty.1]; rfl
      rw [show Hex.DensePoly.trimTrailingZerosList (c :: cs) = [] by
        simp [Hex.DensePoly.trimTrailingZerosList, empty.1, empty.2]]
      simp only [List.foldr_nil, List.foldr_cons, tail, empty.2]
      change (0 : K) = 0 * x + 0
      simp only [zero_mul, add_zero]
    · rw [show Hex.DensePoly.trimTrailingZerosList (c :: cs) =
          c :: Hex.DensePoly.trimTrailingZerosList cs by
        simp [Hex.DensePoly.trimTrailingZerosList, empty]]
      simp only [List.foldr_cons, ih]

/-- Evaluation uses the original finite Horner loop even when interpretation
removes its top coefficients. Only target ring laws absorb those zero steps. -/
theorem polynomial_eval (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E) (x : E)
    (products : ∀ i < p.size,
      read (hornerPrefix p x i * x) = read (hornerPrefix p x i) * read x)
    (sums : ∀ i < p.size,
      read (hornerPrefix p x i * x + p.coeff (p.size - 1 - i)) =
        read (hornerPrefix p x i * x) + read (p.coeff (p.size - 1 - i))) :
    read (p.eval x) = (polynomial read p).eval (read x) := by
  have target : (polynomial read p).eval (read x) =
      (p.toArray.toList.map read).foldr (fun c acc => acc * read x + c) (Zero.zero : K) := by
    rw [Hex.DensePoly.eval_eq_evalImpl, Hex.DensePoly.evalImpl, ← Array.foldr_toList]
    unfold polynomial Hex.DensePoly.toArray Hex.DensePoly.ofCoeffs Hex.DensePoly.trimTrailingZeros
    simpa only [Array.toList_map, Hex.DensePoly.toArray] using
      foldr_trim (p.toArray.toList.map read) (read x)
  rw [target, Hex.DensePoly.eval_eq_evalImpl, Hex.DensePoly.evalImpl,
    ← Array.foldr_toList, List.foldr_eq_foldl_reverse, List.foldr_eq_foldl_reverse,
    ← List.map_reverse, List.foldl_map]
  have initial : read (Zero.zero : E) = (0 : K) := zero
  have mapped := foldl_read read (fun acc c => acc * x + c)
    (fun acc c => acc * read x + read c) p.toArray.toList.reverse (Zero.zero : E) (by
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

end Hex.RealClosure.Transport.Ring

/-- info: 'Hex.RealClosure.Transport.Ring.polynomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Ring.polynomial_mul

/-- info: 'Hex.RealClosure.Transport.Ring.polynomial_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Ring.polynomial_add
/-- info: 'Hex.RealClosure.Transport.Ring.polynomial_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Ring.polynomial_sub
/-- info: 'Hex.RealClosure.Transport.Ring.polynomial_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Ring.polynomial_scale
/-- info: 'Hex.RealClosure.Transport.Ring.polynomial_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Ring.polynomial_derivative

/-- info: 'Hex.RealClosure.Transport.Ring.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Ring.polynomial_eval
