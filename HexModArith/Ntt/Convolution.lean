/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.Transform

public section

/-!
# Convolution through the number-theoretic transform

This file connects the executable transform to independent coefficient-level
convolution references. Linear convolution is the ordinary schoolbook
product. Cyclic and negacyclic folding then reduce that product by `x^n - 1`
and `x^n + 1`, respectively.
-/

namespace Hex

namespace ZMod64

namespace Ntt

/-- Add coefficient lists, treating a missing tail as zero. -/
@[expose] def addCoeffs {p : Nat} [Bounds p] :
    List (ZMod64 p) → List (ZMod64 p) → List (ZMod64 p)
  | [], right => right
  | left, [] => left
  | x :: xs, y :: ys => (x + y) :: addCoeffs xs ys

/-- Coefficientwise addition commutes with polynomial evaluation. -/
theorem evalCoeffs_add {p : Nat} [Bounds p] (point : ZMod64 p)
    (left right : List (ZMod64 p)) :
    evalCoeffs point (addCoeffs left right) =
      evalCoeffs point left + evalCoeffs point right := by
  induction left generalizing right with
  | nil => simp [addCoeffs]
  | cons x xs ih =>
      cases right with
      | nil => simp [addCoeffs]
      | cons y ys =>
          simp only [addCoeffs, evalCoeffs_cons, ih]
          grind

/-- Ordinary low-to-high schoolbook coefficient convolution. -/
@[expose] def linearConvolution {p : Nat} [Bounds p] :
    List (ZMod64 p) → List (ZMod64 p) → List (ZMod64 p)
  | [], _ => []
  | _ :: _, [] => []
  | value :: values, right@(_ :: _) =>
      addCoeffs (right.map fun coefficient => value * coefficient)
        (0 :: linearConvolution values right)

/-- Schoolbook convolution evaluates to the product of the two evaluations. -/
theorem evalCoeffs_linearConvolution {p : Nat} [Bounds p]
    (point : ZMod64 p) (left right : List (ZMod64 p)) :
    evalCoeffs point (linearConvolution left right) =
      evalCoeffs point left * evalCoeffs point right := by
  induction left generalizing right with
  | nil => simp [linearConvolution]
  | cons value values ih =>
      cases right with
      | nil => simp [linearConvolution]
      | cons coefficient coefficients =>
          rw [linearConvolution, evalCoeffs_add, evalCoeffs_scale]
          simp only [evalCoeffs_cons, ih]
          grind

/-- A list of zero coefficients evaluates to zero. -/
@[simp] theorem evalCoeffs_replicate_zero {p : Nat} [Bounds p]
    (point : ZMod64 p) (count : Nat) :
    evalCoeffs point (List.replicate count 0) = 0 := by
  induction count with
  | zero => rfl
  | succ count => simp [List.replicate_succ, *]

/-- A fixed-length coefficient vector containing one nonzero monomial. -/
@[expose] def monomial {p : Nat} [Bounds p] (n degree : Nat)
    (coefficient : ZMod64 p) : List (ZMod64 p) :=
  if _hn : n = 0 then [] else
    List.replicate (degree % n) 0 ++ coefficient ::
      List.replicate (n - (degree % n + 1)) 0

/-- A positive-length monomial vector has exactly the requested length. -/
@[simp] theorem length_monomial {p : Nat} [Bounds p] (n degree : Nat)
    (coefficient : ZMod64 p) (hn : 0 < n) :
    (monomial n degree coefficient).length = n := by
  unfold monomial
  rw [dite_eq_right (Nat.ne_of_gt hn)]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  have hmod := Nat.mod_lt degree hn
  omega

/-- Evaluating a monomial vector gives its represented monomial. -/
theorem evalCoeffs_monomial {p : Nat} [Bounds p] (point : ZMod64 p)
    (n degree : Nat) (coefficient : ZMod64 p) (hn : 0 < n) :
    evalCoeffs point (monomial n degree coefficient) =
      point ^ (degree % n) * coefficient := by
  unfold monomial
  rw [dite_eq_right (Nat.ne_of_gt hn), evalCoeffs_append]
  simp

/-- Adding equal-sized coefficient vectors preserves their common length. -/
theorem length_addCoeffs {p : Nat} [Bounds p]
    (left right : List (ZMod64 p)) (hlength : left.length = right.length) :
    (addCoeffs left right).length = left.length := by
  induction left generalizing right with
  | nil =>
      have : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          simp only [addCoeffs, List.length_cons]
          rw [ih ys (by simpa using hlength)]

/-- The zero-extending coefficient sum has the longer input length. -/
theorem length_addCoeffs_eq_max {p : Nat} [Bounds p]
    (left right : List (ZMod64 p)) :
    (addCoeffs left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => simp [addCoeffs]
  | cons x xs ih =>
      cases right with
      | nil => simp [addCoeffs]
      | cons y ys =>
          simp [addCoeffs, ih]

/-- The schoolbook result fits in the standard ordinary-product length. -/
theorem length_linearConvolution_le {p : Nat} [Bounds p]
    (left right : List (ZMod64 p)) :
    (linearConvolution left right).length ≤ left.length + right.length - 1 := by
  induction left generalizing right with
  | nil => simp [linearConvolution]
  | cons value values ih =>
      cases right with
      | nil => simp [linearConvolution]
      | cons coefficient coefficients =>
          rw [linearConvolution, length_addCoeffs_eq_max]
          simp only [List.length_map, List.length_cons]
          apply Nat.max_le.mpr
          constructor
          · omega
          · have htail := ih (coefficient :: coefficients)
            simp only [List.length_cons] at htail
            omega

/-- Fold coefficients into a fixed cyclic vector, starting at a supplied
absolute degree. -/
@[expose] def foldCyclicFrom {p : Nat} [Bounds p] (n : Nat) :
    Nat → List (ZMod64 p) → List (ZMod64 p)
  | _, [] => List.replicate n 0
  | degree, coefficient :: coefficients =>
      addCoeffs (monomial n degree coefficient)
        (foldCyclicFrom n (degree + 1) coefficients)

/-- Cyclic folding always produces exactly `n` coefficients when `n` is
positive. -/
theorem length_foldCyclicFrom {p : Nat} [Bounds p] (n degree : Nat)
    (coefficients : List (ZMod64 p)) (hn : 0 < n) :
    (foldCyclicFrom n degree coefficients).length = n := by
  induction coefficients generalizing degree with
  | nil => simp [foldCyclicFrom]
  | cons coefficient coefficients ih =>
      rw [foldCyclicFrom,
        length_addCoeffs _ _ (by rw [length_monomial _ _ _ hn, ih])]
      exact length_monomial n degree coefficient hn

/-- At an `n`th root of unity, cyclic folding preserves evaluation, including
the absolute-degree shift used by the recursive worker. -/
theorem evalCoeffs_foldCyclicFrom {p : Nat} [Bounds p]
    (point : ZMod64 p) (n degree : Nat)
    (coefficients : List (ZMod64 p)) (hn : 0 < n)
    (hroot : point ^ n = 1) :
    evalCoeffs point (foldCyclicFrom n degree coefficients) =
      point ^ degree * evalCoeffs point coefficients := by
  induction coefficients generalizing degree with
  | nil => simp [foldCyclicFrom]
  | cons coefficient coefficients ih =>
      rw [foldCyclicFrom, evalCoeffs_add,
        evalCoeffs_monomial point n degree coefficient hn,
        ih (degree + 1), pow_mod point hroot degree]
      rw [show degree + 1 = degree + 1 by rfl, ZMod64.pow_succ]
      simp only [evalCoeffs_cons]
      grind

/-- Fold an ordinary coefficient list modulo `x^n - 1`. -/
@[expose] def foldCyclic {p : Nat} [Bounds p] (n : Nat)
    (coefficients : List (ZMod64 p)) : List (ZMod64 p) :=
  foldCyclicFrom n 0 coefficients

/-- A positive-length cyclic fold has exactly the requested length. -/
@[simp] theorem length_foldCyclic {p : Nat} [Bounds p] (n : Nat)
    (coefficients : List (ZMod64 p)) (hn : 0 < n) :
    (foldCyclic n coefficients).length = n := by
  exact length_foldCyclicFrom n 0 coefficients hn

/-- Cyclic folding preserves evaluation at every `n`th root of unity. -/
theorem evalCoeffs_foldCyclic {p : Nat} [Bounds p]
    (point : ZMod64 p) (n : Nat) (coefficients : List (ZMod64 p))
    (hn : 0 < n) (hroot : point ^ n = 1) :
    evalCoeffs point (foldCyclic n coefficients) =
      evalCoeffs point coefficients := by
  rw [foldCyclic, evalCoeffs_foldCyclicFrom point n 0 coefficients hn hroot]
  simp

/-- Independent coefficient-level cyclic convolution reference. -/
@[expose] def cyclicConvolution {p : Nat} [Bounds p] (n : Nat)
    (left right : List (ZMod64 p)) : List (ZMod64 p) :=
  foldCyclic n (linearConvolution left right)

/-- Cyclic convolution evaluates to the pointwise product at every `n`th root
of unity. -/
theorem evalCoeffs_cyclicConvolution {p : Nat} [Bounds p]
    (point : ZMod64 p) (n : Nat) (left right : List (ZMod64 p))
    (hn : 0 < n) (hroot : point ^ n = 1) :
    evalCoeffs point (cyclicConvolution n left right) =
      evalCoeffs point left * evalCoeffs point right := by
  rw [cyclicConvolution,
    evalCoeffs_foldCyclic point n _ hn hroot,
    evalCoeffs_linearConvolution]

/-- Every DFT coefficient of a cyclic convolution is the pointwise product of
the corresponding input coefficients. -/
theorem dftCoeff_cyclicConvolution {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right : List (ZMod64 p)) (frequency : Nat) :
    dftCoeff plan.root (cyclicConvolution n left right) frequency =
      dftCoeff plan.root left frequency * dftCoeff plan.root right frequency := by
  have hroot : (plan.root ^ frequency) ^ n = 1 := by
    rw [pow_mul, Nat.mul_comm, ← pow_mul, plan.root_order.pow_eq_one]
    simp
  exact evalCoeffs_cyclicConvolution (plan.root ^ frequency) n left right
    plan.length_pos hroot

/-- Pointwise multiplication of equal-order transform values. -/
@[expose] def pointwiseMul {p : Nat} [Bounds p]
    (left right : List (ZMod64 p)) : List (ZMod64 p) :=
  List.zipWith (· * ·) left right

/-- The DFT of cyclic convolution is pointwise multiplication. -/
theorem dft_cyclicConvolution {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right : List (ZMod64 p)) :
    dft plan.root n (cyclicConvolution n left right) =
      pointwiseMul (dft plan.root n left) (dft plan.root n right) := by
  apply List.ext_getElem
  · simp [pointwiseMul]
  · intro frequency hleft hright
    have hfrequency : frequency < n := by simpa using hleft
    simp only [pointwiseMul, List.getElem_zipWith]
    rw [getElem_dft _ _ _ _ hfrequency,
      getElem_dft _ _ _ _ hfrequency,
      getElem_dft _ _ _ _ hfrequency]
    exact dftCoeff_cyclicConvolution plan left right frequency

/-- Array wrapper for pointwise multiplication. -/
@[expose] def pointwiseMulArray {p : Nat} [Bounds p]
    (left right : Array (ZMod64 p)) : Array (ZMod64 p) :=
  (pointwiseMul left.toList right.toList).toArray

/-- Pointwise multiplication of the two executable forward results is the
forward result of the independent cyclic-convolution reference. -/
theorem pointwise_forward_eq_cyclic {p n : Nat}
    [Bounds p] [PrimeModulus p] (plan : NttPlan p n)
    (left right : Array (ZMod64 p))
    (hleft : left.size = n) (hright : right.size = n) :
    pointwiseMulArray (forwardRadixArray plan left)
        (forwardRadixArray plan right) =
      forwardRadixArray plan
        (cyclicConvolution n left.toList right.toList).toArray := by
  have hcyclic :
      (cyclicConvolution n left.toList right.toList).toArray.size = n := by
    simp [length_foldCyclic, cyclicConvolution, plan.length_pos]
  rw [forwardArray_eq_dft plan left hleft,
    forwardArray_eq_dft plan right hright,
    forwardArray_eq_dft plan _ hcyclic]
  unfold pointwiseMulArray dftArray
  rw [dft_cyclicConvolution]

/-- Checked cyclic NTT convolution. Length mismatch is normal failure. -/
def cyclic? {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right : Array (ZMod64 p)) :
    Option (Array (ZMod64 p)) := do
  let leftTransform ← forward? plan left
  let rightTransform ← forward? plan right
  inverse? plan (pointwiseMulArray leftTransform rightTransform)

/-- Successful cyclic NTT convolution is exactly schoolbook convolution
folded modulo `x^n - 1`. -/
theorem cyclic?_eq_reference {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right : Array (ZMod64 p))
    (hleft : left.size = n) (hright : right.size = n) :
    cyclic? plan left right =
      some (cyclicConvolution n left.toList right.toList).toArray := by
  rw [cyclic?, forward?_eq_radix plan left hleft,
    forward?_eq_radix plan right hright]
  change inverse? plan
      (pointwiseMulArray (forwardRadixArray plan left)
        (forwardRadixArray plan right)) = _
  rw [pointwise_forward_eq_cyclic plan left right hleft hright]
  let reference := (cyclicConvolution n left.toList right.toList).toArray
  have hreference : reference.size = n := by
    simp [reference, cyclicConvolution, length_foldCyclic, plan.length_pos]
  have hforward : (forwardRadixArray plan reference).size = n := by
    rw [forwardArray_eq_dft plan reference hreference]
    exact size_dftArray plan.root n reference
  rw [inverse?_eq_radix plan (forwardRadixArray plan reference) hforward,
    inverse_forwardArray plan reference hreference]

/-- Append enough zero coefficients to reach a requested capacity. Callers
use it only when the input already fits. -/
@[expose] def padTo {p : Nat} [Bounds p] (n : Nat)
    (coefficients : List (ZMod64 p)) : List (ZMod64 p) :=
  coefficients ++ List.replicate (n - coefficients.length) 0

/-- Padding a fitting list reaches exactly the requested length. -/
@[simp] theorem length_padTo {p : Nat} [Bounds p] (n : Nat)
    (coefficients : List (ZMod64 p)) (hfit : coefficients.length ≤ n) :
    (padTo n coefficients).length = n := by
  simp [padTo]
  omega

/-- Appending zero coefficients does not change evaluation. -/
@[simp] theorem evalCoeffs_padTo {p : Nat} [Bounds p]
    (point : ZMod64 p) (n : Nat) (coefficients : List (ZMod64 p)) :
    evalCoeffs point (padTo n coefficients) = evalCoeffs point coefficients := by
  rw [padTo, evalCoeffs_append]
  simp

/-- The exact-order DFT is injective on arrays of its plan length. -/
theorem dftArray_injective {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) {left right : Array (ZMod64 p)}
    (hleft : left.size = n) (hright : right.size = n)
    (hequal : dftArray plan.root n left = dftArray plan.root n right) :
    left = right := by
  have hforward : forwardRadixArray plan left = forwardRadixArray plan right := by
    rw [forwardArray_eq_dft plan left hleft,
      forwardArray_eq_dft plan right hright]
    exact hequal
  have hinverse := congrArg (inverseRadixArray plan) hforward
  rw [inverse_forwardArray plan left hleft,
    inverse_forwardArray plan right hright] at hinverse
  exact hinverse

/-- When no coefficient reaches degree `n`, cyclic folding is just zero
padding. -/
theorem foldCyclic_eq_pad {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (coefficients : List (ZMod64 p))
    (hfit : coefficients.length ≤ n) :
    (foldCyclic n coefficients).toArray = (padTo n coefficients).toArray := by
  have hfold : (foldCyclic n coefficients).toArray.size = n := by
    simp [length_foldCyclic, plan.length_pos]
  have hpad : (padTo n coefficients).toArray.size = n := by
    simp [length_padTo, hfit]
  apply dftArray_injective plan hfold hpad
  unfold dftArray
  congr 1
  apply List.ext_getElem
  · simp
  · intro frequency hleft hright
    have hfrequency : frequency < n := by simpa using hleft
    rw [getElem_dft _ _ _ _ hfrequency,
      getElem_dft _ _ _ _ hfrequency]
    simp only [dftCoeff_eq, evalCoeffs_padTo]
    apply evalCoeffs_foldCyclic
    · exact plan.length_pos
    · rw [pow_mul, Nat.mul_comm, ← pow_mul, plan.root_order.pow_eq_one]
      simp

/-- A plan whose length covers the ordinary product turns cyclic convolution
into the zero-padded schoolbook result. -/
theorem cyclicConvolution_eq_linear {p n : Nat}
    [Bounds p] [PrimeModulus p] (plan : NttPlan p n)
    (left right : List (ZMod64 p))
    (hcapacity : left.length + right.length - 1 ≤ n) :
    (cyclicConvolution n left right).toArray =
      (padTo n (linearConvolution left right)).toArray := by
  apply foldCyclic_eq_pad plan
  exact Nat.le_trans (length_linearConvolution_le left right) hcapacity

/-- Zero padding does not change any requested DFT coefficient. -/
theorem dft_padTo {p : Nat} [Bounds p] (root : ZMod64 p)
    (count n : Nat) (coefficients : List (ZMod64 p)) :
    dft root count (padTo n coefficients) = dft root count coefficients := by
  apply List.ext_getElem
  · simp
  · intro frequency hleft hright
    have hfrequency : frequency < count := by simpa using hleft
    rw [getElem_dft _ _ _ _ hfrequency,
      getElem_dft _ _ _ _ hfrequency]
    exact evalCoeffs_padTo (root ^ frequency) n coefficients

/-- Padding either cyclic-convolution input with zeros does not alter the
fixed-length cyclic result. -/
theorem cyclicConvolution_pad_inputs {p n : Nat}
    [Bounds p] [PrimeModulus p] (plan : NttPlan p n)
    (left right : List (ZMod64 p)) :
    (cyclicConvolution n (padTo n left) (padTo n right)).toArray =
      (cyclicConvolution n left right).toArray := by
  have hpadded :
      (cyclicConvolution n (padTo n left) (padTo n right)).toArray.size = n := by
    simp [cyclicConvolution, length_foldCyclic, plan.length_pos]
  have horiginal :
      (cyclicConvolution n left right).toArray.size = n := by
    simp [cyclicConvolution, length_foldCyclic, plan.length_pos]
  apply dftArray_injective plan hpadded horiginal
  unfold dftArray
  congr 1
  rw [dft_cyclicConvolution, dft_cyclicConvolution,
    dft_padTo, dft_padTo]

/-- Checked ordinary convolution. The plan length must be the least power of
two covering the product, and each input must fit that padded length. -/
def ordinary? {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right : Array (ZMod64 p)) :
    Option (Array (ZMod64 p)) :=
  let needed := left.size + right.size - 1
  if n = needed.nextPowerOfTwo ∧ left.size ≤ n ∧ right.size ≤ n then
    cyclic? plan (padTo n left.toList).toArray (padTo n right.toList).toArray
  else
    none

/-- Padding to `nextPowerOfTwo (left.size + right.size - 1)` and running the
NTT returns the zero-padded ordinary schoolbook convolution. -/
theorem ordinary?_eq_reference {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right : Array (ZMod64 p))
    (hnext : n = (left.size + right.size - 1).nextPowerOfTwo)
    (hleft : left.size ≤ n) (hright : right.size ≤ n) :
    ordinary? plan left right =
      some (padTo n (linearConvolution left.toList right.toList)).toArray := by
  have hvalid :
      n = (left.size + right.size - 1).nextPowerOfTwo ∧
        left.size ≤ n ∧ right.size ≤ n := ⟨hnext, hleft, hright⟩
  rw [ordinary?, ite_eq_left hvalid]
  have hpadLeft : (padTo n left.toList).toArray.size = n := by
    simp [length_padTo, hleft]
  have hpadRight : (padTo n right.toList).toArray.size = n := by
    simp [length_padTo, hright]
  rw [cyclic?_eq_reference plan _ _ hpadLeft hpadRight]
  rw [cyclicConvolution_pad_inputs plan left.toList right.toList]
  apply congrArg some
  apply cyclicConvolution_eq_linear plan
  rw [hnext]
  exact Nat.le_nextPowerOfTwo (left.size + right.size - 1)

/-- A successful checked ordinary convolution has the independent
coefficient-level reference value.  This packages the length checks performed
inside `ordinary?`, so coefficient-owner adapters need no duplicate unchecked
hypotheses. -/
theorem ordinary?_eq_of_some {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NttPlan p n) (left right result : Array (ZMod64 p))
    (hresult : ordinary? plan left right = some result) :
  result = (padTo n
      (linearConvolution left.toList right.toList)).toArray := by
  unfold ordinary? at hresult
  dsimp only at hresult
  split at hresult
  next hvalid =>
    obtain ⟨hnext, hleft, hright⟩ := hvalid
    have href := ordinary?_eq_reference plan left right hnext hleft hright
    unfold ordinary? at href
    rw [if_pos ⟨hnext, hleft, hright⟩] at href
    rw [href] at hresult
    exact (Option.some.inj hresult).symm
  next hinvalid => simp at hresult

/-- Split an exponent into its residue and quotient contributions. -/
theorem pow_mod_div {p : Nat} [Bounds p] (point : ZMod64 p)
    (n degree : Nat) :
    point ^ degree =
      point ^ (degree % n) * (point ^ n) ^ (degree / n) := by
  calc
    point ^ degree = point ^ (degree % n + n * (degree / n)) :=
      congrArg (fun exponent : Nat => point ^ exponent)
        (Nat.mod_add_div degree n).symm
    _ = point ^ (degree % n) * point ^ (n * (degree / n)) := by
      rw [Lean.Grind.Semiring.pow_add]
    _ = point ^ (degree % n) * (point ^ n) ^ (degree / n) := by
      rw [pow_mul]

/-- Fold coefficients into a fixed negacyclic vector, starting at a supplied
absolute degree. The quotient by `n` records the alternating sign. -/
@[expose] def foldNegacyclicFrom {p : Nat} [Bounds p] (n : Nat) :
    Nat → List (ZMod64 p) → List (ZMod64 p)
  | _, [] => List.replicate n 0
  | degree, coefficient :: coefficients =>
      addCoeffs
        (monomial n degree ((0 - 1) ^ (degree / n) * coefficient))
        (foldNegacyclicFrom n (degree + 1) coefficients)

/-- Negacyclic folding always produces exactly `n` coefficients when `n` is
positive. -/
theorem length_foldNegacyclicFrom {p : Nat} [Bounds p] (n degree : Nat)
    (coefficients : List (ZMod64 p)) (hn : 0 < n) :
    (foldNegacyclicFrom n degree coefficients).length = n := by
  induction coefficients generalizing degree with
  | nil => simp [foldNegacyclicFrom]
  | cons coefficient coefficients ih =>
      rw [foldNegacyclicFrom,
        length_addCoeffs _ _ (by rw [length_monomial _ _ _ hn, ih])]
      exact length_monomial n degree _ hn

/-- At a root of `x^n = -1`, negacyclic folding preserves evaluation,
including the absolute-degree shift used by the recursive worker. -/
theorem evalCoeffs_foldNegacyclicFrom {p : Nat} [Bounds p]
    (point : ZMod64 p) (n degree : Nat)
    (coefficients : List (ZMod64 p)) (hn : 0 < n)
    (hroot : point ^ n = 0 - 1) :
    evalCoeffs point (foldNegacyclicFrom n degree coefficients) =
      point ^ degree * evalCoeffs point coefficients := by
  induction coefficients generalizing degree with
  | nil => simp [foldNegacyclicFrom]
  | cons coefficient coefficients ih =>
      rw [foldNegacyclicFrom, evalCoeffs_add,
        evalCoeffs_monomial point n degree _ hn,
        ih (degree + 1), ZMod64.pow_succ]
      have hdegree :
          point ^ (degree % n) *
              ((0 - 1) ^ (degree / n) * coefficient) =
            point ^ degree * coefficient := by
        calc
          point ^ (degree % n) *
                ((0 - 1) ^ (degree / n) * coefficient) =
              (point ^ (degree % n) *
                (point ^ n) ^ (degree / n)) * coefficient := by
                  rw [hroot]
                  grind
          _ = point ^ degree * coefficient := by
            rw [← pow_mod_div point n degree]
      rw [hdegree]
      simp only [evalCoeffs_cons]
      grind

/-- Fold an ordinary coefficient list modulo `x^n + 1`. -/
@[expose] def foldNegacyclic {p : Nat} [Bounds p] (n : Nat)
    (coefficients : List (ZMod64 p)) : List (ZMod64 p) :=
  foldNegacyclicFrom n 0 coefficients

/-- A positive-length negacyclic fold has exactly the requested length. -/
@[simp] theorem length_foldNegacyclic {p : Nat} [Bounds p] (n : Nat)
    (coefficients : List (ZMod64 p)) (hn : 0 < n) :
    (foldNegacyclic n coefficients).length = n := by
  exact length_foldNegacyclicFrom n 0 coefficients hn

/-- Negacyclic folding preserves evaluation at every root of `x^n = -1`. -/
theorem evalCoeffs_foldNegacyclic {p : Nat} [Bounds p]
    (point : ZMod64 p) (n : Nat) (coefficients : List (ZMod64 p))
    (hn : 0 < n) (hroot : point ^ n = 0 - 1) :
    evalCoeffs point (foldNegacyclic n coefficients) =
      evalCoeffs point coefficients := by
  rw [foldNegacyclic,
    evalCoeffs_foldNegacyclicFrom point n 0 coefficients hn hroot]
  simp

/-- Independent coefficient-level negacyclic convolution reference. -/
@[expose] def negacyclicConvolution {p : Nat} [Bounds p] (n : Nat)
    (left right : List (ZMod64 p)) : List (ZMod64 p) :=
  foldNegacyclic n (linearConvolution left right)

/-- Negacyclic convolution evaluates to the pointwise product at every root
of `x^n = -1`. -/
theorem evalCoeffs_negacyclicConvolution {p : Nat} [Bounds p]
    (point : ZMod64 p) (n : Nat) (left right : List (ZMod64 p))
    (hn : 0 < n) (hroot : point ^ n = 0 - 1) :
    evalCoeffs point (negacyclicConvolution n left right) =
      evalCoeffs point left * evalCoeffs point right := by
  rw [negacyclicConvolution,
    evalCoeffs_foldNegacyclic point n _ hn hroot,
    evalCoeffs_linearConvolution]

/-- A primitive root of exact order `2n` has `n`th power `-1`. -/
theorem exactOrder_two_mul_half {p n : Nat} [Bounds p] [PrimeModulus p]
    (twist : ZMod64 p) (hn : 0 < n) (horder : ExactOrder twist (2 * n)) :
    twist ^ n = 0 - 1 := by
  have htwoPos : 0 < 2 * n := Nat.mul_pos (by decide) hn
  have hnot : twist ^ n ≠ 1 := by
    rcases horder.half with hbad | hhalf
    · have hne : 2 * n ≠ 1 := by omega
      exact False.elim (hne hbad)
    · simpa using hhalf
  have hsquare : twist ^ n * twist ^ n = 1 := by
    rw [← Lean.Grind.Semiring.pow_add]
    have hsum : n + n = 2 * n := by omega
    rw [hsum]
    exact horder.pow_eq_one
  have hfactor : (twist ^ n - 1) * (twist ^ n + 1) = 0 := by
    rw [Lean.Grind.Ring.sub_eq_add_neg]
    grind
  rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero_of_prime_modulus hfactor with
    hminus | hplus
  · exfalso
    apply hnot
    grind
  · grind

/-- Data required by the standard twist adapter from negacyclic convolution
of length `n` to an ordinary cyclic NTT of length `n`. -/
structure NegacyclicPlan (p n : Nat) [Bounds p] [PrimeModulus p] where
  /-- The reusable length-`n` transform. -/
  transform : NttPlan p n
  /-- A primitive `2n`th root used to twist coefficients. -/
  twist : ZMod64 p
  /-- The twist has exact order `2n`. -/
  twist_order : ExactOrder twist (2 * n)
  /-- Squaring the twist gives the transform root. -/
  root_eq : transform.root = twist ^ 2

namespace NegacyclicPlan

/-- A negacyclic plan's transform length is positive. -/
theorem length_pos {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) : 0 < n :=
  plan.transform.length_pos

/-- The primitive twist satisfies the defining negacyclic equation. -/
theorem twist_pow_length {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) : plan.twist ^ n = 0 - 1 :=
  exactOrder_two_mul_half plan.twist plan.length_pos plan.twist_order

/-- The primitive twist is nonzero. -/
theorem twist_ne_zero {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) : plan.twist ≠ 0 := by
  intro hzero
  have hpow := plan.twist_order.pow_eq_one
  have htwo : 0 < 2 * n := Nat.mul_pos (by decide) plan.length_pos
  rw [hzero, ZMod64.zero_pow (Nat.ne_of_gt htwo)] at hpow
  exact ZMod64.one_ne_zero hpow.symm

end NegacyclicPlan

/-- Multiply coefficient `i` by `root^(degree + i)`. -/
@[expose] def scalePowersFrom {p : Nat} [Bounds p] (root : ZMod64 p) :
    Nat → List (ZMod64 p) → List (ZMod64 p)
  | _, [] => []
  | degree, coefficient :: coefficients =>
      root ^ degree * coefficient ::
        scalePowersFrom root (degree + 1) coefficients

/-- Power scaling preserves the coefficient-list length. -/
@[simp] theorem length_scalePowersFrom {p : Nat} [Bounds p]
    (root : ZMod64 p) (degree : Nat) (coefficients : List (ZMod64 p)) :
    (scalePowersFrom root degree coefficients).length = coefficients.length := by
  induction coefficients generalizing degree with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp [scalePowersFrom, ih]

/-- Evaluation after power scaling is evaluation at the correspondingly
scaled point, with the worker's absolute-degree factor. -/
theorem evalCoeffs_scalePowersFrom {p : Nat} [Bounds p]
    (root point : ZMod64 p) (degree : Nat)
    (coefficients : List (ZMod64 p)) :
    evalCoeffs point (scalePowersFrom root degree coefficients) =
      root ^ degree * evalCoeffs (root * point) coefficients := by
  induction coefficients generalizing degree with
  | nil => simp [scalePowersFrom]
  | cons coefficient coefficients ih =>
      rw [scalePowersFrom, evalCoeffs_cons, ih, ZMod64.pow_succ]
      simp only [evalCoeffs_cons]
      grind

/-- Multiply coefficient `i` by `root^i`. -/
@[expose] def scalePowers {p : Nat} [Bounds p] (root : ZMod64 p)
    (coefficients : List (ZMod64 p)) : List (ZMod64 p) :=
  scalePowersFrom root 0 coefficients

/-- Power scaling preserves list length. -/
@[simp] theorem length_scalePowers {p : Nat} [Bounds p]
    (root : ZMod64 p) (coefficients : List (ZMod64 p)) :
    (scalePowers root coefficients).length = coefficients.length := by
  exact length_scalePowersFrom root 0 coefficients

/-- Evaluation after coefficient twisting changes the evaluation point. -/
theorem evalCoeffs_scalePowers {p : Nat} [Bounds p]
    (root point : ZMod64 p) (coefficients : List (ZMod64 p)) :
    evalCoeffs point (scalePowers root coefficients) =
      evalCoeffs (root * point) coefficients := by
  rw [scalePowers, evalCoeffs_scalePowersFrom]
  simp

/-- Inverse and forward powers of a nonzero residue cancel. -/
theorem inv_pow_mul_pow {p : Nat} [Bounds p] [PrimeModulus p]
    (root : ZMod64 p)
    (hroot : root ≠ 0) (degree : Nat) :
    root⁻¹ ^ degree * root ^ degree = 1 := by
  have hinv : root⁻¹ * root = 1 :=
    ZMod64.inv_mul_eq_one_of_ne_zero hroot
  induction degree with
  | zero => simp
  | succ degree ih =>
      rw [ZMod64.pow_succ, ZMod64.pow_succ]
      calc
        root⁻¹ ^ degree * root⁻¹ * (root ^ degree * root) =
            (root⁻¹ ^ degree * root ^ degree) * (root⁻¹ * root) := by
              grind
        _ = 1 := by rw [ih, hinv]; simp

/-- Scaling by inverse powers cancels scaling by forward powers. -/
theorem scalePowersFrom_inv {p : Nat} [Bounds p] [PrimeModulus p]
    (root : ZMod64 p) (hroot : root ≠ 0) (degree : Nat)
    (coefficients : List (ZMod64 p)) :
    scalePowersFrom root⁻¹ degree
        (scalePowersFrom root degree coefficients) = coefficients := by
  induction coefficients generalizing degree with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [scalePowersFrom]
      rw [ih (degree + 1)]
      congr 1
      calc
        root⁻¹ ^ degree * (root ^ degree * coefficient) =
            (root⁻¹ ^ degree * root ^ degree) * coefficient := by grind
        _ = coefficient := by rw [inv_pow_mul_pow root hroot degree]; simp

/-- Inverse coefficient twisting cancels forward twisting. -/
theorem scalePowers_inv {p : Nat} [Bounds p] [PrimeModulus p]
    (root : ZMod64 p) (hroot : root ≠ 0)
    (coefficients : List (ZMod64 p)) :
    scalePowers root⁻¹ (scalePowers root coefficients) = coefficients := by
  exact scalePowersFrom_inv root hroot 0 coefficients

/-- Twisting a transform point selects the corresponding odd power of the
primitive `2n`th root. -/
theorem twist_mul_root_pow {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) (frequency : Nat) :
    plan.twist * plan.transform.root ^ frequency =
      plan.twist ^ (2 * frequency + 1) := by
  rw [plan.root_eq, pow_mul, ZMod64.pow_succ]
  grind

/-- Every twisted transform point is a root of `x^n = -1`. -/
theorem twistPoint_pow_length {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) (frequency : Nat) :
    (plan.twist * plan.transform.root ^ frequency) ^ n = 0 - 1 := by
  rw [twist_mul_root_pow plan frequency, pow_mul, Nat.mul_comm,
    ← pow_mul, plan.twist_pow_length, negOne_pow_odd]

/-- At each transform frequency, cyclic convolution of twisted inputs agrees
with twisting the independent negacyclic reference. -/
theorem dftCoeff_cyclic_twist {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) (left right : List (ZMod64 p))
    (frequency : Nat) :
    dftCoeff plan.transform.root
        (cyclicConvolution n
          (scalePowers plan.twist left) (scalePowers plan.twist right))
        frequency =
      dftCoeff plan.transform.root
        (scalePowers plan.twist (negacyclicConvolution n left right))
        frequency := by
  rw [dftCoeff_cyclicConvolution plan.transform]
  simp only [dftCoeff_eq, evalCoeffs_scalePowers]
  rw [evalCoeffs_negacyclicConvolution
    (plan.twist * plan.transform.root ^ frequency) n left right
    plan.length_pos (twistPoint_pow_length plan frequency)]

/-- The DFT of cyclic convolution on twisted inputs is the DFT of the twisted
negacyclic reference. -/
theorem dft_cyclic_twist {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) (left right : List (ZMod64 p)) :
    dft plan.transform.root n
        (cyclicConvolution n
          (scalePowers plan.twist left) (scalePowers plan.twist right)) =
      dft plan.transform.root n
        (scalePowers plan.twist (negacyclicConvolution n left right)) := by
  apply List.ext_getElem
  · simp
  · intro frequency hleft hright
    have hfrequency : frequency < n := by simpa using hleft
    rw [getElem_dft _ _ _ _ hfrequency,
      getElem_dft _ _ _ _ hfrequency]
    exact dftCoeff_cyclic_twist plan left right frequency

/-- Zero padding before coefficient twisting does not change the transformed
values. -/
theorem dft_scalePowers_padTo {p : Nat} [Bounds p]
    (root twist : ZMod64 p) (count n : Nat)
    (coefficients : List (ZMod64 p)) :
    dft root count (scalePowers twist (padTo n coefficients)) =
      dft root count (scalePowers twist coefficients) := by
  apply List.ext_getElem
  · simp
  · intro frequency hleft hright
    have hfrequency : frequency < count := by simpa using hleft
    rw [getElem_dft _ _ _ _ hfrequency,
      getElem_dft _ _ _ _ hfrequency]
    simp only [dftCoeff_eq, evalCoeffs_scalePowers, evalCoeffs_padTo]

/-- Cyclic convolution of twisted inputs is exactly the twisted negacyclic
coefficient reference. -/
theorem cyclic_twist_eq_negacyclic {p n : Nat}
    [Bounds p] [PrimeModulus p] (plan : NegacyclicPlan p n)
    (left right : List (ZMod64 p)) :
    (cyclicConvolution n
        (scalePowers plan.twist left) (scalePowers plan.twist right)).toArray =
      (scalePowers plan.twist
        (negacyclicConvolution n left right)).toArray := by
  have hcyclic :
      (cyclicConvolution n
        (scalePowers plan.twist left) (scalePowers plan.twist right)).toArray.size =
        n := by
    simp [cyclicConvolution, length_foldCyclic, plan.length_pos]
  have htwisted :
      (scalePowers plan.twist
        (negacyclicConvolution n left right)).toArray.size = n := by
    simp [negacyclicConvolution, length_foldNegacyclic, plan.length_pos]
  apply dftArray_injective plan.transform hcyclic htwisted
  unfold dftArray
  congr 1
  exact dft_cyclic_twist plan left right

/-- Padding either negacyclic-convolution input with zeros does not alter the
fixed-length result. -/
theorem negacyclicConvolution_pad_inputs {p n : Nat}
    [Bounds p] [PrimeModulus p] (plan : NegacyclicPlan p n)
    (left right : List (ZMod64 p)) :
    (negacyclicConvolution n (padTo n left) (padTo n right)).toArray =
      (negacyclicConvolution n left right).toArray := by
  let padded := negacyclicConvolution n (padTo n left) (padTo n right)
  let original := negacyclicConvolution n left right
  have hpadded : padded.length = n := by
    simp [padded, negacyclicConvolution, length_foldNegacyclic,
      plan.length_pos]
  have horiginal : original.length = n := by
    simp [original, negacyclicConvolution, length_foldNegacyclic,
      plan.length_pos]
  have hscaled :
      (scalePowers plan.twist padded).toArray =
        (scalePowers plan.twist original).toArray := by
    have hpaddedTwist := cyclic_twist_eq_negacyclic plan
      (padTo n left) (padTo n right)
    have horiginalTwist := cyclic_twist_eq_negacyclic plan left right
    apply dftArray_injective plan.transform
    · simp [hpadded]
    · simp [horiginal]
    unfold dftArray
    congr 1
    rw [← hpaddedTwist, ← horiginalTwist,
      dft_cyclicConvolution, dft_cyclicConvolution,
      dft_scalePowers_padTo, dft_scalePowers_padTo]
  have hscaledList :
      scalePowers plan.twist padded =
        scalePowers plan.twist original := by
    simpa using congrArg Array.toList hscaled
  have hunscaled := congrArg (scalePowers plan.twist⁻¹) hscaledList
  rw [scalePowers_inv plan.twist plan.twist_ne_zero padded,
    scalePowers_inv plan.twist plan.twist_ne_zero original] at hunscaled
  exact congrArg List.toArray hunscaled

/-- Checked negacyclic NTT convolution via coefficient twisting. Length
mismatch is normal failure. -/
def negacyclic? {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) (left right : Array (ZMod64 p)) :
    Option (Array (ZMod64 p)) := do
  let result ← cyclic? plan.transform
    (scalePowers plan.twist left.toList).toArray
    (scalePowers plan.twist right.toList).toArray
  some (scalePowers plan.twist⁻¹ result.toList).toArray

/-- A primitive `2n`th twist makes the checked adapter return exactly
schoolbook convolution folded modulo `x^n + 1`. -/
theorem negacyclic?_eq_reference {p n : Nat} [Bounds p] [PrimeModulus p]
    (plan : NegacyclicPlan p n) (left right : Array (ZMod64 p))
    (hleft : left.size = n) (hright : right.size = n) :
    negacyclic? plan left right =
      some (negacyclicConvolution n left.toList right.toList).toArray := by
  have htwistLeft : (scalePowers plan.twist left.toList).toArray.size = n := by
    simpa using hleft
  have htwistRight : (scalePowers plan.twist right.toList).toArray.size = n := by
    simpa using hright
  rw [negacyclic?, cyclic?_eq_reference plan.transform _ _
    htwistLeft htwistRight]
  change some
      (scalePowers plan.twist⁻¹
        (cyclicConvolution n
          (scalePowers plan.twist left.toList)
          (scalePowers plan.twist right.toList))).toArray = _
  have htwisted :
      cyclicConvolution n
          (scalePowers plan.twist left.toList)
          (scalePowers plan.twist right.toList) =
        scalePowers plan.twist
          (negacyclicConvolution n left.toList right.toList) := by
    have harray := cyclic_twist_eq_negacyclic plan left.toList right.toList
    simpa using congrArg Array.toList harray
  rw [htwisted, scalePowers_inv plan.twist plan.twist_ne_zero]

end Ntt

end ZMod64

end Hex
